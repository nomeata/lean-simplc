import Lean
import Std.Data.List.Lemmas
import Std.Lean.Meta.Basic
import Std.Lean.Delaborator

open Lean Meta

def withoutModifingMVarAssignment (x : MetaM α) : MetaM α := do
  let saved ← get
  try
    x
  finally
    set saved

def mvarsToContext {α} (es : Array Expr) (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  let e ← instantiateMVars e
  let mut s := { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen), abstractLevels := false }
  for e' in es do
    (_, s) := AbstractMVars.abstractExprMVars e' s
  let (e, s') := AbstractMVars.abstractExprMVars e s
  s := s'
  setNGen s.ngen
  setMCtx s.mctx
  let e := s.lctx.mkForall s.fvars e
  forallBoundedTelescope e (s.fvars.size) fun _ e => k e

open Elab Tactic
partial
def checkSimpLC (thm1 thm2 : Name) : MetaM Unit := do
  -- logInfo m!"Checking {thm1} and {thm2} for critical pairs"
  let prop1 ← inferType (← mkConstWithFreshMVarLevels thm1)
  let (hyps1, _, eq1) ← forallMetaTelescope prop1
  let some (_, lhs1, rhs1) := eq1.eq?
    | return -- logError m!"Expected equality in conclusion of {thm1}:{indentExpr eq1}"


  let c2 ← mkConstWithFreshMVarLevels thm2
  let prop2 ← inferType c2
  let (hyps2, _, eq2) ← forallMetaTelescope prop2
  let eq2Proof := mkAppN c2 hyps2
  let some (_, _lhs2, _rhs2) := eq2.eq?
    | return -- logError m!"Expected equality in conclusion of {thm2}:{indentExpr eq2}"

  let (rewritten, Expr.mvar goal) ← Conv.mkConvGoalFor lhs1 | unreachable!
  -- logInfo m!"Initial goal: {goal}"

  let rec go (cgoal : MVarId) : MetaM Unit := do
    let (t, _) ← Lean.Elab.Tactic.Conv.getLhsRhsCore cgoal
    if t.isMVar then
      -- logInfo m!"Ignoring metavariable {t} (kind: {repr (← t.mvarId!.getKind)})"
      return
    -- logInfo m!"Looking at term {t}"

    withoutModifingMVarAssignment do -- must not let MVar assignments escape here
      -- let (lhs1', rhs') ← Lean.Elab.Tactic.Conv.getLhsRhsCore cgoal
      -- logInfo m!"eq2: {eq2}\nt: {t}\ncgoal: {(← cgoal.getType).consumeMData}"
      /-
      for mvar in ← getMVars t do
        logInfo m!"mvar {mvar} : {repr (← mvar.getKind)} {← mvar.isAssignable}"
      for mvar in ← getMVars eq2 do
        logInfo m!"mvar {mvar} : {repr (← mvar.getKind)} {← mvar.isAssignable}"
      -/

      if ← withReducible (isDefEqGuarded (mkMVar cgoal) eq2Proof) then
        -- logInfo m!"goal: {cgoal}"
        let cp ← instantiateMVars lhs1
        let e1 ← instantiateMVars rhs1
        let e2 ← instantiateMVars rewritten
        -- ignore trivial critical pairs:
        if ← withReducible (isDefEqGuarded e1 e2) then return
        let msg :=
          m!"The rules {ppConst (← mkConstWithLevelParams thm1)} and {ppConst (← mkConstWithLevelParams thm2)} produce a critical pair. Expression{indentExpr cp}\n" ++
          m!"reduces to{indentExpr e1}\n" ++
          m!"as well as{indentExpr e2}"

        -- logInfo msg
        -- logInfo m!"Proof term:{indentExpr (← instantiateMVars (.mvar goal))}"

        /-
        let mut goal ← mkEq e1 e2
        for m in (← getMVars goal) do
          unless (← m.isAssigned) || hyps1.any (·.mvarId! == m) || hyps2.any (·.mvarId! == m) do
            goal ← mkForallFVars #[mkMVar m] goal
        for h in (hyps2 ++ hyps1).reverse do
          if ! (← h.mvarId!.isAssigned) then
            goal ← mkForallFVars #[h] goal
        check goal
        -/

        let goal ← mkEq e1 e2
        mvarsToContext (hyps1 ++ hyps2) goal fun goal => do
          check goal

          let .mvar simp_goal ← mkFreshExprSyntheticOpaqueMVar goal
            | unreachable!
          let (_, simp_goal) ← simp_goal.intros
          check (mkMVar simp_goal)
          let (remaining_goals, _) ← simp_goal.withContext do
            runTactic simp_goal (← `(tactic|try simp [*]))
          unless remaining_goals.isEmpty do
            logInfo <| msg ++ m!"\njoining failed with\n{goalsToMessageData remaining_goals}"

    -- why is cgoal assigned here?
    -- cgoal.refl

    -- The following works, but sometimes `congr` complains
    if t.isApp then do
      let goals ←
        try Lean.Elab.Tactic.Conv.congr cgoal
        catch _ => pure []
      let goals := goals.filterMap id
      for hi : i in [:goals.length] do
        withoutModifingMVarAssignment $ do
          for hj : j in [:goals.length] do
            if i ≠ j then goals[j].refl
          go goals[i]

    -- This should be simpler, but does not work, (the
    -- isDefEqGuarded above fails) and I do not see why
    /-
    if let .app f x := t then
      if (←inferType f).isArrow then
        withoutModifingMVarAssignment do
          let (rhs, subgoal) ← Conv.mkConvGoalFor x
          rhs.mvarId!.setKind .natural
          goal.assign (← mkCongrArg f subgoal)
          go subgoal.mvarId!
      -- else logInfo m!"Cannot descend into dependent {f} in {t}"
      withoutModifingMVarAssignment do
        let (rhs, subgoal) ← Conv.mkConvGoalFor f
        rhs.mvarId!.setKind .natural
        goal.assign (← mkCongrFun subgoal x)
        go subgoal.mvarId!
    -/



  go goal


def checkSimpLCAll : MetaM Unit := do
  let thms ← getSimpTheorems
  let mut names := #[]
  for (origin, ()) in thms.lemmaNames.set do
    if let .decl n _ false := origin then
      if (`List).isPrefixOf n then
        names := names.push n
  logInfo m!"Found {names.size} simp lemmas"
  names := names[:30]
  logInfo m!"Checking {names.size} simp lemmas for critical pairs"
  -- logInfo m!"{names}"
  for thm1 in names do
    for thm2 in names do
      if thm1 != thm2 then
        checkSimpLC thm1 thm2


open Elab Command in
elab "check_simp_lc " thm1:ident thm2:ident : command => runTermElabM fun _ => do
  let thm1 ← resolveGlobalConstNoOverload thm1
  let thm2 ← resolveGlobalConstNoOverload thm2
  checkSimpLC thm1 thm2

open Elab Command in
elab "check_simp_lc" : command => runTermElabM fun _ => do
  checkSimpLCAll

-- check_simp_lc List.eraseP_cons_of_pos List.intersperse_cons₂


-- attribute [simp] Function.comp_def
-- attribute [simp] List.map_filter
-- check_simp_lc List.map_filter List.map_map
/-
attribute [-simp] List.map_map
check_simp_lc List.map_map List.map_map
-/

-- set_option trace.Meta.Tactic.simp true in
-- check_simp_lc List.indexesOf_nil List.replace_nil

-- check_simp_lc
