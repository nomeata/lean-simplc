import Lean
import Std.Data.List.Lemmas
import Std.Lean.Meta.Basic
import Std.Lean.Delaborator
import Std.Lean.HashSet

open Lean Meta

-- using ppConst
def My.ppOrigin [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n post inv => do
    let r ← mkConstWithLevelParams n;
    match post, inv with
    | true,  true  => return m!"← {ppConst r}"
    | true,  false => return m!"{ppConst r}"
    | false, true  => return m!"↓ ← {ppConst r}"
    | false, false => return m!"↓ {ppConst r}"
  | .fvar n => return mkFVar n
  | .stx _ ref => return ref
  | .other n => return n

def withoutModifingMVarAssignment (x : MetaM α) : MetaM α := do
  let saved ← get
  try
    x
  finally
    set saved

def forallInstTelescope {α} (e : Expr) (n : Nat) (k : Expr → MetaM α) : MetaM α := do
  match n with
  | 0 => k e
  | n+1 =>
    let .forallE name d b bi := e | unreachable!
    if (← isClass? d).isSome then
      if let .some inst ← trySynthInstance d then
        return ← forallInstTelescope (b.instantiate1 inst) n k

    withLocalDecl name bi d fun x => do
      forallInstTelescope (b.instantiate1 x) n k

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
  forallInstTelescope e s.fvars.size k

open Elab Tactic
partial
def checkSimpLC (thm1 : SimpTheorem) (thms : SimpTheorems)
    (ignores : HashSet (Name × Name) := {})
    (verbose : Bool := false)
    : MetaM Unit := withConfig (fun c => { c with etaStruct := .none }) do

  -- IO.println f!"Checking {thm1} for critical pairs"

  let val1 ← thm1.getValue
  let type1 ← inferType val1
  let (hyps1, _bis, eq1) ← forallMetaTelescopeReducing type1
  let eq1 ← whnf (← instantiateMVars eq1)
  let some (_, lhs1, rhs1) := eq1.eq?
    | return -- logError m!"Expected equality in conclusion of {thm1}:{indentExpr eq1}"

  let (rewritten, Expr.mvar goal) ← Conv.mkConvGoalFor lhs1 | unreachable!
  -- logInfo m!"Initial goal: {goal}"

  let rec go (cgoal : MVarId) : MetaM Unit := do
    let (t, _) ← Lean.Elab.Tactic.Conv.getLhsRhsCore cgoal
    if t.isMVar then
      -- logInfo m!"Ignoring metavariable {t} (kind: {repr (← t.mvarId!.getKind)})"
      return
    -- logInfo m!"Looking at term {t}"

    -- logInfo m!"t: {t}\neq2: {eq2}"
    -- logInfo m!"Discr: {thms.post}\nt: {t}"
    let matchs := (← thms.pre.getUnify t simpDtConfig) ++ (← thms.post.getUnify t simpDtConfig)
    let matchs := matchs.filter fun thm2 => ! thms.erased.contains thm2.origin
    let matchs := matchs.filter fun thm2 => ! ignores.contains (thm1.origin.key, thm2.origin.key)
    -- logInfo m!"Matches: {matchs}"
    -- IO.println f!"matches: {matchs}"
    -- TODO: Without the [:1] I am getting stack overflows here
    for thm2 in matchs do withoutModifingMVarAssignment do
      let val2  ← thm2.getValue
      let type2 ← inferType val2
      let (hyps2, _bis, type2) ← forallMetaTelescopeReducing type2
      let type ← whnf (← instantiateMVars type2)
      -- let lhs := type.appFn!.appArg!
      if ← withReducible (isDefEq (← cgoal.getType) type) then
        cgoal.assign (val2.beta hyps2) -- TODO: Do we need this, or is the defeq enough?
        let cp ← instantiateMVars lhs1
        let e1 ← instantiateMVars rhs1
        let e2 ← instantiateMVars rewritten
        -- ignore trivial critical pairs:
        if ← withReducible (isDefEqGuarded e1 e2) then return
        -- logInfo msg
        -- logInfo m!"Proof term:{indentExpr (← instantiateMVars (.mvar goal))}"

        let goal ← mkEq e1 e2
        mvarsToContext (hyps1 ++ hyps2) goal fun goal => do
          check goal
          let .mvar simp_goal ← mkFreshExprSyntheticOpaqueMVar goal
            | unreachable!
          let (_, simp_goal) ← simp_goal.intros
          check (mkMVar simp_goal)
          let (remaining_goals, _) ← simp_goal.withContext do
            runTactic simp_goal (← `(tactic|(
              try contradiction
              try simp [*]
            )))
          unless remaining_goals.isEmpty do
            if verbose then
              -- TODO: Feed these through mvarsToContext, too, for prettier output
              let cp ← instantiateMVars cp
              let e1 ← instantiateMVars e1
              let e2 ← instantiateMVars e2

              logInfo <|
                m!"The rules\n    {← My.ppOrigin thm1.origin} {← My.ppOrigin thm2.origin}\nproduce a critical pair. Expression{indentExpr cp}\n" ++
                m!"reduces to{indentExpr e1}\n" ++
                m!"as well as{indentExpr e2}\n" ++
                m!"joining failed with\n{goalsToMessageData remaining_goals}"
            else
              logInfo m!"  {← My.ppOrigin thm1.origin} {← My.ppOrigin thm2.origin}"

    if true then
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
    else
      -- This should be simpler, but does not work, (the
      -- isDefEqGuarded above fails) and I do not see why
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

  go goal

def mkSimpTheorems (name : Name) : MetaM SimpTheorems := do
  let sthms : SimpTheorems := {}
  sthms.addConst name

def mkSimpTheorem (name : Name) : MetaM SimpTheorem := do
  let sthms ← mkSimpTheorems name
  let sthms := sthms.pre.values ++ sthms.post.values
  return sthms[0]!

-- Exclude these from checking all
def lcBlacklist : Array Name := #[
  ``List.getElem?_eq_get?  -- oddness with .refl and Decidable
  ]

def checkSimpLCAll (ignores : HashSet (Name × Name) := {}): MetaM Unit := do
  let sthms ← getSimpTheorems
  let thms := sthms.pre.values ++ sthms.post.values
  let thms := thms.filter fun sthm => Id.run do
    if sthms.erased.contains sthm.origin then
      return false
    if let .decl n _ false := sthm.origin then
      if n ∈ lcBlacklist then
        return false
      if (`List).isPrefixOf n then
        return true
    return false
  logInfo m!"Checking {thms.size} simp lemmas for critical pairs"
  let filtered_sthms := thms.foldl Lean.Meta.addSimpTheoremEntry (init := {})
  -- logInfo m!"{names}"
  -- let thms := thms[:104] ++ thms[105:]
  for thm1 in thms do
    try
      checkSimpLC thm1 filtered_sthms (ignores := ignores) (verbose := false)
    catch e => logError m!"Failed to check {← My.ppOrigin thm1.origin}\n{← nestedExceptionToMessageData e}"

open Elab Command in
elab "check_simp_lc " thms:ident+ : command => runTermElabM fun _ => do
  let names ← thms.mapM resolveGlobalConstNoOverloadWithInfo
  let sthms ← names.foldlM (fun sthms name => sthms.addConst name) {}
  checkSimpLC (← mkSimpTheorem names[0]!) sthms (verbose := true)


open Parser Term Tactic in
def ignores : Parser := leading_parser
  optional ("ignoring " >> sepBy1IndentSemicolon (Parser.ident >> Parser.ident))


open Elab Command in
elab "check_simp_lc " ign:ignores : command => runTermElabM fun _ => do
  let ignores ← match ign with
    | `(ignores|ignoring $[$i1:ident $i2:ident]*) => do
      let thm1s ← i1.mapM resolveGlobalConstNoOverloadWithInfo
      let thm2s ← i2.mapM resolveGlobalConstNoOverloadWithInfo
      pure (HashSet.ofArray (thm1s.zip thm2s))
    | _ => pure {}
  checkSimpLCAll ignores
