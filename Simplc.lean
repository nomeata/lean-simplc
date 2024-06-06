import Lean
import Simplc.Setup
-- import Std.Data.List.Lemmas
-- import Std.Lean.Meta.Basic
-- import Std.Lean.Delaborator
-- import Std.Lean.HashSet

open Lean Meta

-- remove with https://github.com/leanprover/lean4/pull/4362
def My.ppOrigin [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n post inv => do
    let r ← mkConstWithLevelParams n;
    match post, inv with
    | true,  true  => return m!"← {MessageData.ofConst r}"
    | true,  false => return m!"{MessageData.ofConst r}"
    | false, true  => return m!"↓ ← {MessageData.ofConst r}"
    | false, false => return m!"↓ {MessageData.ofConst r}"
  | .fvar n => return mkFVar n
  | .stx _ ref => return ref
  | .other n => return n

def withoutModifingMVarAssignmentImpl (x : MetaM α) : MetaM α := do
  let saved ← getThe Meta.State
  try
    x
  finally
    set saved
def withoutModifingMVarAssignment {m} [Monad m] [MonadControlT MetaM m] {α} (x : m α) : m α :=
  mapMetaM (fun k => withoutModifingMVarAssignmentImpl k) x


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

def mvarsToContext {α} (es1 : Array Expr) (es2 : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  let es2 ← es2.mapM instantiateMVars
  let s  : AbstractMVars.State := { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen), abstractLevels := false }
  let (es2, s) := Id.run <| StateT.run (s := s) do
    es1.forM fun e => do let _ ← AbstractMVars.abstractExprMVars e
    es2.mapM fun e => AbstractMVars.abstractExprMVars e
  setNGen s.ngen
  setMCtx s.mctx
  withLCtx s.lctx (← getLocalInstances) do
    k s.fvars es2

structure CriticalPair where
  thm1 : SimpTheorem
  thm2 : SimpTheorem
  path : List Nat

def CriticalPair.pp (cp : CriticalPair) : MetaM MessageData :=
  return m!"{← My.ppOrigin cp.thm1.origin} {← My.ppOrigin cp.thm2.origin} (at {cp.path})"

open Elab Tactic
partial
def checkSimpLC (thm1 : SimpTheorem) (thms : SimpTheorems) (ignores : HashSet (Name × Name) := {}) :
    StateT (Array CriticalPair) MetaM Unit :=
  withConfig (fun c => { c with etaStruct := .none }) do

  -- IO.println f!"Checking {thm1} for critical pairs"

  let val1 ← thm1.getValue
  let type1 ← inferType val1
  let (hyps1, _bis, eq1) ← forallMetaTelescopeReducing type1
  let eq1 ← whnf (← instantiateMVars eq1)
  let some (_, lhs1, rhs1) := eq1.eq?
    | return -- logError m!"Expected equality in conclusion of {thm1}:{indentExpr eq1}"

  let (rewritten, Expr.mvar goal) ← Conv.mkConvGoalFor lhs1 | unreachable!
  -- logInfo m!"Initial goal: {goal}"

  let rec go (path : List Nat) (cgoal : MVarId) : StateT (Array CriticalPair) MetaM Unit := do
    let (t, _) ← Lean.Elab.Tactic.Conv.getLhsRhsCore cgoal
    if t.isMVar then
      -- logInfo m!"Ignoring metavariable {t} (kind: {repr (← t.mvarId!.getKind)})"
      return

    let matchs := (← thms.pre.getUnify t simpDtConfig) ++ (← thms.post.getUnify t simpDtConfig)
    for thm2 in matchs do
      let critPair : CriticalPair := ⟨thm1, thm2, path⟩
      if thms.erased.contains thm2.origin then continue
      if ignores.contains (thm1.origin.key, thm2.origin.key) then continue
      if (← isCriticalPairWhitelisted (thm1.origin.key, thm2.origin.key)) then continue
      if path.isEmpty then
        unless thm1.origin.key.quickLt thm2.origin.key do continue
      let good ← withoutModifingMVarAssignment do
        withTraceNode `simplc (do return m!"{exceptBoolEmoji ·} {← critPair.pp}") do
          let val2  ← thm2.getValue
          let type2 ← inferType val2
          let (hyps2, _bis, type2) ← forallMetaTelescopeReducing type2
          let type2 ← whnf (← instantiateMVars type2)
          if ← withReducible (isDefEq (← cgoal.getType) type2) then
            cgoal.assign (val2.beta hyps2) -- TODO: Do we need this, or is the defeq enough?
            mvarsToContext (hyps1 ++ hyps2) #[lhs1, rhs1, rewritten] fun _fvars r => do
              let #[cp, e1, e2] := r | unreachable!
              -- Do we need forallInstTelescope here?
              -- At some point I was using
              -- forallInstTelescope (← mkForallFVars fvars goal) fvars.size fun goal => do
              -- here
              trace[simplc]
                m!"Expression{indentExpr cp}\n" ++
                m!"reduces with {← My.ppOrigin thm1.origin} to{indentExpr e1}\n" ++
                m!"and     with {← My.ppOrigin thm2.origin} to{indentExpr e2}\n"

              let goal ← mkEq e1 e2
              check goal
              let .mvar simp_goal ← mkFreshExprSyntheticOpaqueMVar goal
                | unreachable!
              let (_, simp_goal) ← simp_goal.intros
              check (mkMVar simp_goal)
              let (remaining_goals, _) ← simp_goal.withContext do
                runTactic simp_goal (← `(tactic|(
                  try contradiction
                  trace_state
                  try simp [*]
                )))
              if remaining_goals.isEmpty then
                return true
              trace[simplc] m!"Joining failed with\n{goalsToMessageData remaining_goals}"
              return false
            else
              return true
      unless good do
        modify (·.push critPair)

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
            go (path ++ [i+1]) goals[i]
    else
      -- This should be simpler, but does not work, (the
      -- isDefEqGuarded above fails) and I do not see why
      if let .app f x := t then
        if (←inferType f).isArrow then
          withoutModifingMVarAssignment do
            let (rhs, subgoal) ← Conv.mkConvGoalFor x
            rhs.mvarId!.setKind .natural
            goal.assign (← mkCongrArg f subgoal)
            go (path ++ [2]) subgoal.mvarId!
        -- else logInfo m!"Cannot descend into dependent {f} in {t}"
        withoutModifingMVarAssignment do
          let (rhs, subgoal) ← Conv.mkConvGoalFor f
          rhs.mvarId!.setKind .natural
          goal.assign (← mkCongrFun subgoal x)
          go (path ++ [1]) subgoal.mvarId!
  go [] goal

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

def reportBadPairs (act : StateT (Array CriticalPair) MetaM Unit) : MetaM Unit := do
  let (.unit, badPairs) ← StateT.run act #[]
  unless badPairs.isEmpty do
    logError <| m!"Found {badPairs.size} non-confluent critical pairs:" ++
      indentD (.joinSep ((← badPairs.mapM (·.pp)).toList) "\n")

def checkSimpLCAll (pfix : Name) (ignores : HashSet (Name × Name) := {}): MetaM Unit := do
  let sthms ← getSimpTheorems
  let thms := sthms.pre.values ++ sthms.post.values
  let thms := thms.filter fun sthm => Id.run do
    if sthms.erased.contains sthm.origin then
      return false
    if let .decl n _ false := sthm.origin then
      if n ∈ lcBlacklist then
        return false
      if pfix.isPrefixOf n then
        return true
    return false
  logInfo m!"Checking {thms.size} simp lemmas for critical pairs"
  let filtered_sthms := thms.foldl Lean.Meta.addSimpTheoremEntry (init := {})
  -- logInfo m!"{names}"
  -- let thms := thms[:104] ++ thms[105:]
  reportBadPairs do
    for thm1 in thms do
      try
        checkSimpLC thm1 filtered_sthms (ignores := ignores)
      catch e => logError m!"Failed to check {← My.ppOrigin thm1.origin}\n{← nestedExceptionToMessageData e}"

open Elab Command in
elab "check_simp_lc " thms:ident+ : command => runTermElabM fun _ => do
  let names ← thms.mapM (realizeGlobalConstNoOverloadWithInfo ·)
  let sthms ← names.foldlM (fun sthms name => sthms.addConst name) {}
  reportBadPairs do
    checkSimpLC (← mkSimpTheorem names[0]!) sthms

section
open Parser Term Tactic
def ignores : Parser := leading_parser
  optional ("ignoring " >> sepBy1IndentSemicolon (Parser.ident >> Parser.ident))

def in_opt : Parser := leading_parser
  optional ("in " >> Parser.ident)
end

open Elab Command
elab "check_simp_lc " pfix?:in_opt ign:ignores : command => runTermElabM fun _ => do
  let ignores ← match ign with
    | `(ignores|ignoring $[$i1:ident $i2:ident]*) => do
      let thm1s ← i1.mapM (realizeGlobalConstNoOverloadWithInfo ·)
      let thm2s ← i2.mapM (realizeGlobalConstNoOverloadWithInfo ·)
      pure (HashSet.empty.insertMany (thm1s.zip thm2s))
    | _ => pure {}
  let pfix := match pfix? with
    | `(in_opt|in $i:ident) =>i.getId
    | _ => .anonymous
  checkSimpLCAll pfix ignores

elab "simp_lc_whitelist " thm1:ident thm2:ident : command => runTermElabM fun _ => do
  let name1 ← realizeGlobalConstNoOverloadWithInfo thm1
  let name2 ← realizeGlobalConstNoOverloadWithInfo thm2
  whiteListCriticalPair (name1, name2)
