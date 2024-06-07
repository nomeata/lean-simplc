import Lean
import Simplc.Setup
import Simplc.MVarCycles
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
def checkSimpLC (root_only : Bool) (tac? : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) (thm1 : SimpTheorem) (thms : SimpTheorems) :
    StateT (Array CriticalPair) MetaM Unit :=
  withConfig (fun c => { c with etaStruct := .none }) do
  withCurrHeartbeats do
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
      if (← isIgnoredName thm2.origin.key) then continue
      if (← isCriticalPairWhitelisted (thm1.origin.key, thm2.origin.key)) then continue
      if path.isEmpty then
        unless thm1.origin.key.quickLt thm2.origin.key do continue
      let good ← withoutModifingMVarAssignment do withCurrHeartbeats do
        if simplc.stderr.get (← getOptions) then
          IO.eprintln s!"{thm1.origin.key} {thm2.origin.key}"
        withTraceNode `simplc (do return m!"{exceptBoolEmoji ·} {← critPair.pp}") do
          let val2  ← thm2.getValue
          let type2 ← inferType val2
          let (hyps2, _bis, type2) ← forallMetaTelescopeReducing type2
          let type2 ← whnf (← instantiateMVars type2)
          let type1 ← cgoal.getType
          if ← withReducible (isDefEq type1 type2) then
            cgoal.assign (val2.beta hyps2) -- TODO: Do we need this, or is the defeq enough?
            MVarCycles.checkMVarsCycles

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
                match tac? with
                | .some tac => runTactic simp_goal tac
                | .none =>
                  runTactic simp_goal (← `(tactic|(
                    try contradiction
                    try (apply Fin.elim0; assumption)
                    try simp_all
                    try ((try apply Iff.of_eq); ac_rfl)
                    try omega -- helps with sizeOf lemmas and AC-equivalence of +
                  )))
              if remaining_goals.isEmpty then
                return true
              trace[simplc] m!"Joining failed with\n{goalsToMessageData remaining_goals}"
              return false
            else
              trace[simplc] m!"Not a critical pair, discrTree false positive:" ++
                m!"{indentExpr type1.consumeMData}\n=!={indentExpr type2}"
              return true
      unless good do
        modify (·.push critPair)

    unless root_only do
      if true then
        -- The following works, but sometimes `congr` complains
        if t.isApp then do
          let goals ←
            try Lean.Elab.Tactic.Conv.congr cgoal
            catch e =>
              trace[simplc] m!"congr failed on {cgoal}:\n{← nestedExceptionToMessageData e}"
              pure []
          let goals := goals.filterMap id
          for hi : i in [:goals.length] do
            if (← goals[i].getType).isEq then
              withoutModifingMVarAssignment $ do
                -- rfl all othe others, akin to `selectIdx`
                for hj : j in [:goals.length] do
                  if i ≠ j then
                    if (← goals[j].getType).isEq then
                      goals[j].refl
                    else
                      -- Likely a subsingleton instance, also see https://github.com/leanprover/lean4/issues/4394
                      -- just leave in place, will become a parameter
                      pure ()
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

section
open Parser Term Tactic
def in_opt : Parser := leading_parser
  optional ("in " >> Parser.ident)

syntax "simp_lc_check " "root"? in_opt : command
syntax "simp_lc_inspect " Parser.ident Parser.ident (byTactic)? : command
syntax "simp_lc_whitelist " Parser.ident Parser.ident : command
syntax "simp_lc_ignore " Parser.ident : command
end

def delabWhitelistCmd (cp : CriticalPair) : MetaM (TSyntax `command) := do
  `(command|simp_lc_whitelist $(mkIdent cp.thm1.origin.key) $(mkIdent cp.thm2.origin.key))


def reportBadPairs (cmdStx? : Option (TSyntax `command)) (act : StateT (Array CriticalPair) MetaM Unit) : MetaM Unit := do
  let (.unit, badPairs) ← StateT.run act #[]
  unless badPairs.isEmpty do
    logError <| m!"Found {badPairs.size} non-confluent critical pairs:" ++
      indentD (.joinSep ((← badPairs.mapM (·.pp)).toList) "\n")
    if let .some cmdStx := cmdStx? then
      let mut str : String := ""
      for cp in badPairs do
        let stx ← delabWhitelistCmd cp
        str := str ++ "\n" ++ (← PrettyPrinter.ppCategory `command stx).pretty
      str := str ++ "\n" ++ (← PrettyPrinter.ppCategory `command cmdStx).pretty
      TryThis.addSuggestion cmdStx { suggestion := str, messageData? := m!"(lots of simp_lc_whitelist lines)" }

def checkSimpLCAll (cmdStx : TSyntax `command) (root_only : Bool) (pfix : Name) : MetaM Unit := do
  let sthms ← getSimpTheorems
  let thms := sthms.pre.values ++ sthms.post.values
  let thms ← thms.filterM fun sthm => do
    if sthms.erased.contains sthm.origin then
      return false
    if let .decl n _ false := sthm.origin then
      if (← isIgnoredName n) then
        return false
      if pfix.isPrefixOf n then
        return true
    return false
  logInfo m!"Checking {thms.size} simp lemmas for critical pairs"
  let filtered_sthms := thms.foldl Lean.Meta.addSimpTheoremEntry (init := {})
  -- logInfo m!"{names}"
  -- let thms := thms[:104] ++ thms[105:]
  reportBadPairs cmdStx do
    for thm1 in thms do
      try
        checkSimpLC root_only .none thm1 filtered_sthms
      catch e => logError m!"Failed to check {← My.ppOrigin thm1.origin}\n{← nestedExceptionToMessageData e}"

open Elab Command
elab_rules : command
| `(command|simp_lc_inspect $ident1:ident $ident2:ident $[by $tac?]?) => liftTermElabM fun _ => do
  let name1 ← realizeGlobalConstNoOverloadWithInfo ident1
  let name2 ← realizeGlobalConstNoOverloadWithInfo ident2
  let sthms : SimpTheorems ← SimpTheorems.addConst {} name2
  withOptions (·.setBool `trace.simplc true) do reportBadPairs .none do
    checkSimpLC false tac? (← mkSimpTheorem name1) sthms

| `(command|simp_lc_check $[root%$root?]? $pfix?:in_opt) => liftTermElabM do
  let stx ← getRef
  let pfix := match pfix? with
    | `(in_opt|in $i:ident) =>i.getId
    | _ => .anonymous
  checkSimpLCAll ⟨stx⟩ root?.isSome pfix

elab "simp_lc_whitelist " thm1:ident thm2:ident : command => runTermElabM fun _ => do
  let name1 ← realizeGlobalConstNoOverloadWithInfo thm1
  let name2 ← realizeGlobalConstNoOverloadWithInfo thm2
  whiteListCriticalPair (name1, name2)

elab "simp_lc_ignore " thm:ident : command => runTermElabM fun _ => do
  ignoreName (← realizeGlobalConstNoOverloadWithInfo thm)
