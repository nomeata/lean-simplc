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
def checkSimpLC (thm1 : SimpTheorem) (thms : SimpTheorems) (ignores : HashSet (Name × Name) := {})
    : MetaM Unit := withConfig (fun c => { c with etaStruct := .none }) do

  -- logInfo m!"Checking {thm1} and {thm2} for critical pairs"

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
    -- TODO: Without the [:1] I am getting stack overflows here
    for thm2 in matchs[:1] do withoutModifingMVarAssignment do
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
          -- TODO: Feed these through mvarsToContext, too, for prettier output
          let cp ← instantiateMVars cp
          let e1 ← instantiateMVars e1
          let e2 ← instantiateMVars e2

          let msg :=
            m!"The rules\n    {← My.ppOrigin thm1.origin} {← My.ppOrigin thm2.origin}\nproduce a critical pair. Expression{indentExpr cp}\n" ++
            m!"reduces to{indentExpr e1}\n" ++
            m!"as well as{indentExpr e2}"

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
            logInfo <| msg ++ m!"\njoining failed with\n{goalsToMessageData remaining_goals}"

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
  ``List.foldrM_append,    -- causes it to run out of stack space
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
      checkSimpLC thm1 filtered_sthms (ignores := ignores)
    catch e => logError m!"Failed to check {← My.ppOrigin thm1.origin}\n{← nestedExceptionToMessageData e}"

open Elab Command in
elab "check_simp_lc " thm1:ident thm2:ident : command => runTermElabM fun _ => do
  let thm1 ← resolveGlobalConstNoOverload thm1
  let thm2 ← resolveGlobalConstNoOverload thm2
  checkSimpLC (← mkSimpTheorem thm1) (← mkSimpTheorems thm2)


open Parser Term Tactic in
def ignores : Parser := leading_parser
  optional ("ignoring " >> sepBy1IndentSemicolon (Parser.ident >> Parser.ident))


open Elab Command in
elab "check_simp_lc " ign:ignores : command => runTermElabM fun _ => do
  let ignores ← match ign with
    | `(ignores|ignoring $[$i1:ident $i2:ident]*) => do
      let thm1s ← i1.mapM resolveGlobalConstNoOverload
      let thm2s ← i2.mapM resolveGlobalConstNoOverload
      pure (HashSet.ofArray (thm1s.zip thm2s))
    | _ => pure {}
  checkSimpLCAll ignores

attribute [simp] Function.comp_def
-- fixes
-- check_simp_lc List.map_map List.map_map

@[simp] theorem takeWhile_nil : List.takeWhile p [] = [] := rfl
-- fixes
check_simp_lc List.takeWhile_append_dropWhile List.dropWhile_nil

attribute [simp] List.foldrM
-- fixes
-- check_simp_lc List.foldlM_reverse List.reverse_cons

attribute [-simp] List.takeWhile_append_dropWhile
-- fixes many lemmas

attribute [simp] or_assoc
attribute [simp] and_assoc
-- fixes
-- check_simp_lc List.mem_append List.cons_append

-- Bug: tactic 'rfl' failed, equality expected
-- check_simp_lc List.getElem?_eq_get? List.getElem?_eq_get?

-- This seems to be needed
attribute [simp] List.prefix_refl
attribute [simp] List.suffix_refl
attribute [simp] List.nil_suffix
attribute [simp] List.nil_prefix
attribute [simp] List.nil_infix


check_simp_lc ignoring
  List.disjoint_cons_left List.disjoint_cons_right
  List.disjoint_cons_left List.disjoint_singleton
  List.disjoint_cons_left List.disjoint_append_right
  List.singleton_disjoint List.disjoint_cons_right
  List.disjoint_append_left List.disjoint_cons_right
  List.disjoint_append_left List.disjoint_singleton
  List.disjoint_append_left List.disjoint_append_right

  List.findIdx?_cons List.findIdx?_succ

  List.get?_concat_length List.length_replicate
  List.get?_concat_length List.length_zipWith
  List.get?_concat_length List.length_concat
  List.get?_concat_length List.length_map
  List.get?_concat_length List.length_set
  List.get?_concat_length List.length_dropLast
  List.get?_concat_length List.length_dropLast_cons
  List.get?_concat_length List.length_tail

  List.reverse_prefix List.reverse_cons
  List.reverse_prefix List.reverse_reverse
  List.reverse_prefix List.reverse_append
  List.reverse_prefix List.reverse_nil

  List.getLast_append List.cons_append
  List.getLast_append List.singleton_append
  List.getLast_append List.append_assoc
  List.getLast_append List.nil_append

  List.filterMap_join List.join_cons
  List.filterMap_some List.filterMap_join

  List.take_length List.length_replicate
  List.take_length List.length_zipWith
  List.take_length List.length_concat
  List.take_length List.length_map
  List.take_length List.length_set
  List.take_length List.length_dropLast
  List.take_length List.length_dropLast_cons
  List.take_length List.length_tail

  -- nontrivial precondition.
  -- Is mem_of_find?_eq_some too particular to be in the default simp set?
  List.mem_map List.mem_of_find?_eq_some
  List.mem_reverseAux List.mem_of_find?_eq_some
  List.mem_cons List.mem_of_find?_eq_some
  List.mem_singleton List.mem_of_find?_eq_some
  List.mem_inter_iff List.mem_of_find?_eq_some
  List.mem_erase_of_ne List.mem_of_find?_eq_some
  List.mem_reverse List.mem_of_find?_eq_some
  List.mem_union_iff List.mem_of_find?_eq_some
  List.mem_filterMap List.mem_of_find?_eq_some
  List.mem_eraseP_of_neg List.mem_of_find?_eq_some
  List.mem_append List.mem_of_find?_eq_some
  List.mem_insert_iff List.mem_of_find?_eq_some
  List.mem_range'_1 List.mem_of_find?_eq_some
  List.mem_range List.mem_of_find?_eq_some

  List.mem_map List.map_map
  List.mem_map List.map_cons
  List.mem_map List.map_append
  List.mem_reverseAux List.reverseAux_cons
  List.mem_reverse List.reverse_cons
  List.mem_filterMap List.filterMap_join
  List.mem_filterMap List.filterMap_cons
  List.mem_eraseP_of_neg List.eraseP_cons_of_pos
  List.mem_insert_iff List.insert_of_mem

  List.filter_sublist List.filter_cons_of_pos
  List.filter_sublist List.filter_cons_of_neg
  List.filter_sublist List.filter_filter
  List.filter_sublist List.filter_append
  List.reverse_sublist List.reverse_cons
  List.reverse_sublist List.reverse_reverse
  List.reverse_sublist List.reverse_append

  List.append_sublist_append_left List.append_nil
  List.append_sublist_append_left List.cons_append
  List.append_sublist_append_left List.singleton_append
  List.append_sublist_append_left List.take_append_drop

  List.reverse_suffix List.reverse_cons
  List.reverse_suffix List.reverse_reverse
  List.reverse_suffix List.reverse_append
  List.reverse_suffix List.reverse_nil

  List.dropLast_append_cons List.cons_append
  List.dropLast_concat List.cons_append

  List.enumFrom_map_fst List.enumFrom_cons
  List.infix_append' List.cons_append
  List.infix_append' List.singleton_append
  List.infix_append' List.append_assoc
  List.infix_append' List.nil_append
  List.infix_append' List.append_nil
  List.infix_append' List.take_append_drop
  List.infix_append' List.range'_append_1
  List.reverse_infix List.reverse_cons
  List.reverse_infix List.reverse_reverse
  List.reverse_infix List.reverse_append

  List.length_take List.take_cons_succ
  List.length_take List.take_succ_cons
  List.getLast?_concat List.cons_append
  List.getLast?_concat List.singleton_append
  List.getLast?_concat List.append_assoc

  List.sizeOf_get List.get_replicate
  List.sizeOf_get List.get_map
  List.sizeOf_get List.get_set_eq
  List.sizeOf_get List.get_set_ne
  List.sizeOf_get List.get_dropLast
  List.sizeOf_get List.get_cons_zero
  List.sizeOf_get List.get_cons_succ
  List.sizeOf_get List.get_cons_succ'
  List.sizeOf_get List.get_cons_cons_one
  List.sizeOf_get List.cons.sizeOf_spec
  List.append_cancel_left_eq List.append_nil

  List.nil_eq_append List.append_nil

  List.drop_length List.length_replicate
  List.drop_length List.length_zipWith
  List.drop_length List.length_concat
  List.drop_length List.length_map
  List.drop_length List.length_set
  List.drop_length List.length_dropLast
  List.drop_length List.length_dropLast_cons
  List.drop_length List.length_tail

  List.drop_left List.length_replicate
  List.drop_left List.length_zipWith
  List.drop_left List.length_concat
  List.drop_left List.length_map
  List.drop_left List.length_set
  List.drop_left List.length_dropLast
  List.drop_left List.length_dropLast_cons
  List.drop_left List.length_tail

  List.filter_filter List.filter_cons_of_pos

  List.zipWith_map List.map_map
  List.zipWith_map List.map_cons
  List.zipWith_map List.map_append
