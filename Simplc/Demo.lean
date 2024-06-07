import Simplc

-- set_option trace.simplc true

-- attribute [simp] Function.comp_assoc
@[simp]
theorem Function.comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl
-- fixes
-- simp_lc_check List.map_map List.map_map

@[simp] theorem takeWhile_nil : List.takeWhile p [] = [] := rfl
-- fixes
-- simp_lc_check List.takeWhile_append_dropWhile List.dropWhile_nil

attribute [simp] or_assoc
attribute [simp] and_assoc
-- fixes
-- simp_lc_check List.mem_append List.cons_append

-- Bug: tactic 'rfl' failed, equality expected
-- simp_lc_check List.getElem?_eq_get? List.getElem?_eq_get?

-- Not a good lemma: Non-linear, and goes against the reduction direction
attribute [-simp] List.get_cons_drop
-- simp_lc_check List.any_cons List.get_cons_drop

-- Unclear which one is at fault here
simp_lc_whitelist List.head?_reverse List.reverse_cons
simp_lc_whitelist List.head?_reverse List.reverse_append

-- This should be resolvable using List.mem_cons, but
-- because of the dependency in `decide (x ∈ a :: as)`
simp_lc_whitelist List.elem_eq_mem List.contains_cons


-- We need the non-linear version of List.drop_left
attribute [-simp] List.drop_left
attribute [simp] List.drop_left'
-- simp_lc_check List.drop_left List.length_replicate


-- List.drop_drop adds the numbers in the wrong order
attribute [-simp] List.drop_drop
@[simp] theorem List.drop_drop' (n : Nat) : ∀ (m) (l : List α), drop n (drop m l) = drop (m + n) l := by
  intros; rw [List.drop_drop, Nat.add_comm]

def Nat.add_assoc' : ∀ (n m k : Nat), n + (m + k) = (n + m  )+ k := by
  intros; rw [Nat.add_assoc]

-- One of these needed to join after List.drop_drop' List.drop_drop'
-- attribute [simp] Nat.add_assoc
attribute [simp] Nat.add_assoc'
-- simp_lc_check List.drop_drop' List.drop_drop'

-- Needed to join after List.drop_drop' List.drop_left'
@[simp] theorem List.drop_left_add {l₁ l₂ : List α} {m n} (h : length l₁ = n) :
  List.drop (n + m) (l₁ ++ l₂) = List.drop m l₂ := by
  rw [← List.drop_drop', List.drop_left' h]
-- simp_lc_check List.drop_drop' List.drop_left'

attribute [-simp] List.get?_drop
@[simp]
theorem List.get?_drop' (L : List α) (i j : Nat) : get? (L.drop i) j = get? L (j + i) := by
  rw [List.get?_drop, Nat.add_comm]
-- needed for the following, together with Nat.add_assoc'
-- simp_lc_check List.get?_drop' List.drop_succ_cons

-- Why does this not work:
-- attribute [simp] List.append_ne_nil_of_ne_nil_left
-- attribute [simp] List.append_ne_nil_of_ne_nil_right
-- -- set_option trace.Meta.Tactic.simp true in
-- simp_lc_check List.dropLast_append_of_ne_nil List.cons_append


simp_lc_whitelist List.get?_map List.map_cons
simp_lc_whitelist List.get?_map List.map_append
simp_lc_whitelist List.get?_drop' List.drop_drop'
simp_lc_whitelist List.get?_drop' List.drop_left'
simp_lc_whitelist List.get?_drop' List.drop_left_add
simp_lc_whitelist List.get?_drop' List.drop_append
simp_lc_whitelist List.get?_drop' List.drop_length
simp_lc_whitelist List.nth_take_of_succ List.take_cons_succ
simp_lc_whitelist List.get?_concat_length List.append_assoc
simp_lc_whitelist List.get?_concat_length List.length_replicate
simp_lc_whitelist List.get?_concat_length List.length_zipWith
simp_lc_whitelist List.get?_concat_length List.length_concat
simp_lc_whitelist List.get?_concat_length List.length_map
simp_lc_whitelist List.get?_concat_length List.length_set
simp_lc_whitelist List.get?_concat_length List.length_dropLast
simp_lc_whitelist List.get?_concat_length List.length_dropLast_cons
simp_lc_whitelist List.get?_concat_length List.length_drop
simp_lc_whitelist List.get?_concat_length List.length_reverse
simp_lc_whitelist List.get?_concat_length List.length_take
simp_lc_whitelist List.get?_concat_length List.length_append
simp_lc_whitelist List.get?_concat_length List.length_zip
simp_lc_whitelist List.get?_concat_length List.enumFrom_length
simp_lc_whitelist List.get?_concat_length List.enum_length
simp_lc_whitelist List.get_singleton List.get_cons_succ'
simp_lc_whitelist List.getLast_append List.cons_append
simp_lc_whitelist List.getLast_append List.singleton_append
simp_lc_whitelist List.getLast_append List.append_assoc
simp_lc_whitelist List.filterMap_join List.join_cons
simp_lc_whitelist List.filterMap_map List.map_append
simp_lc_whitelist List.filterMap_map List.map_id'
simp_lc_whitelist List.filterMap_map List.map_id
simp_lc_whitelist List.filterMap_some List.filterMap_join
simp_lc_whitelist List.take_length List.length_replicate
simp_lc_whitelist List.take_length List.length_zipWith
simp_lc_whitelist List.take_length List.length_concat
simp_lc_whitelist List.take_length List.length_map
simp_lc_whitelist List.take_length List.length_set
simp_lc_whitelist List.take_length List.length_dropLast
simp_lc_whitelist List.take_length List.length_dropLast_cons
simp_lc_whitelist List.take_length List.length_drop
simp_lc_whitelist List.take_length List.length_reverse
simp_lc_whitelist List.take_length List.length_take
simp_lc_whitelist List.take_length List.length_append
simp_lc_whitelist List.take_length List.length_zip
simp_lc_whitelist List.take_length List.enumFrom_length
simp_lc_whitelist List.take_length List.enum_length
simp_lc_whitelist List.take_left List.length_replicate
simp_lc_whitelist List.take_left List.length_zipWith
simp_lc_whitelist List.take_left List.length_concat
simp_lc_whitelist List.take_left List.length_map
simp_lc_whitelist List.take_left List.length_set
simp_lc_whitelist List.take_left List.length_dropLast
simp_lc_whitelist List.take_left List.length_dropLast_cons
simp_lc_whitelist List.take_left List.length_drop
simp_lc_whitelist List.take_left List.length_reverse
simp_lc_whitelist List.take_left List.length_take
simp_lc_whitelist List.take_left List.length_append
simp_lc_whitelist List.take_left List.length_zip
simp_lc_whitelist List.take_left List.enumFrom_length
simp_lc_whitelist List.take_left List.enum_length
simp_lc_whitelist List.take_left List.takeWhile_append_dropWhile
simp_lc_whitelist List.take_left List.take_append_drop
simp_lc_whitelist List.take_left List.append_assoc
simp_lc_whitelist List.foldrM_reverse List.reverse_cons
simp_lc_whitelist List.foldrM_reverse List.reverse_append
simp_lc_whitelist List.foldrM_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.foldrM_append List.take_append_drop
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_map
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_reverseAux
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_cons
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_singleton
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_reverse
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_filterMap
simp_lc_whitelist List.mem_of_find?_eq_some List.mem_append
simp_lc_whitelist List.mem_map List.map_map
simp_lc_whitelist List.mem_map List.map_cons
simp_lc_whitelist List.mem_map List.map_append
simp_lc_whitelist List.mem_reverseAux List.reverseAux_cons
simp_lc_whitelist List.mem_reverse List.reverse_cons
simp_lc_whitelist List.mem_reverse List.reverse_append
simp_lc_whitelist List.mem_filterMap List.filterMap_join
simp_lc_whitelist List.mem_filterMap List.filterMap_map
simp_lc_whitelist List.mem_filterMap List.filterMap_cons
simp_lc_whitelist List.mem_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.mem_append List.take_append_drop
simp_lc_whitelist List.mem_insert_iff List.mem_of_find?_eq_some
simp_lc_whitelist List.mem_insert_iff List.insert_of_mem
simp_lc_whitelist List.erase_cons_tail List.erase_cons_head
simp_lc_whitelist List.dropLast_append_of_ne_nil List.cons_append
simp_lc_whitelist List.dropLast_append_of_ne_nil List.singleton_append
simp_lc_whitelist List.dropLast_append_of_ne_nil List.takeWhile_append_dropWhile
simp_lc_whitelist List.dropLast_append_of_ne_nil List.take_append_drop
simp_lc_whitelist List.dropLast_concat List.cons_append
simp_lc_whitelist List.map_map List.map_id'
simp_lc_whitelist List.map_map List.map_id
simp_lc_whitelist List.map_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.map_append List.take_append_drop
simp_lc_whitelist List.map_id' List.map_map
simp_lc_whitelist List.map_id List.map_map
simp_lc_whitelist List.foldr_reverse List.foldr_self_append
simp_lc_whitelist List.foldr_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.foldr_append List.take_append_drop
simp_lc_whitelist List.foldlM_reverse List.reverse_cons
simp_lc_whitelist List.foldlM_reverse List.reverse_append
simp_lc_whitelist List.foldlM_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.foldlM_append List.take_append_drop
simp_lc_whitelist List.reverse_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.reverse_append List.take_append_drop
simp_lc_whitelist List.getLastD_concat List.append_assoc
simp_lc_whitelist List.take_append_drop List.drop_drop'
simp_lc_whitelist List.take_append_drop List.drop_left'
simp_lc_whitelist List.take_append_drop List.drop_left_add
simp_lc_whitelist List.take_append_drop List.drop_append
simp_lc_whitelist List.append_assoc List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_assoc List.take_append_drop
simp_lc_whitelist List.length_zipWith List.zipWith_cons_cons
simp_lc_whitelist List.length_dropLast List.dropLast_append_of_ne_nil
simp_lc_whitelist List.length_drop List.drop_drop'
simp_lc_whitelist List.length_drop List.drop_left'
simp_lc_whitelist List.length_drop List.drop_left_add
simp_lc_whitelist List.length_drop List.drop_append
simp_lc_whitelist List.length_reverse List.reverse_append
simp_lc_whitelist List.length_take List.take_cons_succ
simp_lc_whitelist List.length_take List.take_left
simp_lc_whitelist List.length_append List.cons_append
simp_lc_whitelist List.length_append List.singleton_append
simp_lc_whitelist List.length_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.length_append List.take_append_drop
simp_lc_whitelist List.length_zip List.zip_cons_cons
simp_lc_whitelist List.getLast?_reverse List.reverse_append
simp_lc_whitelist List.getLast?_concat List.cons_append
simp_lc_whitelist List.getLast?_concat List.singleton_append
simp_lc_whitelist List.getLast?_concat List.append_assoc
simp_lc_whitelist List.sizeOf_get List.get_replicate
simp_lc_whitelist List.sizeOf_get List.get_map
simp_lc_whitelist List.sizeOf_get List.get_set_eq
simp_lc_whitelist List.sizeOf_get List.get_set_ne
simp_lc_whitelist List.sizeOf_get List.get_dropLast
simp_lc_whitelist List.sizeOf_get List.get_cons_zero
simp_lc_whitelist List.sizeOf_get List.get_cons_succ'
simp_lc_whitelist List.sizeOf_get List.get_cons_succ
simp_lc_whitelist List.sizeOf_get List.get_cons_cons_one
simp_lc_whitelist List.sizeOf_get List.get_singleton
simp_lc_whitelist List.sizeOf_get List.cons.sizeOf_spec
simp_lc_whitelist List.sizeOf_get List.nil.sizeOf_spec
simp_lc_whitelist List.foldl_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.foldl_append List.take_append_drop
simp_lc_whitelist List.drop_eq_nil_iff_le List.drop_drop'
simp_lc_whitelist List.drop_eq_nil_iff_le List.drop_left'
simp_lc_whitelist List.drop_eq_nil_iff_le List.drop_left_add
simp_lc_whitelist List.drop_eq_nil_iff_le List.drop_append
simp_lc_whitelist List.reverse_eq_nil_iff List.reverse_append
simp_lc_whitelist List.take_eq_take List.take_cons_succ
simp_lc_whitelist List.take_eq_take List.take_zero
simp_lc_whitelist List.take_eq_take List.take_length
simp_lc_whitelist List.take_eq_take List.take_left
simp_lc_whitelist List.take_eq_take List.take_cons_succ
simp_lc_whitelist List.take_eq_take List.take_zero
simp_lc_whitelist List.take_eq_take List.take_length
simp_lc_whitelist List.take_eq_take List.take_left
simp_lc_whitelist List.take_eq_nil_iff List.take_left
simp_lc_whitelist List.append_cancel_left_eq List.append_nil
simp_lc_whitelist List.append_cancel_left_eq List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_cancel_left_eq List.take_append_drop
simp_lc_whitelist List.append_cancel_left_eq List.append_nil
simp_lc_whitelist List.append_cancel_left_eq List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_cancel_left_eq List.take_append_drop
simp_lc_whitelist List.append_cancel_right_eq List.cons_append
simp_lc_whitelist List.append_cancel_right_eq List.singleton_append
simp_lc_whitelist List.append_cancel_right_eq List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_cancel_right_eq List.take_append_drop
simp_lc_whitelist List.append_cancel_right_eq List.append_assoc
simp_lc_whitelist List.append_cancel_right_eq List.nil_append
simp_lc_whitelist List.append_cancel_right_eq List.cons_append
simp_lc_whitelist List.append_cancel_right_eq List.singleton_append
simp_lc_whitelist List.append_cancel_right_eq List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_cancel_right_eq List.take_append_drop
simp_lc_whitelist List.append_cancel_right_eq List.append_assoc
simp_lc_whitelist List.append_cancel_right_eq List.nil_append
simp_lc_whitelist List.append_eq_nil List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_eq_nil List.take_append_drop
simp_lc_whitelist List.nil_eq_append List.append_nil
simp_lc_whitelist List.nil_eq_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.nil_eq_append List.take_append_drop
simp_lc_whitelist List.nil_eq_append List.nil_append
simp_lc_whitelist List.length_eq_zero List.length_replicate
simp_lc_whitelist List.length_eq_zero List.length_zipWith
simp_lc_whitelist List.length_eq_zero List.length_dropLast
simp_lc_whitelist List.length_eq_zero List.length_dropLast_cons
simp_lc_whitelist List.length_eq_zero List.length_drop
simp_lc_whitelist List.length_eq_zero List.length_take
simp_lc_whitelist List.length_eq_zero List.length_append
simp_lc_whitelist List.length_eq_zero List.length_zip
simp_lc_whitelist List.length_eq_zero List.enumFrom_length
simp_lc_whitelist List.length_eq_zero List.enum_length
simp_lc_whitelist List.get?_eq_none List.get?_drop'
simp_lc_whitelist List.get?_eq_none List.nth_take_of_succ
simp_lc_whitelist List.drop_drop' List.drop_length
simp_lc_whitelist List.drop_drop' List.drop_succ_cons
simp_lc_whitelist List.drop_drop' List.drop_left_add
simp_lc_whitelist List.drop_drop' List.drop_append
simp_lc_whitelist List.drop_drop' List.drop_length
simp_lc_whitelist List.drop_left' List.drop_length
simp_lc_whitelist List.drop_left' List.append_nil
simp_lc_whitelist List.drop_left' List.cons_append
simp_lc_whitelist List.drop_left' List.singleton_append
simp_lc_whitelist List.drop_left' List.takeWhile_append_dropWhile
simp_lc_whitelist List.drop_left' List.take_append_drop
simp_lc_whitelist List.drop_left' List.append_assoc
simp_lc_whitelist List.drop_left' List.nil_append
simp_lc_whitelist List.drop_zero List.drop_left'
simp_lc_whitelist List.drop_left_add List.drop_left'
simp_lc_whitelist List.drop_left_add List.append_nil
simp_lc_whitelist List.drop_left_add List.cons_append
simp_lc_whitelist List.drop_left_add List.singleton_append
simp_lc_whitelist List.drop_left_add List.takeWhile_append_dropWhile
simp_lc_whitelist List.drop_left_add List.take_append_drop
simp_lc_whitelist List.drop_left_add List.append_assoc
simp_lc_whitelist List.drop_left_add List.nil_append
simp_lc_whitelist List.drop_append List.drop_left'
simp_lc_whitelist List.drop_append List.length_concat
simp_lc_whitelist List.drop_append List.length_cons
simp_lc_whitelist List.drop_append List.length_singleton
simp_lc_whitelist List.drop_append List.length_append
simp_lc_whitelist List.drop_append List.length_insert_of_not_mem
simp_lc_whitelist List.drop_append List.append_nil
simp_lc_whitelist List.drop_append List.cons_append
simp_lc_whitelist List.drop_append List.singleton_append
simp_lc_whitelist List.drop_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.drop_append List.take_append_drop
simp_lc_whitelist List.drop_append List.append_assoc
simp_lc_whitelist List.drop_length List.length_replicate
simp_lc_whitelist List.drop_length List.length_zipWith
simp_lc_whitelist List.drop_length List.length_map
simp_lc_whitelist List.drop_length List.length_set
simp_lc_whitelist List.drop_length List.length_dropLast
simp_lc_whitelist List.drop_length List.length_dropLast_cons
simp_lc_whitelist List.drop_length List.length_drop
simp_lc_whitelist List.drop_length List.length_reverse
simp_lc_whitelist List.drop_length List.length_take
simp_lc_whitelist List.drop_length List.length_zip
simp_lc_whitelist List.drop_length List.enumFrom_length
simp_lc_whitelist List.drop_length List.enum_length
simp_lc_whitelist List.filter_filter List.filter_cons_of_pos
simp_lc_whitelist List.filter_append List.cons_append
simp_lc_whitelist List.filter_append List.singleton_append
simp_lc_whitelist List.filter_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.filter_append List.take_append_drop
simp_lc_whitelist List.append_bind List.bind_id
simp_lc_whitelist List.append_bind List.takeWhile_append_dropWhile
simp_lc_whitelist List.append_bind List.take_append_drop
simp_lc_whitelist List.mapM_append List.takeWhile_append_dropWhile
simp_lc_whitelist List.mapM_append List.take_append_drop
simp_lc_whitelist List.zipWith_map List.map_map
simp_lc_whitelist List.zipWith_map List.map_cons
simp_lc_whitelist List.zipWith_map List.map_append
simp_lc_whitelist List.zipWith_map List.map_id'
simp_lc_whitelist List.zipWith_map List.map_id
simp_lc_whitelist List.zipWith_map List.map_map
simp_lc_whitelist List.zipWith_map List.map_cons
simp_lc_whitelist List.zipWith_map List.map_append
simp_lc_whitelist List.zipWith_map List.map_id'
simp_lc_whitelist List.zipWith_map List.map_id

simp_lc_whitelist List.get_set_eq Fin.eta
set_option maxHeartbeats 2000

set_option pp.explicit true
#check sizeOf_default
#check Lean.MetavarKind.natural.sizeOf_spec
-- set_option trace.simplc true
-- simp_lc_check sizeOf_default Lean.MetavarKind.natural.sizeOf_spec

simp_lc_check
