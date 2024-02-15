import Simplc

attribute [simp] Function.comp_def
-- fixes
-- check_simp_lc List.map_map List.map_map

@[simp] theorem takeWhile_nil : List.takeWhile p [] = [] := rfl
-- fixes
check_simp_lc List.takeWhile_append_dropWhile List.dropWhile_nil

attribute [simp] List.foldrM
-- fixes
-- check_simp_lc List.foldlM_reverse List.reverse_cons

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

  List.append_sublist_append_left List.takeWhile_append_dropWhile
  List.infix_append' List.takeWhile_append_dropWhile
