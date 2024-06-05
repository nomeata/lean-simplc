import Simplc

attribute [simp] Function.comp_def
-- fixes
-- check_simp_lc List.map_map List.map_map

@[simp] theorem takeWhile_nil : List.takeWhile p [] = [] := rfl
-- fixes
check_simp_lc List.takeWhile_append_dropWhile List.dropWhile_nil

attribute [simp] or_assoc
attribute [simp] and_assoc
-- fixes
-- check_simp_lc List.mem_append List.cons_append

-- Bug: tactic 'rfl' failed, equality expected
-- check_simp_lc List.getElem?_eq_get? List.getElem?_eq_get?

set_option trace.simplc true
check_simp_lc  List.any_cons List.get_cons_drop

#exit
set_option trace.simplc true
check_simp_lc ignoring
  List.get?_concat_length List.length_replicate
  List.get?_concat_length List.length_zipWith
  List.get?_concat_length List.length_concat
  List.get?_concat_length List.length_map
  List.get?_concat_length List.length_set
  List.get?_concat_length List.length_dropLast
  List.get?_concat_length List.length_dropLast_cons

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

  -- nontrivial precondition.
  -- Is mem_of_find?_eq_some too particular to be in the default simp set?
  List.mem_map List.mem_of_find?_eq_some
  List.mem_reverseAux List.mem_of_find?_eq_some
  List.mem_cons List.mem_of_find?_eq_some
  List.mem_singleton List.mem_of_find?_eq_some
  List.mem_reverse List.mem_of_find?_eq_some
  List.mem_filterMap List.mem_of_find?_eq_some
  List.mem_append List.mem_of_find?_eq_some
  List.mem_insert_iff List.mem_of_find?_eq_some

  List.mem_map List.map_map
  List.mem_map List.map_cons
  List.mem_map List.map_append
  List.mem_reverseAux List.reverseAux_cons
  List.mem_reverse List.reverse_cons
  List.mem_filterMap List.filterMap_join
  List.mem_filterMap List.filterMap_cons
  List.mem_insert_iff List.insert_of_mem

  List.dropLast_append_cons List.cons_append
  List.dropLast_concat List.cons_append

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

  List.drop_left List.length_replicate
  List.drop_left List.length_zipWith
  List.drop_left List.length_concat
  List.drop_left List.length_map
  List.drop_left List.length_set
  List.drop_left List.length_dropLast
  List.drop_left List.length_dropLast_cons

  List.filter_filter List.filter_cons_of_pos

  List.zipWith_map List.map_map
  List.zipWith_map List.map_cons
  List.zipWith_map List.map_append

  --and more, unsorted
  List.get?_map List.map_cons
  List.get?_map List.map_append
  List.get?_concat_length List.append_assoc
  List.get?_concat_length List.length_reverse
  List.get?_concat_length List.length_take
  List.get?_concat_length List.length_append
  List.get?_concat_length List.length_zip
  List.get?_concat_length List.enumFrom_length
  List.get?_concat_length List.enum_length
  List.filterMap_join List.filterMap_some
  List.take_length List.length_drop
  List.take_length List.length_reverse
  List.take_length List.length_take
  List.take_length List.length_append
  List.take_length List.length_zip
  List.take_length List.enumFrom_length
  List.take_length List.enum_length
  List.mem_of_find?_eq_some List.mem_map
  List.mem_of_find?_eq_some List.mem_reverseAux
  List.mem_of_find?_eq_some List.mem_cons
  List.mem_of_find?_eq_some List.mem_singleton
  List.mem_of_find?_eq_some List.mem_reverse
  List.mem_of_find?_eq_some List.mem_filterMap
  List.mem_of_find?_eq_some List.mem_append
  List.mem_of_find?_eq_some List.mem_insert_iff
  List.mem_reverse List.reverse_append
  List.mem_append List.takeWhile_append_dropWhile
  List.mem_append List.take_append_drop
  List.dropLast_append_cons List.append_assoc
  List.dropLast_concat List.append_assoc
  List.map_append List.takeWhile_append_dropWhile
  List.map_append List.take_append_drop
  List.foldr_append List.takeWhile_append_dropWhile
  List.foldr_append List.take_append_drop
  List.foldlM_append List.takeWhile_append_dropWhile
  List.foldlM_append List.take_append_drop
  List.reverse_append List.take_append_drop
  List.getLastD_concat List.append_assoc
  List.append_assoc List.takeWhile_append_dropWhile
  List.append_assoc List.take_append_drop
  List.length_dropLast List.dropLast_append_cons
  List.length_drop List.drop_left
  List.length_reverse List.reverse_append
  List.length_append List.cons_append
  List.length_append List.singleton_append
  List.length_append List.takeWhile_append_dropWhile
  List.length_append List.take_append_drop
  List.length_append List.append_assoc
  List.length_zip List.zip_cons_cons
  List.foldl_append List.takeWhile_append_dropWhile
  List.foldl_append List.take_append_drop
  List.reverse_eq_nil_iff List.reverse_append
  List.append_cancel_left_eq List.takeWhile_append_dropWhile
  List.append_cancel_left_eq List.take_append_drop
  List.append_cancel_left_eq List.takeWhile_append_dropWhile
  List.append_cancel_left_eq List.take_append_drop
  List.append_cancel_right_eq List.cons_append
  List.append_cancel_right_eq List.singleton_append
  List.append_cancel_right_eq List.takeWhile_append_dropWhile
  List.append_cancel_right_eq List.take_append_drop
  List.append_cancel_right_eq List.append_assoc
  List.append_cancel_right_eq List.nil_append
  List.append_cancel_right_eq List.cons_append
  List.append_cancel_right_eq List.singleton_append
  List.append_cancel_right_eq List.takeWhile_append_dropWhile
  List.append_cancel_right_eq List.take_append_drop
  List.append_cancel_right_eq List.append_assoc
  List.append_cancel_right_eq List.nil_append
  List.append_eq_nil List.takeWhile_append_dropWhile
  List.append_eq_nil List.take_append_drop
  List.nil_eq_append List.takeWhile_append_dropWhile
  List.nil_eq_append List.take_append_drop
  List.nil_eq_append List.nil_append
  List.get?_eq_none List.get?_cons_succ
  List.drop_length List.length_drop
  List.drop_length List.length_reverse
  List.drop_length List.length_take
  List.drop_length List.length_append
  List.drop_length List.length_zip
  List.drop_length List.enumFrom_length
  List.drop_length List.enum_length
  List.drop_left List.length_drop
  List.drop_left List.length_reverse
  List.drop_left List.length_take
  List.drop_left List.length_append
  List.drop_left List.length_zip
  List.drop_left List.enumFrom_length
  List.drop_left List.enum_length
  List.drop_left List.takeWhile_append_dropWhile
  List.drop_left List.take_append_drop
  List.drop_left List.append_assoc
  List.filter_append List.cons_append
  List.filter_append List.singleton_append
  List.filter_append List.takeWhile_append_dropWhile
  List.filter_append List.take_append_drop
  List.append_bind List.bind_id
  List.append_bind List.takeWhile_append_dropWhile
  List.append_bind List.take_append_drop
  List.bind_id List.append_bind
  List.mapM_append List.takeWhile_append_dropWhile
  List.mapM_append List.take_append_drop
  List.zipWith_map List.map_id'
  List.zipWith_map List.map_id
  List.zipWith_map List.map_id'
  List.zipWith_map List.map_id

  List.foldlM_reverse List.reverse_cons
  List.foldlM_reverse List.reverse_append
  List.foldrM_reverse List.reverse_cons
  List.foldrM_reverse List.reverse_append

  List.foldrM_append List.takeWhile_append_dropWhile
  List.foldrM_append List.take_append_drop
