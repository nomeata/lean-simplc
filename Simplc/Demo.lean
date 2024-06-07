import Simplc

simp_lc_ignore eq_self
simp_lc_ignore sizeOf_default

-- (i : Nonempty b) ⊢ b
simp_lc_whitelist imp_self forall_const

-- Missing List.join_append
simp_lc_whitelist List.append_bind List.bind_id

@[simp] theorem Char.toNat_mk : Char.toNat ⟨v,n⟩ = v.toNat := rfl
-- for simp_lc_inspect Char.mk.sizeOf_spec Char.sizeOf

-- Better ite_not?
-- Probably more an issue with how simp_lc puts [Decidable ¬p] into the context
-- rather than only [Decidable p]
@[simp]
theorem ite_not' (p : Prop) {inst : Decidable ¬p} (x y : α) :
  ite (¬p) x y = @ite _ p (by exact Classical.propDecidable p) y x :=
  sorry
simp_lc_ignore ite_not'
-- for
-- simp_lc_inspect dite_not dite_eq_ite

-- missing theorem, variant of `addNat_subNat`
@[simp] theorem addNat_subNat {i : Fin (n + 1)} (h : 1 ≤ (i : Nat)) : (Fin.subNat 1 i h).succ = i :=
  sorry
-- for
-- simp_lc_inspect Fin.addNat_one Fin.addNat_subNat

-- This is probably not so bad, because it is a highly conditional lemma
-- but is it really useful to try this on every mem goal?
simp_lc_ignore List.mem_of_find?_eq_some

-- variant of add_one_le_iff
@[simp] theorem add_one_eq_iff {n : Nat} : ∀ {k : Fin (n + 1)}, k + 1 = k ↔ k = Fin.last _ := by
  sorry
-- for
-- simp_lc_inspect Fin.le_zero_iff Fin.add_one_le_iff

@[simp] theorem bne_not_left (x y : Bool) : ((!x) != y) = !(x != y) := sorry
@[simp] theorem bne_not_right (x y : Bool) : (x != (!y)) = !(x != y) := sorry
-- for
-- simp_lc_inspect Bool.bne_assoc Bool.bne_true

simp_lc_whitelist Bool.bne_assoc bne_self_eq_false'
simp_lc_whitelist Bool.bne_assoc Bool.bne_self_left
simp_lc_whitelist Bool.bne_assoc Bool.bne_not_self
simp_lc_whitelist bne_self_eq_false Bool.bne_assoc

simp_lc_whitelist Bool.not_not_eq Bool.not_eq_not

-- here simp_lc builds bad mvar assignments
-- simp_lc_inspect Fin.is_lt Nat.lt_irrefl

-- set_option simplc.stderr true in
-- simp_lc_check root

#exit

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
