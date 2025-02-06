import Mathlib.Tactic


lemma Sum.swap_inj {α β : Type} : (@Sum.swap α β).Injective := by
  intro
  aesop

lemma finset_of_cardinality_between {α β : Type} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α < n) (hn : n ≤ Fintype.card α + Fintype.card β) :
    ∃ b : Finset β, Fintype.card (α ⊕ b) = n ∧ Nonempty b := by
  have beta : n - Fintype.card α ≤ Fintype.card β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - Fintype.card α :=
    (Finset.exists_subset_card_eq beta).imp (by simp)
  use s
  rw [Fintype.card_sum, Fintype.card_coe, hs]
  constructor
  · omega
  · by_contra ifempty
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at ifempty
      exact Finset.eq_empty_of_forall_not_mem ifempty
    omega


variable {R : Type}

lemma zero_in_set_range_singType_cast [Ring R] : (0 : R) ∈ Set.range SignType.cast :=
  ⟨0, rfl⟩

lemma in_set_range_singType_cast_mul_in_set_range_singType_cast [Ring R] {a b : R}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨_, SignType.coe_mul a' b'⟩

lemma in_set_range_singType_cast_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ Set.range SignType.cast ↔ |a| ∈ Set.range SignType.cast := by
  constructor
  · rintro ⟨s, rfl⟩
    cases s with
    | zero => use 0; simp
    | pos => use 1; simp
    | neg => use 1; simp
  · intro ⟨s, hs⟩
    symm at hs
    cases s with
    | zero =>
      rw [SignType.zero_eq_zero, SignType.coe_zero, abs_eq_zero] at hs
      exact ⟨0, hs.symm⟩
    | pos =>
      rw [SignType.pos_eq_one, abs_eq_max_neg, max_eq_iff] at hs
      cases hs with
      | inl poz =>
        exact ⟨1, poz.left.symm⟩
      | inr neg =>
        use -1
        rw [neg_eq_iff_eq_neg] at neg
        exact neg.left.symm
    | neg =>
      exfalso
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      have h0 := (abs_nonneg a).trans_eq hs
      norm_num at h0

lemma inv_eq_self_of_in_set_range_singType_cast [Field R] {a : R} (ha : a ∈ Set.range SignType.cast) :
    1 / a = a := by
  obtain ⟨s, rfl⟩ := ha
  cases s <;> simp
