import Mathlib.Tactic

prefix:max "#" => Fintype.card
prefix:max "◩" => Sum.inl
prefix:max "◪" => Sum.inr

variable {α : Type}

@[simp]
abbrev Function.range {ι : Type} (f : ι → α) : Set α := Set.range f

lemma Sum.swap_inj {β : Type} : (@Sum.swap α β).Injective := by
  intro
  aesop

lemma finset_of_cardinality_between {β : Type} [Fintype α] [Fintype β] {n : ℕ}
    (hα : #α < n) (hn : n ≤ #α + #β) :
    ∃ b : Finset β, #(α ⊕ b) = n ∧ Nonempty b := by
  have beta : n - #α ≤ #β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - #α :=
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

lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  rw [←Finset.sum_subset (Finset.subset_univ {0})]
  · simp
  intro x _ hx
  apply hf
  simpa using hx


lemma zero_in_singTypeCastRange [Ring α] : (0 : α) ∈ SignType.cast.range :=
  ⟨0, rfl⟩

lemma in_singTypeCastRange_mul_in_singTypeCastRange [Ring α] {a b : α}
    (ha : a ∈ SignType.cast.range) (hb : b ∈ SignType.cast.range) :
    a * b ∈ SignType.cast.range := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨_, SignType.coe_mul a' b'⟩

lemma neg_one_mul_in_singTypeCastRange [Ring α] {a : α}
    (ha : a ∈ SignType.cast.range) :
    (-1) * a ∈ SignType.cast.range :=
  in_singTypeCastRange_mul_in_singTypeCastRange ⟨-1, rfl⟩ ha

lemma in_singTypeCastRange_of_neg_one_mul_self [Ring α] {a : α}
    (ha : (-1) * a ∈ SignType.cast.range) :
    a ∈ SignType.cast.range := by
  rw [←neg_neg a, neg_eq_neg_one_mul]
  apply neg_one_mul_in_singTypeCastRange
  rwa [neg_eq_neg_one_mul]

lemma in_singTypeCastRange_iff_abs [LinearOrderedCommRing α] (a : α) :
    a ∈ SignType.cast.range ↔ |a| ∈ SignType.cast.range := by
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

lemma inv_eq_self_of_in_singTypeCastRange [Field α] {a : α} (ha : a ∈ SignType.cast.range) :
    1 / a = a := by
  obtain ⟨s, rfl⟩ := ha
  cases s <;> simp
