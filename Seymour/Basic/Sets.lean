import Seymour.Basic.Conversions

/-!
# Sets

This file provides lemmas about sets that are not present in Mathlib.
-/

variable {α : Type*}

lemma Disjoint.ni_right_of_in_left {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ X) : a ∉ Y :=
  (by simpa [hXY.inter_eq] using Set.mem_inter ha ·)

lemma Disjoint.ni_left_of_in_right {X Y : Set α} {a : α} (hXY : Disjoint X Y) (ha : a ∈ Y) : a ∉ X :=
  hXY.symm.ni_right_of_in_left ha

lemma in_left_of_in_union_of_ni_right {X Y : Set α} {a : α} (haXY : a ∈ X ∪ Y) (haY : a ∉ Y) : a ∈ X := by
  tauto_set

lemma in_right_of_in_union_of_ni_left {X Y : Set α} {a : α} (haXY : a ∈ X ∪ Y) (haX : a ∉ X) : a ∈ Y := by
  tauto_set

lemma singleton_inter_in_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ X :=
  Set.mem_of_mem_inter_left (ha.symm.subset rfl)

lemma singleton_inter_in_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ Y :=
  Set.mem_of_mem_inter_right (ha.symm.subset rfl)

lemma right_eq_right_of_union_eq_union {A₁ A₂ B₁ B₂ : Set α}
    (hA : A₁ = A₂) (hB₁ : A₁ ⫗ B₁) (hB₂ : A₂ ⫗ B₂) (hAB : A₁ ∪ B₁ = A₂ ∪ B₂) :
    B₁ = B₂ := by
  tauto_set

lemma union_disjoint_union_iff (A₁ A₂ B₁ B₂ : Set α) :
    (A₁ ∪ A₂) ⫗ (B₁ ∪ B₂) ↔ (A₁ ⫗ B₁ ∧ A₂ ⫗ B₁) ∧ (A₁ ⫗ B₂ ∧ A₂ ⫗ B₂) := by
  rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]

lemma union_disjoint_union {A₁ A₂ B₁ B₂ : Set α} (hAABB : (A₁ ⫗ B₁ ∧ A₂ ⫗ B₁) ∧ (A₁ ⫗ B₂ ∧ A₂ ⫗ B₂)) :
    (A₁ ∪ A₂) ⫗ (B₁ ∪ B₂) := by
  rwa [union_disjoint_union_iff]

lemma Subtype.subst_elem {X Y : Set α} (x : X) (hXY : X = Y) : (hXY ▸ x).val = x.val := by
  aesop

lemma eq_toFinset_of_toSet_eq {s : Finset α} {S : Set α} [Fintype S] (hsS : s.toSet = S) : s = S.toFinset := by
  aesop

def HasSubset.Subset.equiv {A B : Set α} [∀ i, Decidable (i ∈ A)] (hAB : A ⊆ B) : A.Elem ⊕ (B \ A).Elem ≃ B.Elem :=
  ⟨(·.casesOn hAB.elem Set.diff_subset.elem),
  fun i => if hiA : i.val ∈ A then ◩⟨i.val, hiA⟩ else ◪⟨i.val, by simp [hiA]⟩,
  fun _ => by aesop,
  fun _ => by aesop⟩

variable {β : Type*}

lemma ofSupportFinite_support_eq [Zero β] {f : α → β} {S : Set α} (hS : Finite S) (hfS : f.support = S) :
    (Finsupp.ofSupportFinite f (hfS ▸ hS)).support = S := by
  aesop

lemma finset_of_cardinality_between [Fintype α] [Fintype β] {n : ℕ}
    (hα : #α < n) (hn : n ≤ #α + #β) :
    ∃ b : Finset β, #(α ⊕ b) = n ∧ Nonempty b := by
  have hβ : n - #α ≤ #β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - #α := (Finset.exists_subset_card_eq hβ).imp (by simp)
  use s
  constructor
  · rw [Fintype.card_sum, Fintype.card_coe, hs]
    omega
  · by_contra hs'
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at hs'
      exact Finset.eq_empty_of_forall_not_mem hs'
    omega
