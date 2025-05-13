import Seymour.Basic.Basic

/-!
This file provides lemmas about sets that are not present in Mathlib.
-/

variable {α : Type}

lemma disjoint_of_sdiff_inter (X Y : Set α) : X \ (X ∩ Y) ⫗ Y \ (X ∩ Y) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff

lemma disjoint_of_sdiff_singleton {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) :
    X \ {a} ⫗ Y \ {a} :=
  ha ▸ disjoint_of_sdiff_inter X Y

lemma right_eq_right_of_union_eq_union {A₁ A₂ B₁ B₂ : Set α}
    (hA : A₁ = A₂) (hB₁ : A₁ ⫗ B₁) (hB₂ : A₂ ⫗ B₂) (hAB : A₁ ∪ B₁ = A₂ ∪ B₂) :
    B₁ = B₂ := by
  tauto_set

lemma eq_toFinset_of_toSet_eq {s : Finset α} {S : Set α} [Fintype S] (hsS : s.toSet = S) : s = S.toFinset := by
  aesop

variable {β : Type}

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
