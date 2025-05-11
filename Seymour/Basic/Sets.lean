import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.SymmDiff
import Mathlib.Tactic

import Seymour.Basic.Basic

/-!
This file provides lemmas about sets that are missing in Mathlib.
-/

variable {α : Type}

lemma disjoint_of_sdiff_inter {α : Type} (X Y : Set α) : X \ (X ∩ Y) ⫗ Y \ (X ∩ Y) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff

lemma disjoint_of_sdiff_singleton {α : Type} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) :
    X \ {a} ⫗ Y \ {a} :=
  ha ▸ disjoint_of_sdiff_inter X Y

lemma right_eq_right_of_union_eq_union {A₁ A₂ B₁ B₂ : Set α}
    (hA : A₁ = A₂) (hB₁ : A₁ ⫗ B₁) (hB₂ : A₂ ⫗ B₂) (hAB : A₁ ∪ B₁ = A₂ ∪ B₂) :
    B₁ = B₂ := by
  tauto_set
