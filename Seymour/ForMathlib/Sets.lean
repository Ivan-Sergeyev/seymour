import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic

/-!
This provides lemmas about sets (mostly dealing with disjointness) that are missing in Mathlib.
We do not use out custom notation here because this file is higher than `Basic.lean` in the import hierarchy.
-/

variable {α : Type*} {X Y : Set α}

lemma setminus_inter_union_eq_union : X \ (X ∩ Y) ∪ Y = X ∪ Y := by
  ext a
  constructor
  · intro ha
    cases ha with
    | inl ha' =>
      left
      exact Set.mem_of_mem_diff ha'
    | inr haY =>
      right
      exact haY
  · simp

variable {a : α}

lemma disjoint_of_singleton_intersection_left_wo (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) Y := by
  rw [Set.disjoint_iff_forall_ne]
  intro u huXa v hvY huv
  have hua : u ≠ a
  · aesop
  have huX : u ∈ X
  · aesop
  have huXY := Set.mem_inter huX (huv ▸ hvY)
  rw [hXY, Set.mem_singleton_iff] at huXY
  exact hua huXY

lemma disjoint_of_singleton_intersection_right_wo (hXY : X ∩ Y = {a}) : Disjoint X (Y \ {a}) := by
  rw [disjoint_comm]
  rw [Set.inter_comm] at hXY
  exact disjoint_of_singleton_intersection_left_wo hXY

lemma disjoint_of_singleton_intersection_both_wo (hXY : X ∩ Y = {a}) : Disjoint (X \ {a}) (Y \ {a}) :=
  Disjoint.disjoint_sdiff_left (disjoint_of_singleton_intersection_right_wo hXY)
