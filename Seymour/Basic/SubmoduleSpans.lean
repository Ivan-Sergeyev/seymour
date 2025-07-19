import Seymour.Basic.Basic

/-!
# Submodule Spans

This file provides lemmas about the linear spans of vector sets that are not present in Mathlib.
-/

variable {α R O : Type*} [AddCommGroup O]

lemma in_submoduleSpan_range [Semiring R] [Module R O] (f : α → O) (a : α) :
    f a ∈ Submodule.span R f.range := by
  apply SetLike.mem_of_subset
  · apply Submodule.subset_span
  · simp

variable [DivisionRing R] [Module R O] {f : α → O} {s : Set α}

lemma span_eq_of_maximal_subset_linearIndepOn (t : Set α) (hf : Maximal (fun r : Set α => r ⊆ t ∧ LinearIndepOn R f r) s) :
    Submodule.span R (f '' s) = Submodule.span R (f '' t) := by
  apply le_antisymm (Submodule.span_mono (Set.image_mono hf.prop.left))
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hf.prop.right.mem_span_iff.← (hf.mem_of_prop_insert ⟨Set.insert_subset hx hf.prop.left, ·⟩)

lemma span_eq_top_of_maximal_linearIndepOn (hf : Maximal (LinearIndepOn R f) s) :
    Submodule.span R (f '' s) = Submodule.span R f.range := by
  simp [span_eq_of_maximal_subset_linearIndepOn Set.univ (by simpa)]
