import Seymour.Basic.Basic

/-!
# Submodule Spans

This file provides lemmas about the linear spans of vector sets that are not present in Mathlib.
-/

variable {α R O : Type*} [DivisionRing R] [AddCommGroup O] [Module R O] {v : α → O} {s : Set α}

lemma span_eq_of_maximal_subset_linearIndepOn (t : Set α) (hs : Maximal (fun r : Set α => r ⊆ t ∧ LinearIndepOn R v r) s) :
    Submodule.span R (v '' s) = Submodule.span R (v '' t) := by
  apply le_antisymm (Submodule.span_mono (Set.image_mono hs.prop.left))
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hs.prop.right.mem_span_iff.← (hs.mem_of_prop_insert ⟨Set.insert_subset hx hs.prop.left, ·⟩)

lemma span_eq_top_of_maximal_linearIndepOn (hs : Maximal (LinearIndepOn R v) s) :
    Submodule.span R (v '' s) = Submodule.span R v.range := by
  simp [span_eq_of_maximal_subset_linearIndepOn Set.univ (by simpa)]
