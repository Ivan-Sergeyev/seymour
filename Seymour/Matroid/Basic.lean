import Mathlib.Data.Matroid.Basic
import Seymour.Basic.Basic

/-!
# Basic stuff about matroids

This file provides lemmas about matroids that are not present in Mathlib.
-/

variable {α : Type*} {M : Matroid α} {G I : Set α}

lemma Matroid.IsBase.not_ssubset_indep (hMG : M.IsBase G) (hMI : M.Indep I) : ¬(G ⊂ I) :=
  (M.isBase_iff_maximal_indep.→ hMG).not_ssuperset hMI

lemma Matroid.Indep.finite_of_finite_base (hMI : M.Indep I) (hMG : M.IsBase G) (hG : Finite G) :
    Finite I := by
  have ⟨_, hM, hI⟩ := hMI.exists_isBase_superset
  exact (hMG.finite_of_finite hG hM).subset hI
