import Mathlib.Data.Matroid.Sum
import Seymour.Basic.Basic

/-!
# Basic stuff about matroids

This file provides lemmas about matroids that are not present in Mathlib.
-/

variable {α : Type*}

/-- The sum of two matroids on disjoint ground sets of the same type is a matroid whose ground set is a union of the ground sets
    of the summands, in which a subset of said ground set is independent iff its intersections with respective ground set are
    independent in each matroid. -/
abbrev Disjoint.matroidSum {Mₗ Mᵣ : Matroid α} (hEE : Mₗ.E ⫗ Mᵣ.E) : Matroid α :=
  Matroid.disjointSum Mₗ Mᵣ hEE


variable {M : Matroid α} {G I : Set α}

lemma Matroid.IsBase.not_ssubset_indep (hMG : M.IsBase G) (hMI : M.Indep I) : ¬(G ⊂ I) :=
  (M.isBase_iff_maximal_indep.→ hMG).not_ssuperset hMI

lemma Matroid.Indep.finite_of_finite_base (hMI : M.Indep I) (hMG : M.IsBase G) (hG : Finite G) :
    Finite I := by
  have ⟨_, hM, hI⟩ := hMI.exists_isBase_superset
  exact (hMG.finite_of_finite hG hM).subset hI
