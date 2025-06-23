import Mathlib.Data.Matroid.Basic
import Seymour.Basic.Basic

/-!
# Matroid Basics

This file provides basuc lemmas about matroids that are not present in Mathlib.
-/

lemma Matroid.IsBase.not_ssubset_indep {α : Type} {M : Matroid α} {G I : Set α} (hMG : M.IsBase G) (hMH : M.Indep I) :
    ¬(G ⊂ I) :=
  (M.isBase_iff_maximal_indep.→ hMG).not_ssuperset hMH
