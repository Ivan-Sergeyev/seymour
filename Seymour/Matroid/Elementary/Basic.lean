import Mathlib.Data.Matroid.Basic
import Seymour.Basic.Basic


variable {α : Type}

lemma Matroid.base_not_ssubset_indep (M : Matroid α) {G I : Set α} (hMG : M.IsBase G) (hMH : M.Indep I) : ¬(G ⊂ I) :=
  (M.isBase_iff_maximal_indep.→ hMG).not_ssuperset hMH

lemma Matroid.base_not_ssubset_base (M : Matroid α) {G H : Set α} (hMG : M.IsBase G) (hMH : M.IsBase H) : ¬(G ⊂ H) :=
  M.base_not_ssubset_indep hMG hMH.indep
