import Seymour.Basic.SubmoduleSpans
import Seymour.Basic.Conversions

/-!
# Submodule Basis

This file provides auxilliary lemmas for proving `Matrix.exists_standardRepr_isBase` via the subspace generated by a matrix.
-/

variable {α R : Type*} [Ring R] {X Y G I : Set α} {A : Matrix X Y R} {hIX : I ⊆ X}

private lemma Basis.linearIndepOn_in_submodule_aux (B : Basis G R (Submodule.span R A.range)) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range ↔
    LinearIndepOn R (B.repr.toLinearMap ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩)) hIX.elem.range :=
  let c : (G →₀ R) →ₗ[R] (G → R) := ⟨⟨Finsupp.toFun, ↓↓rfl⟩, ↓↓rfl⟩
  ⟨fun hI => (linearIndependent_iff.← ↓(hI ·)).of_comp c,
    (c.linearIndependent_iff (LinearMap.ker_eq_bot.← DFunLike.coe_injective')).←⟩

lemma Basis.linearIndepOn_in_submodule (B : Basis G R (Submodule.span R A.range)) (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  rw [B.linearIndepOn_in_submodule_aux]
  rw [LinearMap.linearIndepOn_iff_of_injOn]
  · exact hAI.of_comp (Submodule.span R A.range).subtype
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)

lemma Basis.linearIndepOn_of_in_submodule (B : Basis G R (Submodule.span R A.range))
    (hBI : LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  rw [B.linearIndepOn_in_submodule_aux, LinearMap.linearIndepOn_iff_of_injOn] at hBI
  · rw [linearIndepOn_iff'] at hBI ⊢
    intro s c hs hsc
    apply hBI s c hs
    ext j
    simpa using congr_fun hsc j
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)
