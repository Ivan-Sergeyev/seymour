import Seymour.Basic.SubmoduleSpans
import Seymour.Basic.Conversions


variable {α R : Type} [DivisionRing R] {X Y G I : Set α} {A : Matrix X Y R} {hIX : I ⊆ X}

lemma auxxx_aux (B : Basis G R (Submodule.span R A.range))
    (hI : LinearIndepOn R (fun x : X => B.repr ⟨A x, in_submoduleSpan_range A x⟩) hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range :=
  let c : (G →₀ R) →ₗ[R] (G → R) := ⟨⟨Finsupp.toFun, ↓↓rfl⟩, ↓↓rfl⟩
  (c.linearIndependent_iff (LinearMap.ker_eq_bot.← DFunLike.coe_injective')).← hI

lemma auxxx (B : Basis G R (Submodule.span R A.range))
    (hI : LinearIndepOn R (B.repr.toLinearMap ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩)) hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  apply auxxx_aux
  exact hI

lemma Basis.linearIndepOn_in_submodule (B : Basis G R (Submodule.span R A.range)) (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  apply auxxx
  rw [LinearMap.linearIndepOn_iff_of_injOn]
  · exact hAI.of_comp (Submodule.span R A.range).subtype
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)

lemma auxxxo_aux (B : Basis G R (Submodule.span R A.range))
    (hI : LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range) :
    LinearIndepOn R (fun x : X => B.repr ⟨A x, in_submoduleSpan_range A x⟩) hIX.elem.range := by
  sorry

lemma auxxxo (B : Basis G R (Submodule.span R A.range))
    (hI : LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range) :
    LinearIndepOn R (B.repr.toLinearMap ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩)) hIX.elem.range := by
  apply auxxxo_aux
  exact hI

lemma Basis.linearIndepOn_of_in_submodule (B : Basis G R (Submodule.span R A.range))
    (hBI : LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  have hRB := auxxxo B hBI
  rw [LinearMap.linearIndepOn_iff_of_injOn] at hRB
  · rw [linearIndepOn_iff'] at hRB ⊢
    intro s c hs hsc
    apply hRB s c hs
    ext j
    simpa using congr_fun hsc j
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)
