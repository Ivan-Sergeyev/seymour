import Seymour.Basic.Basic


variable {α R : Type}

lemma in_submoduleSpan_range {O : Type} [Semiring R] [AddCommMonoid O] [Module R O] (f : α → O) (a : α) :
    f a ∈ Submodule.span R f.range := by
  apply SetLike.mem_of_subset
  · apply Submodule.subset_span
  · simp

-- Peter Nelson proved:
lemma span_eq_of_maximal_subset_linearIndepOn {O : Type} [DivisionRing R] [AddCommGroup O] [Module R O] {v : α → O} {s : Set α}
    (t : Set α) (hs : Maximal (fun r : Set α => r ⊆ t ∧ LinearIndepOn R v r) s) :
    Submodule.span R (v '' s) = Submodule.span R (v '' t) := by
  apply le_antisymm (Submodule.span_mono (Set.image_mono hs.prop.left))
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hs.prop.right.mem_span_iff.← (hs.mem_of_prop_insert ⟨Set.insert_subset hx hs.prop.left, ·⟩)

-- Peter Nelson proved:
lemma span_eq_top_of_maximal_linearIndepOn {O : Type} [DivisionRing R] [AddCommGroup O] [Module R O] {v : α → O} {s : Set α}
    (hs : Maximal (LinearIndepOn R v) s) :
    Submodule.span R (v '' s) = Submodule.span R v.range := by
  simp [span_eq_of_maximal_subset_linearIndepOn Set.univ (by simpa)]


variable [Ring R] {X Y G I : Set α} {A : Matrix X Y R} {hIX : I ⊆ X}

lemma Basis.linearIndepOn_in_submodule (B : Basis G R (Submodule.span R A.range)) (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  have : Finite G := sorry
  -- TODO is `Finite G` really necessary?
  show LinearIndepOn R
    ((Finsupp.linearEquivFunOnFinite R R G.Elem).toLinearMap ∘ B.repr.toLinearMap
      ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩))
    hIX.elem.range
  rw [LinearMap.linearIndepOn_iff_of_injOn, LinearMap.linearIndepOn_iff_of_injOn]
  · exact hAI.of_comp (Submodule.span R A.range).subtype
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)
  · exact (Finsupp.linearEquivFunOnFinite R R G.Elem).toEquiv.injective.injOn

lemma Basis.linearIndepOn_of_in_submodule (B : Basis G R (Submodule.span R A.range))
    (hBI : LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  have : Finite G := sorry
  -- TODO is `Finite G` really necessary?
  have hBI' :
    LinearIndepOn R
      ((Finsupp.linearEquivFunOnFinite R R G.Elem).toLinearMap ∘ B.repr.toLinearMap
       ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩))
      hIX.elem.range
  · exact hBI
  rw [LinearMap.linearIndepOn_iff_of_injOn, LinearMap.linearIndepOn_iff_of_injOn] at hBI'
  · rw [linearIndepOn_iff'] at hBI' ⊢
    intro s c hs hsc
    apply hBI' s c hs
    ext j
    simpa using congr_fun hsc j
  · exact LinearMap.injOn_of_disjoint_ker (Submodule.span_mono (hIX.elem.range.image_subset_range _)) (by simp)
  · exact (Finsupp.linearEquivFunOnFinite R R G.Elem).toEquiv.injective.injOn
