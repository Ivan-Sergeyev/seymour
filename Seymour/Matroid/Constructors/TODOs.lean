import Seymour.Basic.Sets
import Seymour.Matrix.Basic

open scoped Matrix Set.Notation

variable {α R : Type}

lemma in_submoduleSpan_range {O : Type} [Semiring R] [AddCommMonoid O] [Module R O] (f : α → O) (a : α) :
    f a ∈ Submodule.span R f.range := by
  apply SetLike.mem_of_subset
  · apply Submodule.subset_span
  · simp

variable [Field R] {X Y G I : Set α} {A : Matrix X Y R}

lemma todo_left_aux {hIX : I ⊆ X} (B : Basis G R (Submodule.span R A.range)) (hAI : LinearIndepOn R A hIX.elem.range) :
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

lemma todo_right_aux {hIX : I ⊆ X} (B : Basis G R (Submodule.span R A.range))
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

variable [DecidableEq α] [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)]

lemma todo_left {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
        ∘ Subtype.toSum)
      hIGX.elem.range := by
  have hX : G ∪ (X \ G) = X := Set.union_diff_cancel' (by tauto) hGX
  let e : hIGX.elem.range → hIX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert (todo_left_aux B hAI).comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · simp_rw [hij]
        simp only [hij, if_true] at hBij
        convert hBij
        ext
        apply hB
    else
      convert Eq.refl (0 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · convert hBij
        · ext
          apply hB
        · symm
          simpa using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [Matrix.submatrix, Subtype.toSum, hiX, hiG, e]

lemma todo_right {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hBI : LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
        ∘ Subtype.toSum) hIGX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  apply todo_right_aux B
  have hX : X = G ∪ (X \ G) := (Set.union_diff_cancel' (by tauto) hGX).symm
  let e : hIX.elem.range → hIGX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert hBI.comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, hhi⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simp [*]
      · simp [Matrix.submatrix, Subtype.toSum, e, hiG]
        simpa [Matrix.one_apply] using hij
    else
      convert Eq.refl (0 : R)
      · simp [*]
      · simp [Matrix.submatrix, Subtype.toSum, e, hiG]
        simpa [Matrix.one_apply] using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [Matrix.submatrix, Subtype.toSum, hiX, hiG, e]
