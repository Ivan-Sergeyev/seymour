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

lemma todo_left_aux (B : Basis G R (Submodule.span R A.range)) (hIX : I ⊆ X)
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  have almost :
    LinearIndepOn R
      (B.repr.toLinearMap ∘ (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩))
      hIX.elem.range
  · rw [LinearMap.linearIndepOn_iff_of_injOn]
    · exact hAI.of_comp (Submodule.span R A.range).subtype
    apply LinearMap.injOn_of_disjoint_ker
      (Submodule.span_mono
        (Set.image_subset_range (fun x : X => (⟨A x, in_submoduleSpan_range A x⟩ : Submodule.span R A.range)) hIX.elem.range))
    simp
  have : Finite G := sorry -- hopefully not needed in the end
  show LinearIndepOn R
    ((Finsupp.linearEquivFunOnFinite R R G.Elem).toLinearMap ∘ B.repr.toLinearMap ∘
      (fun x : X => ⟨A x, in_submoduleSpan_range A x⟩))
    hIX.elem.range
  rw [LinearMap.linearIndepOn_iff_of_injOn]
  · exact almost
  · exact Function.Injective.injOn (Equiv.injective (Finsupp.linearEquivFunOnFinite R R G).toEquiv)

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
  unfold LinearIndepOn -- `convert` doesn't see through definitional equalities
  convert (todo_left_aux B hIX hAI).comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, -⟩
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

-- Potentially useful lemmas:
-- LinearMap.linearIndependent_iff_of_disjoint
-- LinearIndependent.of_comp
-- LinearIndepOn.of_comp
-- LinearMap.linearIndependent_iff_of_injOn
-- LinearIndependent.linearCombinationEquiv

lemma todo_right (hA : LinearIndepOn R A (X ↓∩ G)) {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hBI : LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
       ∘ Subtype.toSum) hIGX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  sorry
