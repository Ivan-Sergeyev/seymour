import Seymour.Basic.Sets
import Seymour.Matrix.Basic

open scoped Matrix Set.Notation

variable {α R : Type}

lemma in_submoduleSpan_range {O : Type} [Semiring R] [AddCommMonoid O] [Module R O] (f : α → O) (a : α) :
    f a ∈ Submodule.span R f.range := by
  apply SetLike.mem_of_subset
  · apply Submodule.subset_span
  · simp

lemma todo_left_aux_aux' {O : Type} [Field R] [AddCommMonoid O] [Module R O] {f : α → O} {G I : Set α}
    (hf : LinearIndepOn R f G) {B : Basis G R (Submodule.span R f.range)}
    (hB : ∀ a g : G, ∀ haR : f a ∈ Submodule.span R f.range, B.repr ⟨f a, haR⟩ g = B.repr (B a) g)
    (hAI : LinearIndepOn R f I) :
    LinearIndepOn R (fun a : α => B.repr ⟨f a, in_submoduleSpan_range f a⟩) I := by
  sorry

lemma todo_left_aux_aux {O : Type} [Field R] [AddCommMonoid O] [Module R O] {f : α → O} {G I : Set α}
    (hf : LinearIndepOn R f G) {B : Basis G R (Submodule.span R f.range)}
    (hB : ∀ a : α, ∀ g : G, ∀ haG : a ∈ G, ∀ haR : f a ∈ Submodule.span R f.range, B.repr ⟨f a, haR⟩ g = B.repr (B ⟨a, haG⟩) g)
    (hAI : LinearIndepOn R f I) :
    LinearIndepOn R (fun a : α => B.repr ⟨f a, in_submoduleSpan_range f a⟩) I := by
  sorry

variable [DecidableEq α] [Field R] {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)] {A : Matrix X Y R}

-- Potentially useful lemmas for the following proofs:
-- LinearMap.linearIndependent_iff_of_disjoint
-- LinearIndependent.of_comp
-- LinearIndepOn.of_comp
-- LinearMap.linearIndependent_iff_of_injOn
-- LinearIndependent.linearCombinationEquiv

lemma todo_left_aux (hA : LinearIndepOn R A (X ↓∩ G)) {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hIX : I ⊆ X)
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g) hIX.elem.range := by
  have hB' :
    ∀ x : X, ∀ g : G, ∀ hxG : x.val ∈ G, ∀ hxR : A x ∈ Submodule.span R A.range,
      B.repr ⟨(A x), hxR⟩ g = B.repr (B ⟨x, hxG⟩) g
  · intros
    apply hB
  have hB'' :
    ∀ x : G, ∀ g : G, ∀ hxR : A (hGX.elem x) ∈ Submodule.span R A.range,
      B.repr ⟨A (hGX.elem x), hxR⟩ g = B.repr (B x) g
  · intros
    apply hB'
  show LinearIndepOn R (fun x : X => (B.repr ⟨A x, in_submoduleSpan_range A x⟩).toFun) hIX.elem.range
  sorry
  -- simp only [Basis.repr_self_apply] at hB''
  -- apply LinearIndepOn.of_comp (M' := Y → R)
  -- convert hAI
  -- ext ⟨i, hi⟩ ⟨j, hj⟩
  -- rw [Function.comp_apply]
  -- sorry
  -- sorry

lemma todo_left (hA : LinearIndepOn R A (X ↓∩ G)) {B : Basis G R (Submodule.span R A.range)}
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
  convert (todo_left_aux hA hGX hIX hB hAI).comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  have hiX : i ∈ X := hX ▸ hi
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
    simp [Matrix.submatrix, Subtype.toSum, hiX, hiG, e]

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
