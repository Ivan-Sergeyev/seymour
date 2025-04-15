import Seymour.Basic.Sets
import Seymour.Matrix.Basic

open scoped Matrix Set.Notation

variable {α R : Type}

lemma in_submoduleSpan_range {O : Type} [Semiring R] [AddCommMonoid O] [Module R O] (f : α → O) (a : α) :
    f a ∈ Submodule.span R f.range := by
  apply SetLike.mem_of_subset
  · apply Submodule.subset_span
  · simp

variable [DecidableEq α] [Field R] {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)] {A : Matrix X Y R}

-- Potential lemmas to use in the following proofs:
-- LinearMap.linearIndependent_iff_of_disjoint
-- LinearIndependent.of_comp
-- LinearIndepOn.of_comp
-- LinearMap.linearIndependent_iff_of_injOn
-- LinearIndependent.linearCombinationEquiv

lemma todo_left_aux (hA : LinearIndepOn R A (X ↓∩ G)) (B : Basis G R (Submodule.span R A.range))
    (hGX : G ⊆ X) (hIX : I ⊆ X) (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R (Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)) hIX.elem.range := by
  sorry

lemma todo_left (hA : LinearIndepOn R A (X ↓∩ G)) (B : Basis G R (Submodule.span R A.range))
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
       ∘ Subtype.toSum)
      hIGX.elem.range := by
  have intermediate_step := todo_left_aux hA B hGX hIX hAI
  sorry

lemma todo_right (hA : LinearIndepOn R A (X ↓∩ G)) (B : Basis G R (Submodule.span R A.range))
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hBI : LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
       ∘ Subtype.toSum) hIGX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  sorry
