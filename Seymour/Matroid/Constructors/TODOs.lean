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

-- Potential lemmas to use in the following two proofs:
-- LinearMap.linearIndependent_iff_of_disjoint
-- LinearIndependent.of_comp
-- LinearIndepOn.of_comp
-- LinearMap.linearIndependent_iff_of_injOn
-- LinearIndependent.linearCombinationEquiv

lemma todo_left (hA : LinearIndepOn R A (X ↓∩ G)) (B : Basis G R (Submodule.span R A.range))
    (hGX : G ⊆ X)
    (hXGX : X \ G ⊆ X) -- redundant but keep
    (hI : I ⊆ X)
    (hI' : I ⊆ (G ∪ X \ G)) -- redundant but keep
    (hAI : LinearIndepOn R A hI.elem.range) :
    LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
       ∘ Subtype.toSum) hI'.elem.range
     := by
  sorry

lemma todo_right (hA : LinearIndepOn R A (X ↓∩ G)) (B : Basis G R (Submodule.span R A.range))
    (hGX : G ⊆ X)
    (hXGX : X \ G ⊆ X) -- redundant but keep
    (hGXX : G ∪ X = X) -- redundant but keep
    (hI : I ⊆ G ∪ X)
    (hBI : LinearIndepOn R
      (((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id).uppendId
       ∘ Subtype.toSum)
      ((Iff.of_eq (congr_arg (I ⊆ ·) Set.union_diff_self)).← hI).elem.range) :
    LinearIndepOn R A (hGXX ▸ hI).elem.range := by
  sorry

-- lemma todo_right' [Field R] {X G I : Set α} {O : Type} [AddCommMonoid O] [Module R O]
--     [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)] {A : X → O}
--     (lin_indep : LinearIndepOn R A (X ↓∩ G))
--     (B : Basis G R (Submodule.span R A.range))
--     (hGX : G ⊆ X)
--     (hXGX : X \ G ⊆ X) -- redundant but keep
--     (hGXX : G ∪ X = X) -- redundant but keep
--     (hI : I ⊆ G ∪ X)
--     (hBI : LinearIndepOn R
--       (((Matrix.of (fun x : X => fun g : G => B.coord g ⟨A x, in_submoduleSpan_range A x⟩)).submatrix hXGX.elem id).uppendId
--        ∘ Subtype.toSum)
--       ((Iff.of_eq (congr_arg (I ⊆ ·) Set.union_diff_self)).← hI).elem.range) :
--     LinearIndepOn R A (hGXX ▸ hI).elem.range := by
--   sorry
