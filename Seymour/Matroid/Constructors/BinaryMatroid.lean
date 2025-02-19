import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Map
import Mathlib.Data.Matroid.Sum

import Seymour.Basic

open scoped Matrix


/-- Data representing a vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (α R : Type) where
  /-- Row indices. -/
  X : Set α
  /-- Col indices. -/
  Y : Set α
  /-- Full representation matrix. -/
  A : Matrix X Y R


variable {α R : Type} [Semiring R]

/-- A set `S` is independent in `M[A]` iff
    `S ⊆ Y` and `S` corresponds to a linearly independent submultiset of columns in `A`. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (I : Set α) : Prop :=
  ∃ hI : I ⊆ M.Y, LinearIndependent R (fun i : I => (M.A · (hI.elem i)))

def VectorMatroid.IndepColsOn (M : VectorMatroid α R) (I : Set α) : Prop :=
  I ⊆ M.Y ∧ LinearIndepOn R M.Aᵀ (·.val ∈ I)

lemma VectorMatroid.indepColsOn_iff_indepCols (M : VectorMatroid α R) (I : Set α) :
    M.IndepColsOn I ↔ M.IndepCols I := by
  constructor <;> intro ⟨hI, hAI⟩
  · use hI
    simp [LinearIndepOn/-, Matrix.transpose-/] at hAI
    #check linearIndependent_iff_finset_linearIndependent
    #check LinearIndependent.map_of_injective_injectiveₛ
    #check LinearIndependent.comp
    #check LinearIndependent.of_comp
    #check linearIndependent_subtype_range
    --apply LinearIndependent.of_comp (M' := M.X → R)
    --let f : (M.X.Elem → R) →ₗ[R] (M.X.Elem → R) := LinearMap.funLeft R R id
    --apply LinearIndependent.of_comp f
    #check LinearIndependent.map_injOn
    #check linearIndependent_image
    --rw [linearIndependent_image] at hAI
    sorry
  · simp [VectorMatroid.IndepColsOn, LinearIndepOn]
    use hI
    show LinearIndependent R fun (v : Set.Elem (fun y : M.Y => y.val ∈ I)) => M.Aᵀ v.val
    show LinearIndependent R ((fun (j : M.Y) => M.Aᵀ j) ∘ (fun v : Set.Elem (fun y : M.Y => y.val ∈ I) => ⟨v.val, hI (v.property)⟩))
    apply LinearIndependent.comp
    · sorry
    exact Subtype.val_injective

private def VectorMatroid.IndepRows (M : VectorMatroid α R) (I : Set α) : Prop :=
  ∃ hI : I ⊆ M.X, LinearIndependent R (fun i : I => (M.A (hI.elem i)))

private def VectorMatroid.IndepRowsOn (M : VectorMatroid α R) (I : Set α) : Prop :=
  I ⊆ M.X ∧ LinearIndepOn R M.A (·.val ∈ I)

private lemma VectorMatroid.indepRowsOn_iff_indepRows (M : VectorMatroid α R) (I : Set α) :
    M.IndepRowsOn I ↔ M.IndepRows I := by
  unfold VectorMatroid.IndepRows VectorMatroid.IndepRowsOn LinearIndepOn
  constructor <;> intro ⟨hI, hAI⟩ <;> use hI
  · rw [linearIndependent_iff_finset_linearIndependent] at hAI ⊢
    intro s
    specialize hAI (s.map (⟨fun i => ⟨hI.elem i, by simp [HasSubset.Subset.elem]; aesop⟩,
        fun x y hxy => by simp [HasSubset.Subset.elem] at hxy; exact SetCoe.ext hxy⟩))
    apply LinearIndependent.comp
    · apply LinearIndependent.comp
      · sorry
      exact HasSubset.Subset.elem_injective hI
    exact Subtype.val_injective
  · sorry

lemma VectorMatroid.indepCols_iff_submatrix (M : VectorMatroid α R) (I : Set α) :
    M.IndepCols I ↔ ∃ hI : I ⊆ M.Y, LinearIndependent R (M.A.submatrix id (hI.elem))ᵀ := by
  rfl

/-- Empty set is independent. -/
theorem VectorMatroid.indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ :=
  ⟨M.Y.empty_subset, linearIndependent_empty_type⟩

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.indepCols_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) :
    M.IndepCols I :=
  have ⟨hJ, hM⟩ := hMJ
  ⟨hIJ.trans hJ, hM.comp hIJ.elem hIJ.elem_injective⟩

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.indepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  by_contra! non_aug
  rw [Maximal] at hMI'
  push_neg at hMI'
  obtain ⟨hI, I_indep⟩ := hMI
  obtain ⟨⟨hJ, J_indep⟩, hJ'⟩ := hMJ
  let I' : Set M.Y := { x : M.Y.Elem | x.val ∈ I }
  let J' : Set M.Y := { x : M.Y.Elem | x.val ∈ J }
  let Iᵥ : Set (M.X → R) := M.Aᵀ '' I'
  let Jᵥ : Set (M.X → R) := M.Aᵀ '' J'
  let Iₛ : Submodule R (M.X → R) := Submodule.span R Iᵥ
  let Jₛ : Submodule R (M.X → R) := Submodule.span R Jᵥ
  have Jᵥ_ss_Iₛ : Jᵥ ⊆ Iₛ
  · intro v ⟨x, hxJ, hxv⟩
    by_cases hvI : v ∈ Iᵥ
    · aesop
    · have x_in_J : ↑x ∈ J := hxJ
      have x_ni_I : ↑x ∉ I := by aesop
      have x_in_JwoI : ↑x ∈ J \ I := Set.mem_diff_of_mem x_in_J x_ni_I
      have hMxI : ¬M.IndepCols (↑x ᕃ I) := non_aug ↑x x_in_JwoI
      sorry
  have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  · intro v ⟨x, hxI, hxv⟩
    have hMxJ : M.IndepCols (↑x ᕃ J)
    · have hxJ : (↑x ᕃ J) ⊆ M.Y := Set.insert_subset (hI hxI) hJ
      have hvJ : (M.A.submatrix id hxJ.elem)ᵀ '' Set.univ = v ᕃ Jᵥ
      · sorry
      sorry
    have v_in_Jᵥ : v ∈ Jᵥ := by aesop
    exact Set.mem_of_mem_of_subset v_in_Jᵥ Submodule.subset_span
  have Jₛ_le_Iₛ : Jₛ ≤ Iₛ := Submodule.span_le.← Jᵥ_ss_Iₛ
  have Iₛ_le_Jₛ : Iₛ ≤ Jₛ := Submodule.span_le.← Iᵥ_ss_Jₛ
  have Iₛ_eq_Jₛ : Iₛ = Jₛ := Submodule.span_eq_span Iᵥ_ss_Jₛ Jᵥ_ss_Iₛ
  clear Jᵥ_ss_Iₛ Iᵥ_ss_Jₛ Jₛ_le_Iₛ Iₛ_le_Jₛ
  sorry

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.indepCols_maximal (M : VectorMatroid α R) (I : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols I := by
  sorry

/-- `VectorMatroid` expressed as `IndepMatroid`. -/
def VectorMatroid.toIndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.Y
  Indep := M.IndepCols
  indep_empty := M.indepCols_empty
  indep_subset := M.indepCols_subset
  indep_aug := M.indepCols_aug
  indep_maximal S _ := M.indepCols_maximal S
  subset_ground _ := Exists.choose

/-- `VectorMatroid` converted to `Matroid`. -/
def VectorMatroid.toMatroid (M : VectorMatroid α R) : Matroid α :=
  M.toIndepMatroid.matroid

@[simp]
lemma VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = M.Y :=
  rfl

@[simp]
lemma VectorMatroid.toMatroid_indep (M : VectorMatroid α R) : M.toMatroid.Indep = M.IndepCols :=
  rfl


-- todo: section 2.2/6.3 from Oxley: Different matroid representations
-- the following operations on `A` do not change `M[A]`:
-- 2.2.1 Interchange two rows.  <-- can be generalized for free to reindexing of rows
-- 2.2.2 Multiply a row by non-zero.
-- 2.2.3 Replace a row by the sum of that row and another.
-- 2.2.4 Adjoin or remove a zero row.
-- 2.2.5 Interchange two columns (the labels moving with the columns).  <-- trivial in lean: indices are labeled and unordered
-- 2.2.6 Multiply a column by a non-zero member of F.
-- 2.2.7 Replace each matrix entry by its image under some automorphism of F.

-- todo: if A is non-zero, it can be reduced to `[1 | B]` by a sequence of operations of types 2.2.1--2.2.5
