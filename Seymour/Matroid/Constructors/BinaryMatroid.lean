import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Map
import Mathlib.Data.Matroid.Sum

import Seymour.Basic.Basic

open scoped Matrix Set.Notation


/-- Data representing a vector matroid. -/
structure VectorMatroid (α R : Type) where
  /-- Row indices. -/
  X : Set α
  /-- Col indices. -/
  Y : Set α
  /-- Full representation matrix. -/
  A : Matrix X Y R


variable {α R : Type} [Semiring R]

/-- A set is independent in a vector matroid iff it corresponds to a linearly independent submultiset of columns. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (I : Set α) : Prop :=
  I ⊆ M.Y ∧ LinearIndepOn R M.Aᵀ (M.Y ↓∩ I)

/-- Our old (equivalent) definition. -/
private def VectorMatroid.IndepColsOld (M : VectorMatroid α R) (I : Set α) : Prop :=
  ∃ hI : I ⊆ M.Y, LinearIndependent R (fun i : I => (M.A · (hI.elem i)))

private lemma VectorMatroid.indepCols_eq_indepColsOld (M : VectorMatroid α R) :
    M.IndepCols = M.IndepColsOld := by
  ext I
  constructor <;> intro ⟨hI, hAI⟩ <;> use hI <;> let e : I ≃ M.Y ↓∩ I :=
      (Equiv.ofInjective hI.elem hI.elem_injective).trans (Equiv.Set.ofEq hI.elem_range)
  · exact (linearIndependent_equiv' e (by aesop)).← hAI
  · exact (linearIndependent_equiv' e (by aesop)).→ hAI

lemma VectorMatroid.indepCols_iff_elem (M : VectorMatroid α R) (I : Set α) :
    M.IndepCols I ↔ ∃ hI : I ⊆ M.Y, LinearIndepOn R M.Aᵀ hI.elem.range := by
  unfold IndepCols HasSubset.Subset.elem
  aesop

lemma VectorMatroid.indepCols_iff_submatrix (M : VectorMatroid α R) (I : Set α) :
    M.IndepCols I ↔ ∃ hI : I ⊆ M.Y, LinearIndependent R (M.A.submatrix id hI.elem)ᵀ :=
  M.indepCols_eq_indepColsOld ▸ Iff.rfl

lemma VectorMatroid.indepCols_iff_submatrix' (M : VectorMatroid α R) (I : Set α) :
    M.IndepCols I ↔ ∃ hI : I ⊆ M.Y, LinearIndependent R (M.Aᵀ.submatrix hI.elem id) :=
  M.indepCols_eq_indepColsOld ▸ Iff.rfl


/-- Empty set is independent. -/
private theorem VectorMatroid.indepColsOld_empty (M : VectorMatroid α R) :
    M.IndepColsOld ∅ :=
  ⟨M.Y.empty_subset, linearIndependent_empty_type⟩

/-- Empty set is independent. -/
theorem VectorMatroid.indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ :=
  M.indepCols_eq_indepColsOld ▸ M.indepColsOld_empty

/-- A subset of a independent set of columns is independent. -/
private theorem VectorMatroid.indepColsOld_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepColsOld J) (hIJ : I ⊆ J) :
    M.IndepColsOld I :=
  have ⟨hJ, hM⟩ := hMJ
  ⟨hIJ.trans hJ, hM.comp hIJ.elem hIJ.elem_injective⟩

/-- A subset of a independent set of columns is independent. -/
theorem VectorMatroid.indepCols_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) :
    M.IndepCols I :=
  M.indepCols_eq_indepColsOld ▸ M.indepColsOld_subset I J (M.indepCols_eq_indepColsOld ▸ hMJ) hIJ

/-- A non-maximal independent set of columns can be augmented with another independent column. -/
private theorem VectorMatroid.indepColsOld_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepColsOld I) (hMI' : ¬Maximal M.IndepColsOld I) (hMJ : Maximal M.IndepColsOld J) :
    ∃ x ∈ J \ I, M.IndepColsOld (x ᕃ I) := by
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
      have hMxI : ¬M.IndepColsOld (↑x ᕃ I) := non_aug ↑x x_in_JwoI
      sorry
  have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  · intro v ⟨x, hxI, hxv⟩
    have hMxJ : M.IndepColsOld (↑x ᕃ J)
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

/-- A non-maximal independent set of columns can be augmented with another independent column. -/
theorem VectorMatroid.indepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) :=
  let hMM := M.indepCols_eq_indepColsOld
  hMM ▸ M.indepColsOld_aug I J (hMM ▸ hMI) (hMM ▸ hMI') (hMM ▸ hMJ)

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.indepCols_maximal (M : VectorMatroid α R) (I : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols I := by
  intros J hIndepJ hJI
  let S : Set (Set α) := {K | M.IndepCols K ∧ K ⊆ I}
  have linearIndepOn_sUnion_of_directed_in_M {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s) (h : ∀ a ∈ s, LinearIndepOn R M.Aᵀ (M.Y ↓∩ a)) : LinearIndepOn R M.Aᵀ (M.Y ↓∩ (⋃₀ s)) := by
    let s' : Set (Set ↑M.Y) := Set.range fun t : s => M.Y ↓∩ t
    have hss' : Set.sUnion s' = M.Y ↓∩ ⋃₀ s := by aesop
    rw [← hss']
    have hs' : DirectedOn (· ⊆ ·) s' := by
      intros x' hx' y' hy'
      have hx : ∃ x ∈ s, x' = M.Y ↓∩ x := by aesop
      have hy : ∃ y ∈ s, y' = M.Y ↓∩ y := by aesop
      obtain ⟨x, hx⟩ := hx
      obtain ⟨y, hy⟩ := hy
      obtain ⟨z, hz⟩ := hs x hx.left y hy.left
      use M.Y ↓∩ z
      constructor
      · aesop
      · constructor
        · rw [hx.right]
          refine Set.preimage_mono ?_
          exact hz.right.left
        · rw [hy.right]
          refine Set.preimage_mono ?_
          exact hz.right.right
    apply linearIndepOn_sUnion_of_directed hs'
    intro a' ha'
    have _ : ∃ a ∈ s, a' = M.Y ↓∩ a := by aesop
    aesop
  exact zorn_subset_nonempty S (fun c hcss hchain _ ↦ ⟨⋃₀ c, ⟨⟨Set.sUnion_subset (fun _ hxc ↦ (hcss hxc).left.left), linearIndepOn_sUnion_of_directed_in_M hchain.directedOn (fun _ hxc ↦ (hcss hxc).left.right)⟩, Set.sUnion_subset (fun _ hxc ↦ (hcss hxc).right)⟩, fun _ hs ↦ Set.subset_sUnion_of_mem hs⟩) J ⟨hIndepJ, hJI⟩

/-- `VectorMatroid` expressed as `IndepMatroid`. -/
private def VectorMatroid.toIndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.Y
  Indep := M.IndepCols
  indep_empty := M.indepCols_empty
  indep_subset := M.indepCols_subset
  indep_aug := M.indepCols_aug
  indep_maximal S _ := M.indepCols_maximal S
  subset_ground _ := And.left

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
