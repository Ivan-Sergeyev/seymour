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

set_option maxHeartbeats 0

/-- A non-maximal independent set of columns can be augmented with another independent column. -/
theorem VectorMatroid.indepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  by_contra! non_aug
  rw [Maximal] at hMI'
  push_neg at hMI'
  obtain ⟨hI, I_indep⟩ := hMI
  obtain ⟨⟨hJ, J_indep⟩, hJ'⟩ := hMJ
  obtain ⟨K, ⟨hMK, IK, nKI⟩⟩ := hMI' ⟨hI, I_indep⟩
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
      rw [IndepCols] at hMxI
      push_neg at hMxI
      have hnMxI : ¬LinearIndepOn R M.Aᵀ (M.Y ↓∩ (↑x ᕃ I)) := hMxI (Set.insert_subset (hJ hxJ) hI)
      have YxI : M.Y ↓∩ (↑x ᕃ I) = x ᕃ I' := by aesop
      rw [YxI] at hnMxI
      have hI_indep : LinearIndepOn R M.Aᵀ I' := I_indep
      by_contra! hv_ni_I
      have hv_ni_Iv : v ∉ Submodule.span R Iᵥ := hv_ni_I
      have hx_ni_I : x ∉ I' := x_ni_I
      have hMx_ni_Is : M.Aᵀ x ∉ Submodule.span R (M.Aᵀ '' I') := by aesop
      have hxI_indep : LinearIndepOn R M.Aᵀ (x ᕃ I') := by
        sorry
        -- exact (linearIndepOn_insert hx_ni_I).mpr ⟨hI_indep, hMx_ni_Is⟩
      contradiction
  have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  · intro v ⟨x, hxI, hxv⟩
    by_contra! hv_ni_Jₛ
    have hMx_ni_J' : M.Aᵀ x ∉ Submodule.span R (M.Aᵀ '' J') := Eq.mpr_not (congrArg (Membership.mem (Submodule.span R Jᵥ)) hxv) hv_ni_Jₛ
    have hx_ni_J' : x ∉ J' := by
      by_contra! hx_in_J'
      have hMx_in_MJ' : M.Aᵀ x ∈ (M.Aᵀ '' J') := Set.mem_image_of_mem M.Aᵀ hx_in_J'
      have hv_in_MJ' : v ∈ (M.Aᵀ '' J') := Set.mem_of_eq_of_mem (id (Eq.symm hxv)) hMx_in_MJ'
      have _ : v ∈ ↑Jₛ := Submodule.mem_span.← fun p a => a hv_in_MJ'
      contradiction
    have hJ'_indep : LinearIndepOn R M.Aᵀ J' := J_indep
    have hxJ'_indep : LinearIndepOn R M.Aᵀ (x ᕃ J') := by
      sorry
      -- exact (linearIndepOn_insert hx_ni_J').mpr ⟨hJ'_indep, hMx_ni_J'⟩
    have hMxJ_indep : M.IndepCols (↑x ᕃ J) := by
      rw [IndepCols]
      constructor
      · exact Set.insert_subset (hI hxI) hJ
      · have hxJ' : M.Y ↓∩ (↑x ᕃ J) = x ᕃ J' := by aesop
        rw [hxJ']
        exact hxJ'_indep
    apply hJ' at hMxJ_indep
    have hxJ_in_J : ↑x ᕃ J ≤ J := by aesop
    have _ : x ∈ J' := hxJ_in_J (Set.mem_insert (↑x) J)
    contradiction
  have Iₛ_eq_Jₛ : Iₛ = Jₛ := Submodule.span_eq_span Iᵥ_ss_Jₛ Jᵥ_ss_Iₛ
  obtain ⟨k, ⟨k_in_K, k_ni_I⟩⟩ := Set.not_subset.→ nKI
  have kI_in_K : (k ᕃ I) ⊆ K := Set.insert_subset k_in_K IK
  have MkI_indep : M.IndepCols (k ᕃ I) := M.indepCols_subset (k ᕃ I) K hMK kI_in_K
  have kI_in_MY : k ᕃ I ⊆ M.Y := MkI_indep.left
  have k_in_MY : k ∈ M.Y := kI_in_MY (Set.mem_insert k I)
  let k' : ↑M.Y := ⟨k, k_in_MY⟩
  by_cases hk'_in_J' : k' ∈ J'
  · have hk_in_JI : k ∈ J \ I := Set.mem_diff_of_mem hk'_in_J' k_ni_I
    exact non_aug k hk_in_JI MkI_indep
  . have hkI' : M.Y ↓∩ (k ᕃ I) = ↑k' ᕃ I' := by aesop
    have k'_ni_I' : k' ∉ I' := k_ni_I
    rw [IndepCols, hkI'] at MkI_indep
    obtain ⟨_, MkI_indep⟩ := MkI_indep
    have hMk'_ni_I'_span : M.Aᵀ k' ∉ Submodule.span R (M.Aᵀ '' I') := by
      sorry
      -- exact ((linearIndepOn_insert k'_ni_I').mp MkI_indep).right
    have hMk'_ni_J'_span : M.Aᵀ k' ∉ Submodule.span R (M.Aᵀ '' J') := by
      have I'_span_eq_J'_span : Submodule.span R (M.Aᵀ '' I') = Submodule.span R (M.Aᵀ '' J') := Iₛ_eq_Jₛ
      rw [← I'_span_eq_J'_span]
      exact hMk'_ni_I'_span
    have J'_indep : LinearIndepOn R M.Aᵀ J' := J_indep
    have hkJ'_indep : LinearIndepOn R M.Aᵀ (k' ᕃ J') := by
      sorry
      -- exact (linearIndepOn_insert hk'_in_J').mpr ⟨J'_indep, hMk'_ni_J'_span⟩
    have hMI_kJ : M.IndepCols (k ᕃ J) := by
      rw [IndepCols]
      constructor
      · exact Set.insert_subset k_in_MY hJ
      · have hkJ' : M.Y ↓∩ (k ᕃ J) = k' ᕃ J' := by aesop
        rw [hkJ']
        exact hkJ'_indep
    apply hJ' at hMI_kJ
    have hkJ_in_J : k ᕃ J ≤ J := by aesop
    have hk_in_J : k ∈ J := hkJ_in_J (Set.mem_insert k J)
    contradiction

lemma linearIndepOn_sUnion_of_directedOn {X Y : Set α} {A : Matrix Y X R} {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (hA : ∀ a ∈ s, LinearIndepOn R A (Y ↓∩ a)) :
    LinearIndepOn R A (Y ↓∩ (⋃₀ s)) := by
  let s' : Set (Set Y.Elem) := (fun t : s => Y ↓∩ t).range
  have hss' : Y ↓∩ ⋃₀ s = s'.sUnion := by aesop
  rw [hss']
  apply linearIndepOn_sUnion_of_directed
  · intro x' hx' y' hy'
    obtain ⟨x, hxs, hxM⟩ : ∃ x ∈ s, x' = Y ↓∩ x := by aesop
    obtain ⟨y, hys, hyM⟩ : ∃ y ∈ s, y' = Y ↓∩ y := by aesop
    obtain ⟨z, _, hz⟩ := hs x hxs y hys
    exact ⟨Y ↓∩ z, by aesop, hxM ▸ Set.preimage_mono hz.left, hyM ▸ Set.preimage_mono hz.right⟩
  · aesop

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.indepCols_maximal (M : VectorMatroid α R) (I : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols I :=
  fun J hMJ hJI =>
    zorn_subset_nonempty
      { K : Set α | M.IndepCols K ∧ K ⊆ I }
      (fun c hcS chain_c _ =>
        ⟨⋃₀ c,
        ⟨⟨Set.sUnion_subset (fun _ hxc => (hcS hxc).left.left),
          linearIndepOn_sUnion_of_directedOn chain_c.directedOn (fun _ hxc => (hcS hxc).left.right)⟩,
          Set.sUnion_subset (fun _ hxc => (hcS hxc).right)⟩,
        fun _ => Set.subset_sUnion_of_mem⟩)
      J ⟨hMJ, hJI⟩

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
