import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Map

import Seymour.Basic
import Seymour.ForMathlib.SetTheory

open scoped Matrix


section Definition

/-- Vector matroid `M[A]` of matrix `A`. -/
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

lemma VectorMatroid.indepCols_iff_submatrix (M : VectorMatroid α R) (I : Set α) :
    M.IndepCols I ↔
    ∃ hI : I ⊆ M.Y, LinearIndependent R (M.A.submatrix id (hI.elem))ᵀ := by
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

end Definition


section API

variable {α R : Type} [Semiring R]

/-- `VectorMatroid` converted to `Matroid`. -/
def VectorMatroid.toMatroid (M : VectorMatroid α R) : Matroid α :=
  M.toIndepMatroid.matroid

@[simp]
lemma VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = M.Y :=
  rfl

@[simp]
lemma VectorMatroid.toMatroid_indep (M : VectorMatroid α R) : M.toMatroid.Indep = M.IndepCols :=
  rfl

end API


section EquivalentTransformations

-- todo: section 2.2/6.3 from Oxley: Different matroid representations
-- the following operations on `A` do not change `M[A]`:
-- 2.2.1 Interchange two rows.  <-- can be generalized for free to reindexing of rows
-- 2.2.2 Multiply a row by non-zero.
-- 2.2.3 Replace a row by the sum of that row and another.
-- 2.2.4 Adjoin or remove a zero row.
-- 2.2.5 Interchange two columns (the labels moving with the columns).  <-- trivial in lean: indices are labeled and unordered
-- 2.2.6 Multiply a column by a non-zero member of F.
-- 2.2.7 Replace each matrix entry by its image under some automorphism of F.

-- todo: if A is non-zero, it can be reduced to [1 | B] by a sequence of operations of types 2.2.1--2.2.5

end EquivalentTransformations


section StandardRepr

/-- Standard matrix representation of a vector matroid. TODO finiteness? -/
structure StandardRepr (α R : Type) where
  /-- Row indices. -/
  X : Set α
  /-- Col indices. -/
  Y : Set α
  /-- Basis and nonbasis elements are disjoint -/
  hXY : X ⫗ Y
  /-- Standard representation matrix. -/
  B : Matrix X Y R
  /-- The computer can distinguish the rows from each other. -/
  deceqX : DecidableEq X
  /-- The computer can distinguish the cols from each other. -/
  deceqY : DecidableEq Y
  /-- The computer can determine whether certain element is a row. -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- The computer can determine whether certain element is a col. -/
  decmemY : ∀ a, Decidable (a ∈ Y)

attribute [instance] StandardRepr.deceqX
attribute [instance] StandardRepr.deceqY
attribute [instance] StandardRepr.decmemX
attribute [instance] StandardRepr.decmemY

variable {α R : Type} [Ring R]

/-- Vector matroid constructed from standard representation. -/
def StandardRepr.toVectorMatroid (S : StandardRepr α R) : VectorMatroid α R :=
  ⟨S.X, S.X ∪ S.Y, (S.B.prependId · ∘ Subtype.toSum)⟩

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.E = S.X ∪ S.Y :=
  rfl

/-- Full representation matrix of vector matroid is `[1 | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A (S : StandardRepr α R) :
    S.toVectorMatroid.A = (S.B.prependId · ∘ Subtype.toSum) :=
  rfl

/-- Set is independent in the vector matroid iff
    corresponding multiset of columns of `[1 | B]` is linearly independent over `R`. -/
lemma StandardRepr.toVectorMatroid_indep_iff (S : StandardRepr α R) [DecidableEq α] (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y,
      LinearIndependent R (fun i : I => (S.B.prependId · (hI.elem i).toSum)) := by
  rfl

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, M = S.toVectorMatroid := by
  sorry

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_base {B : Set α}
    (M : VectorMatroid α R) (hB : M.toMatroid.Base B) (hBY : B ⊆ M.Y) :
    ∃ S : StandardRepr α R, M.X = B ∧ M = S.toVectorMatroid := by
  sorry

/-- Construct a matroid from standard representation. -/
def StandardRepr.toMatroid (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

/-- Set is independent in the resulting matroid iff
    the corresponding multiset of columns of `[1 | B]` is linearly independent over `R`. -/
@[simp]
lemma StandardRepr.toMatroid_indep_iff (S : StandardRepr α R) [DecidableEq α] (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y,
      LinearIndependent R (fun i : I => (S.B.prependId · (hI.elem i).toSum)) := by
  rfl

lemma StandardRepr.toMatroid_indep_iff_submatrix (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem))ᵀ := by
  rfl

/-- The identity matrix has linearly independent rows. -/
lemma Matrix.one_linearIndependent [DecidableEq α] : LinearIndependent R (1 : Matrix α α R) := by
-- Riccardo Brasca proved:
  rw [linearIndependent_iff]
  intro l hl
  ext j
  simpa [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum_apply', Matrix.one_apply] using congr_fun hl j
-- TODO check if in Mathlib already

-- /-- The image of all rows of a standard representation is a base in the resulting matroid. -/
-- lemma StandardRepr.toMatroid_base [DecidableEq α] (S : StandardRepr α R) :
--     S.toMatroid.Base (S.emb '' Set.range Sum.inl) := by
--   apply Matroid.Indep.base_of_forall_insert
--   · rw [StandardRepr.toMatroid_indep_iff_submatrix]
--     use (by simp)
--     show LinearIndependent R (S.B.prependId.transpose.submatrix _ id)
--     rw [Matrix.transpose_fromCols, Matrix.transpose_one]
--     convert @Matrix.one_linearIndependent S.X R _ _
--     sorry -- defeq + simp should suffice
--   · intro e he
--     sorry --  if you add anything extra to the identity matrix, it becomes singular

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.B.transpose
  deceqX := S.deceqY
  deceqY := S.deceqX
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of standard representation gives a dual matroid. -/
lemma StandardRepr.toMatroid_dual (S : StandardRepr α R) :
    S.toMatroid✶ = S✶.toMatroid :=
  sorry -- Theorem 2.2.8 in Oxley

/-- Every vector matroid's dual has a standard representation. -/
lemma VectorMatroid.dual_exists_standardRepr (M : VectorMatroid α R) :
    ∃ S' : StandardRepr α R, M.toMatroid✶ = S'.toMatroid :=
  have ⟨S, hS⟩ := M.exists_standardRepr
  ⟨S✶, hS ▸ S.toMatroid_dual⟩

end StandardRepr


section regularity

/-- Matrix `S` is a TU signing of `U` iff `S` is TU and its entries are the same as in `U` up to signs. -/
def Matrix.IsTuSigningOf {X Y : Type} (S : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  S.IsTotallyUnimodular ∧ ∀ i j, |S i j| = (U i j).val
-- do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (A : Matrix X Y (ZMod n)) : Prop :=
  ∃ A' : Matrix X Y ℚ, A'.IsTuSigningOf A

variable {α : Type}

/-- The main definition of regularity: `M` is regular iff it is constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

lemma Matroid.IsRegular.isBinary {M : Matroid α} (hM : M.IsRegular) :
    ∃ X Y : Set α, ∃ A : Matrix X Y Z2, (VectorMatroid.mk X Y A).toMatroid = M := by
  sorry

lemma Matroid.IsRegular.isBinaryStd {M : Matroid α} (hM : M.IsRegular) :
    ∃ X Y : Set α, ∃ hXY : X ⫗ Y, ∃ A : Matrix X Y Z2,
      ∃ deqX : DecidableEq X, ∃ deqY : DecidableEq Y, ∃ dinX : (∀ a, Decidable (a ∈ X)), ∃ dinY : (∀ a, Decidable (a ∈ Y)),
        (StandardRepr.mk X Y hXY A deqX deqY dinX dinY).toMatroid = M := by
  sorry

/-- Matroid `M` that can be represented by a matrix over `Z2` with a TU signing -/
abbrev StandardRepr.HasTuSigning (S : StandardRepr α Z2) : Prop :=
  S.B.HasTuSigning

lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning [DecidableEq α] (S : StandardRepr α Z2) :
    S.toMatroid.IsRegular ↔ S.HasTuSigning := by
  sorry

end regularity

-- TODO port 1-sum

section TwoSum

variable {α : Type}

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix_2sumComposition {β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

variable [DecidableEq α]

/-- `StandardRepresentation`-level 2-sum of two matroids.
The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def StandardRepr_2sum {a : α} {M₁ M₂ : StandardRepr α Z2} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    StandardRepr α Z2 × Prop :=
  let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
  let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
  ⟨
    ⟨
      (M₁.X \ {a}) ∪ M₂.X,
      M₁.Y ∪ (M₂.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨M₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_inter_both_wo ha, M₂.hXY.disjoint_sdiff_right⟩⟩,
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
      inferInstance,
      inferInstance,
    ⟩,
    (M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is2sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  B : StandardRepr α Z2
  B₁ : StandardRepr α Z2
  B₂ : StandardRepr α Z2
  hM : B.toMatroid = M
  hM₁ : B₁.toMatroid = M₁
  hM₂ : B₂.toMatroid = M₂
  a : α
  ha : B₁.X ∩ B₂.Y = {a}
  hXY : B₂.X ⫗ B₁.Y
  is2sum : B = (StandardRepr_2sum ha hXY).fst
  isValid : (StandardRepr_2sum ha hXY).snd

lemma Matrix_2sumComposition_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) (x : Y₁ → ℚ) (y : X₂ → ℚ) :
    (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  sorry

lemma StandardRepr_2sum_B {M₁ M₂ : StandardRepr α Z2} {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    ∃ haX₁ : a ∈ M₁.X, ∃ haY₂ : a ∈ M₂.Y,
      (StandardRepr_2sum ha hXY).fst.B =
      (Matrix_2sumComposition
        (M₁.B ∘ Set.diff_subset.elem)
        (M₁.B ⟨a, haX₁⟩)
        (M₂.B · ∘ Set.diff_subset.elem)
        (M₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ M₁.X ∩ M₂.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma todo_find_home (x y : Z2) : (x.val : ℚ) * (y.val : ℚ) = ((x*y).val : ℚ) := by
  fin_cases x <;> fin_cases y <;> simp
  apply one_mul

lemma StandardRepr_2sum_isRegular {M₁ M₂ : StandardRepr α Z2} {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y)
    (hM₁ : M₁.HasTuSigning) (hM₂ : M₂.HasTuSigning) :
    (StandardRepr_2sum ha hXY).fst.HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepr_2sum_B ha hXY
  let x' : M₁.Y.Elem → ℚ := B₁ ⟨a, haX₁⟩
  let y' : M₂.X.Elem → ℚ := (B₂ · ⟨a, haY₂⟩)
  let A₁' : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem ℚ := B₁ ∘ Set.diff_subset.elem
  let A₂' : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem ℚ := (B₂ · ∘ Set.diff_subset.elem)
  have hA₁ :
    ∀ i : (M₁.X \ {a}).Elem, ∀ j : M₁.Y.Elem,
      |A₁' i j| = (M₁.B (Set.diff_subset.elem i) j).val
  · intro i j
    exact hBB₁ (Set.diff_subset.elem i) j
  have hA₂ :
    ∀ i : M₂.X.Elem, ∀ j : (M₂.Y \ {a}).Elem,
      |A₂' i j| = (M₂.B i (Set.diff_subset.elem j)).val
  · intro i j
    exact hBB₂ i (Set.diff_subset.elem j)
  have hx' : ∀ j, |x' j| = (M₁.B ⟨a, haX₁⟩ j).val
  · intro j
    exact hBB₁ ⟨a, haX₁⟩ j
  have hy' : ∀ i, |y' i| = (M₂.B i ⟨a, haY₂⟩).val
  · intro i
    exact hBB₂ i ⟨a, haY₂⟩
  let B' := Matrix_2sumComposition A₁' x' A₂' y' -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply Matrix_2sumComposition_isTotallyUnimodular
    · apply hB₁.comp_rows
    · apply hB₂.comp_cols
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all [B']
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        simp only [Matrix.fromBlocks_apply₂₁, B', hx', hy', abs_mul]
        apply todo_find_home
      | inr j₂ =>
        specialize hA₂ i₂ j₂
        simp_all [x', y', A₁', A₂', B']

/-- Any 2-sum of regular matroids is a regular matroid.
This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem StandardRepresentation.Is2sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨_, _, _, rfl, rfl, rfl, _, _, _, rfl, -⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply StandardRepr_2sum_isRegular
  · exact hM₁
  · exact hM₂

end TwoSum

-- TODO port 3-sum


section IsGraphic

-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops
/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic {α : Type} [DecidableEq α] (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ M = (VectorMatroid.mk X Y A).toMatroid

/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic {α : Type} {X Y : Set α} {M : Matroid α} {A : Matrix X Y ℚ}
    (hMA : M = (VectorMatroid.mk X Y A).toMatroid) (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  sorry

/-- Graphic matroid is regular. -/
lemma Matroid.IsGraphic.isRegular {α : Type} [DecidableEq α] {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  sorry

end IsGraphic


section IsCographic

/-- Matroid is cographic iff its dual is represented by an incidence matrix of a graph. -/
def Matroid.IsCographic {α : Type} [DecidableEq α] (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Cographic matroid is regular. -/
lemma Matroid.IsCographic.is_regular {α : Type} [DecidableEq α] {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  sorry

end IsCographic


section decomposition

variable {α : Type} [DecidableEq α]

/-- TODO define R10. -/
def matroidR10 : StandardRepr α Z2 :=
  sorry -- inside we have some `Fin 10 ↪ α` whose image is `E`

/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) : M.IsGood
| theR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
--| is1sum {M M₁ M₂ : Matroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
--| is3sum {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

/-- THE HOLY GRAIL. -/
theorem oldSeymour {M : Matroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry

end decomposition
