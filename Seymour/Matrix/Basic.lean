import Seymour.Basic.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

open scoped Matrix

variable {α : Type}

@[simp low]
abbrev Matrix.prependId [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) : Matrix m (m ⊕ n) α :=
  Matrix.fromCols 1 A

@[simp low]
abbrev Matrix.uppendId [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) : Matrix (n ⊕ m) n α :=
  Matrix.fromRows 1 A

@[simp]
lemma Matrix.prependId_transpose [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) :
    A.prependIdᵀ = Aᵀ.uppendId := by
  ext i j
  cases i with
  | inr => rfl
  | inl i' =>
    if hi' : i' = j then
      simp [Matrix.one_apply_eq, hi']
    else
      simp [Matrix.one_apply_ne, hi', Ne.symm hi']

@[simp]
lemma Matrix.uppendId_transpose [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) :
    A.uppendIdᵀ = Aᵀ.prependId := by
  rw [←Matrix.transpose_transpose A.transpose.prependId, Matrix.prependId_transpose, Matrix.transpose_transpose]

lemma Matrix.ext_col {m n : Type} {A B : Matrix m n α} (hAB : ∀ i : m, A i = B i) : A = B :=
  Matrix.ext (congr_fun <| hAB ·)

lemma Matrix.det_int_coe [DecidableEq α] [Fintype α] (A : Matrix α α ℤ) (F : Type) [Field F] :
    ((A.det : ℤ) : F) = ((A.map Int.cast).det : F) := by
  simp only [Matrix.det_apply, Int.cast_sum, Matrix.map_apply]
  congr
  ext p
  if h1 : p.sign = 1 then
    simp [h1]
  else
    simp [Int.units_ne_iff_eq_neg.→ h1]

lemma Matrix.det_rat_coe [DecidableEq α] [Fintype α] (A : Matrix α α ℚ) (F : Type) [Field F] [CharZero F] :
    ((A.det : ℚ) : F) = ((A.map Rat.cast).det : F) := by
  simp only [Matrix.det_apply, Rat.cast_sum, Matrix.map_apply]
  congr
  ext p
  if h1 : p.sign = 1 then
    simp [h1]
  else
    simp [Int.units_ne_iff_eq_neg.→ h1]

lemma IsUnit.linearIndependent_matrix [DecidableEq α] [Fintype α] {R : Type} [CommRing R] {A : Matrix α α R} (hA : IsUnit A) :
    LinearIndependent R A :=
  A.linearIndependent_rows_of_isUnit hA

lemma sum_elem_matrix_row_of_mem [DecidableEq α] {β : Type} [AddCommMonoidWithOne β] {x : α} {S : Set α} [Fintype S]
    (hxS : x ∈ S) :
    ∑ i : S.Elem, (1 : Matrix α α β) x i.val = 1 := by
  convert sum_elem_of_single_nonzero hxS (fun _ => Matrix.one_apply_ne')
  exact (Matrix.one_apply_eq x).symm

lemma sum_elem_matrix_row_of_nmem [DecidableEq α] {β : Type} [AddCommMonoidWithOne β] {x : α} {S : Set α} [Fintype S]
    (hxS : x ∉ S) :
    ∑ i : S.Elem, (1 : Matrix α α β) x i.val = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  exact Matrix.one_apply_ne' (ne_of_mem_of_not_mem y.property hxS)


variable {T₁ T₂ S₁ S₂ : Set α} {β : Type}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (A : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((A ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- Convert a matrix over set unions to a block matrix. -/
def Matrix.toMatrixSumSum (A : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β :=
  ((A ∘ Sum.toUnion) · ∘ Sum.toUnion)

/-- Converting a block matrix to a matrix over set unions and back to a block matrix gives the original matrix, assuming that
    both said unions are disjoint. -/
@[simp]
lemma toMatrixUnionUnion_toMatrixSumSum (hT : T₁ ⫗ T₂) (hS : S₁ ⫗ S₂) (A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    A.toMatrixUnionUnion.toMatrixSumSum = A := by
  ext
  simp [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, *]

/-- Converting a matrix over set unions to a block matrix and back to a matrix over set unions gives the original matrix. -/
@[simp]
lemma toMatrixSumSum_toMatrixUnionUnion (A : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    A.toMatrixSumSum.toMatrixUnionUnion = A := by
  ext
  simp [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum]

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.IsTotallyUnimodular.toMatrixUnionUnion [CommRing β] {A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β}
    (hA : A.IsTotallyUnimodular) :
    A.toMatrixUnionUnion.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intros
  apply hA
