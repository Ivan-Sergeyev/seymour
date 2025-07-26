import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic.Basic

/-!
# Basic stuff about matrices

This file provides a specific API about matrices for the purposes of our project.
-/

open scoped Matrix

variable {α : Type*}

@[simp]
lemma Matrix.one_fromCols_transpose [Zero α] [One α] {m n : Type*} [DecidableEq m] (A : Matrix m n α) :
    (1 ◫ A)ᵀ = (1 : Matrix m m α) ⊟ Aᵀ := by
  rw [←Matrix.transpose_one, ←Matrix.transpose_fromCols, Matrix.transpose_one]

@[simp]
lemma Matrix.one_fromRows_transpose [Zero α] [One α] {m n : Type*} [DecidableEq n] (A : Matrix m n α) :
    (1 ⊟ A)ᵀ = ((1 : Matrix n n α) ◫ Aᵀ : Matrix ..) := by
  rw [←Matrix.transpose_one, ←Matrix.transpose_fromRows, Matrix.transpose_one]

@[simp]
lemma Matrix.fromCols_one_transpose [Zero α] [One α] {m n : Type*} [DecidableEq m] (A : Matrix m n α) :
    (A ◫ 1)ᵀ = Aᵀ ⊟ (1 : Matrix m m α) := by
  rw [←Matrix.transpose_one, ←Matrix.transpose_fromCols, Matrix.transpose_one]

@[simp]
lemma Matrix.fromRows_one_transpose [Zero α] [One α] {m n : Type*} [DecidableEq n] (A : Matrix m n α) :
    (A ⊟ 1)ᵀ = (Aᵀ ◫ (1 : Matrix n n α) : Matrix ..) := by
  rw [←Matrix.transpose_one, ←Matrix.transpose_fromRows, Matrix.transpose_one]

/-- Two matrices are equal if they agree on all columns. -/
lemma Matrix.ext_col {m n : Type*} {A B : Matrix m n α} (hAB : ∀ i : m, A i = B i) : A = B :=
  Matrix.ext (congr_fun <| hAB ·)

/-- Computing the determinant of a square integer matrix and then converting it to a general field gives the same result as
    converting all elements to given field and computing the determinant afterwards. -/
lemma Matrix.det_int_coe [DecidableEq α] [Fintype α] (A : Matrix α α ℤ) (F : Type*) [Field F] :
    ((A.det : ℤ) : F) = ((A.map Int.cast).det : F) := by
  simp only [Matrix.det_apply, Int.cast_sum, Matrix.map_apply]
  congr
  ext p
  if h1 : p.sign = 1 then
    simp [h1]
  else
    simp [Int.units_ne_iff_eq_neg.→ h1]

lemma Matrix.entryProd_outerProd_eq_mul_col_mul_row {m n : Type*} [Semigroup α] (A : Matrix m n α) (c : m → α) (r : n → α) :
    A ⊡ c ⊗ r = Matrix.of (fun i : m => fun j : n => (A i j * c i) * r j) := by
  simp [mul_assoc]

lemma Matrix.entryProd_outerProd_eq_mul_row_mul_col {m n : Type*} [CommSemigroup α] (A : Matrix m n α) (c : m → α) (r : n → α) :
    A ⊡ c ⊗ r = Matrix.of (fun i : m => fun j : n => (A i j * r j) * c i) := by
  ext
  simp only [Matrix.of_apply, smul_eq_mul]
  nth_rw 2 [mul_comm]
  rw [mul_assoc]

lemma sum_elem_smul_matrix_row_of_mem [DecidableEq α] {β : Type*} [NonAssocSemiring β] {x : α} {S : Set α} [Fintype S]
    (f : α → β) (hxS : x ∈ S) :
    ∑ i : S.Elem, f i • (1 : Matrix α α β) x i.val = f x := by
  convert sum_elem_of_single_nonzero hxS (fun a ha =>
    show ((f a • (1 : Matrix α α β) x a) = 0) by simp [Matrix.one_apply_ne' ha])
  rw [Matrix.one_apply_eq x, smul_eq_mul, mul_one]

lemma sum_elem_smul_matrix_row_of_nmem [DecidableEq α] {β : Type*} [NonAssocSemiring β] {x : α} {S : Set α} [Fintype S]
    (f : α → β) (hxS : x ∉ S) :
    ∑ i : S.Elem, f i • (1 : Matrix α α β) x i.val = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  rw [Matrix.one_apply_ne' (ne_of_mem_of_not_mem y.property hxS)]
  apply smul_zero

/-- The absolute value of a matrix is a matrix made of absolute values of respective elements. -/
def Matrix.abs [LinearOrderedAddCommGroup α] {m n : Type*} (A : Matrix m n α) : Matrix m n α :=
  Matrix.of (|A · ·|)

-- We redeclare `|·|` instead of using the existing notation because the official `abs` requires a lattice.
macro:max atomic("|" noWs) A:term noWs "|" : term => `(Matrix.abs $A)
