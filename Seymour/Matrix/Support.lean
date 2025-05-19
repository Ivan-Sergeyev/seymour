import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic.Fin


variable {X Y R : Type} [Zero R] [DecidableEq R]

@[simp]
def Matrix.support (A : Matrix X Y R) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

lemma Matrix.support_transpose (A : Matrix X Y R) :
    A.support.transpose = A.transpose.support :=
  rfl

lemma Matrix.support_submatrix (A : Matrix X Y R) {X' Y' : Type} (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl

omit R

lemma Matrix.support_Z2 (A : Matrix X Y Z2) : A.support = A := by
  aesop

lemma Matrix.IsTotallyUnimodular.abs_eq_support_val {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j| = (A.support i j).val := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ZMod.natCast_val, ←hs]
  cases s <;> rfl

lemma Matrix.IsTotallyUnimodular.abs_cast_eq_support {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j|.cast = A.support i j := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ←hs]
  cases s <;> simp
