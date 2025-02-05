import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.Data.Fintype.Card
import Seymour.ForMathlib.Basic


/-- Formally verified algorithm for testing total unimodularity. -/
def Matrix.testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ k : ℕ, k ≤ min m n → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ Set.range SignType.cast


lemma Matrix.isTotallyUnimodular_of_aux_le {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ}
    (hA : ∀ k : ℕ, k ≤ m → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ Set.range SignType.cast) :
    A.IsTotallyUnimodular := by
  intro k f g hf _
  have hkm : k ≤ m
  · simpa using Fintype.card_le_of_injective f hf
  exact hA k hkm f g

lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular → A.IsTotallyUnimodular := by
  intro hA
  if hmn : m ≤ n then
    have hm : min m n = m := Nat.min_eq_left hmn
    apply A.isTotallyUnimodular_of_aux_le
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    convert hA
    exact hm.symm
  else
    push_neg at hmn
    have hn : min m n = n := Nat.min_eq_right hmn.le
    rw [←Matrix.transpose_isTotallyUnimodular_iff]
    apply A.transpose.isTotallyUnimodular_of_aux_le
    intro k hk f g
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    rw [←Matrix.det_transpose]
    exact hA k (hk.trans_eq hn.symm) g f

theorem Matrix.testTotallyUnimodular_eq_isTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor
  · exact A.isTotallyUnimodular_of_testTotallyUnimodular
  intro hA
  rw [Matrix.isTotallyUnimodular_iff] at hA
  simp only [Matrix.testTotallyUnimodular, and_imp, decide_eq_true_eq, eq_iff_iff, iff_true]
  intro k _ f g
  exact hA k f g

instance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Decidable A.IsTotallyUnimodular :=
  decidable_of_iff _ A.testTotallyUnimodular_eq_isTotallyUnimodular


/-- Faster algorithm for testing total unimodularity but without formal guarantees. -/
def Matrix.testTotallyUnimodularFaster {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  (∀ k : ℕ, k < min m n → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ Set.range SignType.cast) ∧ (
    if hmn : m = n
      then (A.submatrix id (finCongr hmn)).det ∈ Set.range SignType.cast
    else if m < n
      then (∀ y : Fin m → Fin n, (A.submatrix id y).det ∈ Set.range SignType.cast)
      else (∀ x : Fin n → Fin m, (A.submatrix x id).det ∈ Set.range SignType.cast)
  )
