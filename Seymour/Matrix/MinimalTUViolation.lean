import Seymour.Matrix.Pivoting


variable {X Y R : Type} [CommRing R]

/-- A matrix is minimal TU violating if it is not TU, but its every proper submatrix is TU. -/
def Matrix.IsMinimalTUViolating (A : Matrix X Y R) : Prop :=
  ¬A.IsTotallyUnimodular ∧
    ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, (¬f.Surjective ∨ ¬g.Surjective) → (A.submatrix f g).IsTotallyUnimodular

/-- The order of a minimal TU violating matrix is the number of its rows. -/
def Matrix.IsMinimalTUViolating.order {A : Matrix X Y R} (_hA : A.IsMinimalTUViolating) (hX : Fintype X) (_hY : Fintype Y) :=
  hX.card

def Matrix.ContainsMinimalTUViolating (A : Matrix X Y R) (k : ℕ) : Prop :=
  ∃ f : Fin k → X, ∃ g : Fin k → Y, f.Bijective ∧ g.Bijective ∧ (A.submatrix f g).IsMinimalTUViolating

/-- A minimal TU violating matrix is square. -/
lemma Matrix.IsMinimalTUViolating_is_square {A : Matrix X Y R} (hA : A.IsMinimalTUViolating) (hX : Fintype X) (hY : Fintype Y) :
    hX.card = hY.card := by
  obtain ⟨hAnot, hAyes⟩ := hA
  rw [Matrix.IsTotallyUnimodular] at hAnot
  push_neg at hAnot
  obtain ⟨k, f, g, inj_f, inj_g, hAfg⟩ := hAnot
  specialize hAyes k f g
  by_contra hXY
  apply hAfg
  rw [Matrix.isTotallyUnimodular_iff] at hAyes
  apply hAyes
  rw [← Mathlib.Tactic.PushNeg.not_and_or_eq]
  intro ⟨surj_f, surj_g⟩
  apply hXY
  trans k <;> rw [←Fintype.card_fin k]
  · symm
    exact Fintype.card_of_bijective ⟨inj_f, surj_f⟩
  · exact Fintype.card_of_bijective ⟨inj_g, surj_g⟩

/-- A 2 × 2 minimal TU violating matrix has four ±1 entries. -/
lemma Matrix.IsMinimalTUViolating_two_by_two_entries {A : Matrix X Y R}
  (hA : A.IsMinimalTUViolating) (hX : Fintype X) (hY : Fintype Y) (hA2: hA.order hX hY = 2) :
    ∀ i j, A i j = -1 ∨ A i j = 1 :=
  sorry

/-- Every non-TU matrix contains a minimal TU violating matrix. -/
lemma Matrix.IsMinimalTUViolating_in_non_TU {A : Matrix X Y R} (hA : ¬A.IsTotallyUnimodular) :
    ∃ k : ℕ, A.ContainsMinimalTUViolating k :=
  sorry

variable {F : Type} [Field F]

/-- The form of a matrix after pivoting and removing the pivot row and column. -/
lemma Matrix.shortTableauPivot_no_pivot_row_col [DecidableEq X] [DecidableEq Y]
  (A : Matrix X Y F) (x : X) (y : Y) (i : X) (j : Y) (hix : i ≠ x) (hjx : j ≠ y) :
    A.shortTableauPivot x y i j = A i j - A i y * A x j / A x y := by
  simp [Matrix.shortTableauPivot, hix, hjx]

/-- Pivoting in a minimal TU violating matrix and removing the pivot row and column
  yields a minimal TU violating matrix. -/
lemma Matrix.IsMinimalTUViolating_after_pivot {A : Matrix X Y R} {x : X} {y : Y}
  (hA : A.IsMinimalTUViolating) (hX : Fintype X) (hY : Fintype Y) (hXY : hX.card >= 2) (hxy : A x y ≠ 0) :
    False := -- fixme: pivot on A x y + delete pivot row & col => MVM
  sorry
  -- sketch:
  -- * the resulting matrix has the same determinant as the original one (cofactor computation), hence not TU
  -- * every proper submatrix is TU, because TUness is preserved under pivoting
