import Seymour.Basic

-- #check Matrix.linearIndependent_rows_of_invertible
-- #check Matrix.Nondegenerate

variable {X Y F : Type} [DecidableEq X] [Fintype X] [Field F]

/-- Rows of a matrix are linearly independent iff the matrix contains a nonsigular square submatrix of full height. -/
lemma Matrix.linearIndendent_iff_exists_submatrix_unit (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, IsUnit (A.submatrix id f) := by
  sorry

/-- Rows of a matrix are linearly independent iff the matrix contains a square submatrix of full height with nonzero det. -/
lemma Matrix.linearIndendent_iff_exists_submatrix_det (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, (A.submatrix id f).det ≠ 0 := by
  convert A.linearIndendent_iff_exists_submatrix_unit
  convert isUnit_iff_ne_zero.symm
  apply Matrix.isUnit_iff_isUnit_det
