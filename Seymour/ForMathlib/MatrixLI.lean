import Seymour.Basic

#check Matrix.linearIndependent_rows_of_invertible
#check Matrix.Nondegenerate


lemma Matrix.linearIndendent_iff_exists_submatrix_unit {X Y F : Type} [DecidableEq X] [Fintype X] [Field F]
    (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, IsUnit (A.submatrix id f) := by
  sorry

lemma Matrix.linearIndendent_iff_exists_submatrix_det {X Y F : Type} [DecidableEq X] [Fintype X] [Field F]
    (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, (A.submatrix id f).det ≠ 0 := by
  convert A.linearIndendent_iff_exists_submatrix_unit
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.symm
