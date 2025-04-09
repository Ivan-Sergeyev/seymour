import Seymour.Matrix.Basic

variable {X Y Z R : Type} [Fintype Z] [DecidableEq Z] [CommRing R] {f : Z → X} {g : Z → Y}

lemma Matrix.submatrix_det_zero_of_not_injective_right (A : Matrix X Y R) (hg : ¬g.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [Function.not_injective_iff] at hg
  obtain ⟨i, j, hgij, hij⟩ := hg
  apply Matrix.det_zero_of_column_eq hij
  simp [hgij]

lemma Matrix.submatrix_det_zero_of_not_injective_left (A : Matrix X Y R) (hf : ¬f.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [←Matrix.det_transpose, Matrix.transpose_submatrix]
  exact A.transpose.submatrix_det_zero_of_not_injective_right hf
