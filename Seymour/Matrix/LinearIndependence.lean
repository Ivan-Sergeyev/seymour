import Seymour.Matrix.Basic
import Mathlib.Data.Matrix.Rank

open scoped Matrix

variable {X Y F : Type} [Fintype X] [Fintype Y] [Field F]

lemma Matrix.not_linearIndependent_of_rank_lt (A : Matrix X Y F) (hA : A.rank < #X) :
    ¬ LinearIndependent F A :=
  (A.rank_eq_finrank_span_row ▸ finrank_span_eq_card · ▸ hA |>.false)

lemma Matrix.not_linearIndependent_of_too_many_rows (A : Matrix X Y F) (hYX : #Y < #X) :
    ¬ LinearIndependent F A :=
  A.not_linearIndependent_of_rank_lt (A.rank_le_card_width.trans_lt hYX)


variable [DecidableEq X] [DecidableEq Y]

lemma Matrix.exists_submatrix_rank (A : Matrix X Y F) : ∃ r : Fin A.rank → X, (A.submatrix r id).rank = A.rank := by
  simp only [Matrix.rank_eq_finrank_span_row]
  sorry

/-- Rows of a matrix are linearly independent iff the matrix contains a nonsigular square submatrix of full height. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_unit (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, IsUnit (A.submatrix id f) := by
  constructor
  · intro hA
    have hXA : #X = Aᵀ.rank := (A.rank_transpose.trans hA.rank_matrix).symm
    obtain ⟨f, hf⟩ := Aᵀ.exists_submatrix_rank
    use f ∘ Fintype.equivFinOfCardEq hXA
    have hX : #X = (A.submatrix id (f ∘ Fintype.equivFinOfCardEq hXA)).rank
    · rw [←Matrix.transpose_submatrix, Matrix.rank_transpose] at hf
      conv => lhs; rw [hXA, ←hf]
      exact ((A.submatrix id f).rank_submatrix (Equiv.refl X) (Fintype.equivFinOfCardEq hXA)).symm
    rw [←Matrix.linearIndependent_rows_iff_isUnit, linearIndependent_iff_card_eq_finrank_span, hX]
    apply Matrix.rank_eq_finrank_span_row
  · intro ⟨f, hAf⟩
    exact hAf.linearIndependent_matrix.of_comp (LinearMap.funLeft F F f)

/-- Rows of a matrix are linearly independent iff the matrix contains a square submatrix of full height with nonzero det. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_det (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, (A.submatrix id f).det ≠ 0 := by
  convert A.linearIndependent_iff_exists_submatrix_unit
  convert isUnit_iff_ne_zero.symm
  apply Matrix.isUnit_iff_isUnit_det
