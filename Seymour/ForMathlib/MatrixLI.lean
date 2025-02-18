import Seymour.Basic
import Mathlib.Data.Matrix.Rank

variable {X Y F : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] [Field F]

lemma Matrix.exists_submatrix_rank (A : Matrix X Y F) : ∃ r : Fin A.rank → X, (A.submatrix r id).rank = A.rank := by
  sorry

/-- Rows of a matrix are linearly independent iff the matrix contains a nonsigular square submatrix of full height. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_unit (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, IsUnit (A.submatrix id f) := by
  constructor
  · intro hA
    have hXA : #X = A.transpose.rank := (A.rank_transpose.trans hA.rank_matrix).symm
    obtain ⟨f, hf⟩ := A.transpose.exists_submatrix_rank
    use f ∘ Fintype.equivFinOfCardEq hXA
    rw [←Matrix.transpose_submatrix, Matrix.rank_transpose] at hf
    have hX : #X = (A.submatrix id (f ∘ Fintype.equivFinOfCardEq hXA)).rank
    · conv => lhs; rw [hXA, ←hf]
      show (A.submatrix id f).rank = ((A.submatrix id f).submatrix (Equiv.refl X) (Fintype.equivFinOfCardEq hXA)).rank
      --have := (A.submatrix id f).rank_submatrix (Equiv.refl X) (Fintype.equivFinOfCardEq hXA)
      --have := (A.submatrix id f).rank_reindex (Equiv.refl X) (Fintype.equivFinOfCardEq hXA)
      sorry
    rw [←Matrix.linearIndependent_rows_iff_isUnit]
    show LinearIndependent F (A.submatrix id (f ∘ Fintype.equivFinOfCardEq hXA))
    rw [linearIndependent_iff_card_eq_finrank_span, hX]
    --simp [Set.finrank, Module.finrank, Matrix.rank, Submodule.span, LinearMap.range]
    sorry
  · intro ⟨f, hAf⟩
    exact hAf.linearIndependent_matrix.of_comp (LinearMap.funLeft F F f)

/-- Rows of a matrix are linearly independent iff the matrix contains a square submatrix of full height with nonzero det. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_det (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, (A.submatrix id f).det ≠ 0 := by
  convert A.linearIndependent_iff_exists_submatrix_unit
  convert isUnit_iff_ne_zero.symm
  apply Matrix.isUnit_iff_isUnit_det
