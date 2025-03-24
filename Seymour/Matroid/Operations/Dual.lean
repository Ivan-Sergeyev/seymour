import Seymour.Matroid.Constructors.StandardRepresentation


variable {α R : Type} [DecidableEq α] [DivisionRing R]

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.B.transpose
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of standard representation gives a dual matroid. -/
lemma StandardRepr.dual_toMatroid (S : StandardRepr α R) :
    S✶.toMatroid = S.toMatroid✶ :=
  sorry -- Theorem 2.2.8 in Oxley

/-- Every vector matroid's dual has a standard representation. -/
lemma VectorMatroid.dual_exists_standardRepr (M : VectorMatroid α R) :
    ∃ S' : StandardRepr α R, S'.toMatroid = M.toMatroid✶ :=
  have ⟨S, hS⟩ := M.exists_standardRepr
  ⟨S✶, hS ▸ S.dual_toMatroid⟩
