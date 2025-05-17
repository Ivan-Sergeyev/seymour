import Seymour.Matrix.Basic

variable {X Y R : Type} [CommRing R]

/-- Matrix `A` satisfies TUness for submatrices up to `k`×`k` size, i.e.,
    the determinant of every `k`×`k` submatrix of `A` (not necessarily injective) is `1`, `0`, or `-1`. -/
def Matrix.isPartiallyUnimodular (A : Matrix X Y R) (k : ℕ) : Prop :=
  ∀ f : Fin k → X, ∀ g : Fin k → Y, (A.submatrix f g).det ∈ SignType.cast.range

lemma exists_submatrix_of_not_isPartiallyUnimodular {A : Matrix X Y R} {k : ℕ} (hAk : ¬ A.isPartiallyUnimodular k) :
    ∃ f : Fin k → X, ∃ g : Fin k → Y, (A.submatrix f g).det ∉ SignType.cast.range := by
  simpa [Matrix.isPartiallyUnimodular] using hAk

lemma Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k, A.isPartiallyUnimodular k :=
  A.isTotallyUnimodular_iff
