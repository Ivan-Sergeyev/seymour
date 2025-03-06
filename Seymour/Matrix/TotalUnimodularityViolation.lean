import Seymour.Matrix.Basic


variable {X Y R : Type} [CommRing R]

/-- The smallest submatrix of `A` that is not totally unimodular has size `k` (propositionally equal to what is written). -/
def Matrix.MinimumViolationSizeIs (A : Matrix X Y R) (k : ℕ) : Prop :=
  (∀ n : ℕ, ∀ f : Fin n → X, ∀ g : Fin n → Y, n < k → f.Injective → g.Injective →
    (A.submatrix f g).det ∈ SignType.cast.range) ∧
  ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)

lemma Matrix.minimumViolationSizeIs_iff (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)) := by
  -- if not injective then `∈ SignType.cast.range` is tautological
  sorry

lemma Matrix.minimumViolationSizeIs_iff' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ∃ f : Fin k → X, ∃ g : Fin k → Y, f.Injective ∧ g.Injective ∧ (A.submatrix f g).det ∉ SignType.cast.range) := by
  simp [Matrix.minimumViolationSizeIs_iff]

lemma Matrix.minimumViolationSizeIs_iff'' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ∃ f : Fin k → X, ∃ g : Fin k → Y, (A.submatrix f g).det ∉ SignType.cast.range) := by
  -- `∉ SignType.cast.range` itself implies `f.Injective` and `g.Injective`
  sorry

lemma Matrix.isTotallyUnimodular_iff_none_minimumViolationSizeIs (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k : ℕ, ¬(A.MinimumViolationSizeIs k) := by
  sorry
