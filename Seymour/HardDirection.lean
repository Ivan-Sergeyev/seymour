import Seymour.EasyDirection


variable {α : Type*} [DecidableEq α]

/-- The hard direction of the Seymour's theorem. -/
theorem Matroid.IsRegular.isGood {M : Matroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry

/-- Matroid is regular iff it can be decomposed into graphic matroids & cographics matroids & matroids isomorphic to R10
    using 1-sums & 2-sums & 3-sums. -/
theorem Matroid.isRegular_iff_isGood (M : Matroid α) : M.IsRegular ↔ M.IsGood :=
  ⟨Matroid.IsRegular.isGood, Matroid.IsGood.isRegular⟩
