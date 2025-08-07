import Seymour.Results.EasyDirection


variable {α : Type*} [DecidableEq α]

/-- The hard direction of the Seymour's theorem (restricted to matroids of finite rank). -/
theorem Matroid.IsRegular.isGood_of_rankFinite {M : Matroid α} (hM : M.IsRegular) (hM' : M.RankFinite) : M.IsGood := by
  sorry

/-- Matroid of finite rank is regular iff it can be decomposed into
    graphic matroids & cographics matroids & matroids isomorphic to R10 using 1-sums & 2-sums & 3-sums. -/
theorem Matroid.RankFinite.isRegular_iff_isGood {M : Matroid α} (hM : M.RankFinite) : M.IsRegular ↔ M.IsGood :=
  ⟨(·.isGood_of_rankFinite hM), Matroid.IsGood.isRegular⟩
