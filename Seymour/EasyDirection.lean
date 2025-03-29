import Seymour.Matroid.Operations.Sum1
import Seymour.Matroid.Operations.Sum2
import Seymour.Matroid.Operations.Sum3
import Seymour.Matroid.Notions.Graphicness
import Seymour.Matroid.Special.R10

variable {α : Type} [DecidableEq α]

/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) : M.IsGood
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : Matroid α} (hM : M.Is1sumOf M₁ M₂) (hM₁ : M₁.IsGood) (hM₂ : M₂.IsGood) : M.IsGood
| is2sum {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsGood) (hM₂ : M₂.IsGood) : M.IsGood
| is3sum {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsGood) (hM₂ : M₂.IsGood) : M.IsGood

/-- Corollary of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsGood.isRegular {M : Matroid α} (hM : M.IsGood) : M.IsRegular := by
  induction hM with
  | graphic hM => exact hM.isRegular
  | cographic hM => exact hM.isRegular
  | @isomorphicR10 M e hM => simp [←M.isRegular_mapEquiv_iff e, hM]
  | is1sum hM _ _ ih₁ ih₂ => exact hM.isRegular ih₁ ih₂
  | is2sum hM _ _ ih₁ ih₂ => exact hM.isRegular ih₁ ih₂
  | is3sum hM _ _ ih₁ ih₂ => exact hM.isRegular ih₁ ih₂
