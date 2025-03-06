import Seymour.Matroid.Operations.Sum1
import Seymour.Matroid.Operations.Sum2
import Seymour.Matroid.Operations.Sum3
import Seymour.Matroid.Notions.Graphic


variable {α : Type} [DecidableEq α]

/-- TODO define R10. -/
def matroidR10 : StandardRepr α Z2 :=
  sorry

/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) : M.IsGood
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : Matroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

/-- THE HOLY GRAIL. -/
theorem oldSeymour {M : Matroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry
