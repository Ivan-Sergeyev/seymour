import Seymour.Matroid.Sum1
import Seymour.Matroid.Sum2
import Seymour.Matroid.Sum3
import Seymour.Matroid.Graphicness
import Seymour.Matroid.R10

variable {α : Type} [DecidableEq α]

/-- Simplified definition:
    (1) does not include cographic matroids
    (2) uses the less general version of 3-sum -/
inductive Matroid.IsGoodaux : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGoodaux
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGoodaux
-- fork constructors
| is1sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is1sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsGoodaux) (hMᵣ : Mᵣ.IsGoodaux) : M.IsGoodaux
| is2sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is2sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsGoodaux) (hMᵣ : Mᵣ.IsGoodaux) : M.IsGoodaux
| is3sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOfaux Mₗ Mᵣ) (hMₗ : Mₗ.IsGoodaux) (hMᵣ : Mᵣ.IsGoodaux) : M.IsGoodaux

/-- Corollary of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsGoodaux.isRegular {M : Matroid α} (hM : M.IsGoodaux) : M.IsRegular := by
  induction hM with
  | graphic hM => exact hM.isRegular
  | @isomorphicR10 M e hM => simp [←M.isRegular_mapEquiv_iff e, hM]
  | is1sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
  | is2sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
  | is3sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
/--
info: 'Matroid.IsGoodaux.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.IsGoodaux.isRegular

/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) : M.IsGood
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is1sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood
| is2sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is2sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood
| is3sum {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsGood) (hMᵣ : Mᵣ.IsGood) : M.IsGood

/-- Corollary of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsGood.isRegular {M : Matroid α} (hM : M.IsGood) : M.IsRegular := by
  induction hM with
  | graphic hM => exact hM.isRegular
  | cographic hM => sorry
  | @isomorphicR10 M e hM => simp [←M.isRegular_mapEquiv_iff e, hM]
  | is1sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
  | is2sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
  | is3sum hM _ _ ihₗ ihᵣ => exact hM.isRegular ihₗ ihᵣ
