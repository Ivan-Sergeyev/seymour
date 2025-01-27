import Mathlib.Data.Matroid.Map

import Seymour.Matroid.Classes.Regular
import Seymour.Matroid.Classes.Graphic
import Seymour.Matroid.Constructors.ConcreteInstances
import Seymour.Matroid.Operations.SumDelta.Basic

/-!
This file states the "hard" (decomposition) direction of the Seymour decomposition theorem.
-/

def BinaryMatroid.Is1sumOf {α : Type} [DecidableEq α] (M M₁ M₂ : BinaryMatroid α) : Prop := sorry -- todo: move to SumDelta
def BinaryMatroid.Is2sumOf {α : Type} [DecidableEq α] (M M₁ M₂ : BinaryMatroid α) : Prop := sorry -- todo: move to SumDelta
def BinaryMatroid.Is3sumOf {α : Type} [DecidableEq α] (M M₁ M₂ : BinaryMatroid α) : Prop := sorry -- todo: move to SumDelta

/-- Every regular matroid `M` can be constructed using direct sums, 2-sums, and 3-sums starting
  with matroids each of which is either graphic, cographic, or isomorphic to R10,
  and each of which is isomorphic to a minor of `M`. TODO this is not what the definition says! -/
inductive BinaryMatroid.IsGood {α : Type} [DecidableEq α] : BinaryMatroid α → Prop
-- leaf constructors
| graphic {M : BinaryMatroid α} (hM : M.toMatroid.IsGraphic) : M.IsGood
| cographic {M : BinaryMatroid α} (hM : M.toMatroid.IsCographic) : M.IsGood
| isomR10 {M : BinaryMatroid α} {e : α ≃ Fin 10} (hM : M.toMatroid.mapEquiv e = MatroidR10.toVectorMatroid.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M M₁ M₂ : BinaryMatroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

theorem hardSeymour {α : Type} [DecidableEq α] {M : BinaryMatroid α} (hM : M.toMatroid.IsRegular) : M.IsGood := by
  sorry
