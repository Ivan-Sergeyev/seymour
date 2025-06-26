import Seymour.Matroid.Constructors.StandardRepresentation


/-- Shared properties of 1-sum, 2-sum, and 3-sum of binary matroids. -/
structure Matroid.IsPresumOf {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hXₗ : Finite Sₗ.X
  hXᵣ : Finite Sᵣ.X
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
