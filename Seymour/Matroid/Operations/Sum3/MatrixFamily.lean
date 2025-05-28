import Seymour.Matroid.Operations.Sum3.CanonicalSigning


variable {α : Type} [DecidableEq α]

-- TODO define the family of matrices, prove that the canonical signing is in it, prove that matrices in the family are TU

/-private-/ lemma matrix3sumCanonicalSigning_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ ℚ} {Bᵣ : Matrix Xᵣ Yᵣ ℚ} (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ : Bₗ.IsTotallyUnimodular) (hBᵣ : Bᵣ.IsTotallyUnimodular) :
    -- TODO propagate the necessary assumptions from `standardRepr3sumComposition.snd`
    (matrix3sumCanonicalSigning Bₗ Bᵣ hXX hYY).IsTotallyUnimodular := by
  sorry
