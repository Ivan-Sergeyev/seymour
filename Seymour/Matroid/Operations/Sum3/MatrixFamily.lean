import Seymour.Matroid.Operations.Sum3.CanonicalSigning


variable {α : Type}

/-- Captures definition 49. -/
/-private-/ structure matrix3sumLike (Xₗ Yₗ Xᵣ Yᵣ : Set α) (c₀ c₁ : Xᵣ → ℚ) where
  Aₗ : Matrix Xₗ Yₗ ℚ
  Aᵣ : Matrix Xᵣ Yᵣ ℚ
  D : Matrix Xᵣ Yₗ ℚ
  hc₀ : ∀ i, c₀ i ∈ Set.range SignType.cast
  hc₁ : ∀ i, c₁ i ∈ Set.range SignType.cast
  hc₀₁ : ∀ i, c₀ i - c₁ i ∈ Set.range SignType.cast
  hAₗ : (Aₗ ⊟ D).IsTotallyUnimodular
  hAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular
  hD : ∀ j, (D · j) = 0 ∨ (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀

/-private-/ abbrev matrix3sumLike.matrix {Xₗ Yₗ Xᵣ Yᵣ : Set α} {c₀ c₁ : Xᵣ → ℚ}
    (C : matrix3sumLike Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ C.Aₗ 0 C.D C.Aᵣ

/-- todo: capture lemma 51. -/
/-private-/ lemma matrix3sumLike_pivot {Xₗ Yₗ Xᵣ Yᵣ : Set α} {c₀ c₁ : Xᵣ → ℚ} (C : matrix3sumLike Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    {x : Xₗ} {y : Yₗ} (hxy : C.Aₗ x y ≠ 0) :
    False :=
  sorry

/-- Captures lemma 52. -/
/-private-/ lemma matrix3sumLike_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {c₀ c₁ : Xᵣ → ℚ} (C : matrix3sumLike Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    C.matrix.IsTotallyUnimodular :=
  sorry


variable [DecidableEq α]

/-- Captures lemma 50. -/
/-private-/ def matrix3sumCanonicalSigning_to_matrix3sumLike {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ ℚ} {Bᵣ : Matrix Xᵣ Yᵣ ℚ} (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ : Bₗ.IsTotallyUnimodular) (hBᵣ : Bᵣ.IsTotallyUnimodular) :
      matrix3sumLike (Xₗ \ {x₀, x₁}) (Yₗ \ {y₂}) (Xᵣ \ {x₂}) (Yᵣ \ {y₀, y₁}) (Bᵣ._col ⟨y₀, hYY.mem3₀ᵣ⟩) (Bᵣ._col ⟨y₁, hYY.mem3₁ᵣ⟩) where
  -- let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  -- let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  Aₗ := sorry
  Aᵣ := sorry
  D := sorry
  hc₀ := sorry
  hc₁ := sorry
  hc₀₁ := sorry
  hAₗ := sorry
  hAᵣ := sorry
  hD := sorry

/-- Captures lemma 53. -/
/-private-/ lemma matrix3sumCanonicalSigning_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ ℚ} {Bᵣ : Matrix Xᵣ Yᵣ ℚ} (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ : Bₗ.IsTotallyUnimodular) (hBᵣ : Bᵣ.IsTotallyUnimodular) :
    -- TODO propagate the necessary assumptions from `standardRepr3sumComposition.snd`
    (matrix3sumCanonicalSigning Bₗ Bᵣ hXX hYY).IsTotallyUnimodular := by
  sorry
