import Seymour.Matroid.Operations.Sum3.CanonicalSigning


/-- Canonical signing of 3-sum constructed from TU signings of summands. -/
@[simp]
/-private-/ noncomputable def matrix3sumCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (Bₗ' : Matrix Xₗ Yₗ ℚ) (Bᵣ' : Matrix Xᵣ Yᵣ ℚ) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    let ⟨⟨x₀ₗ, x₁ₗ, _⟩, ⟨_, _, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨_, _, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _⟩⟩ := hYY.inter3all
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ⊕ Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ ⊕ Yᵣ.drop2 y₀ᵣ y₁ᵣ) ℚ :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  -- convert summands to canonical form
  let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
  let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
  -- extract submatrices
  let Aₗ := Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ
  let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  let Aᵣ := Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  -- the actual definition
  matrix3sumComposition x₀ₗ x₁ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ

/-private-/ lemma matrix3sumCanonicalSigning_isSigningOf_matrix3sumComposition {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ ℚ} {Bᵣ : Matrix Xᵣ Yᵣ ℚ} (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ : ∀ i : Xₗ, ∀ j : Yₗ, Bₗ i j ∈ SignType.cast.range) (hBᵣ : ∀ i : Xᵣ, ∀ j : Yᵣ, Bᵣ i j ∈ SignType.cast.range) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- extract submatrices but over `Z2`
    let Aₗ := Bₗ.support.Aₗ x₀ₗ x₁ₗ y₂ₗ
    let Dₗ := Bₗ.support.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ := Bₗ.support.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Bᵣ.support.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Bᵣ.support.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- the necessary parts of "validity" of the 3-sum
    |Bₗ x₀ₗ y₀ₗ| = 1 →
    |Bₗ x₀ₗ y₂ₗ| = 1 →
    |Bₗ x₂ₗ y₀ₗ| = 1 →
    |Bₗ x₁ₗ y₂ₗ| = 1 →
    |Bₗ x₂ₗ y₁ₗ| = 1 →
    |Bᵣ x₀ᵣ y₀ᵣ| = 1 →
    |Bᵣ x₀ᵣ y₂ᵣ| = 1 →
    |Bᵣ x₂ᵣ y₀ᵣ| = 1 →
    |Bᵣ x₁ᵣ y₂ᵣ| = 1 →
    |Bᵣ x₂ᵣ y₁ᵣ| = 1 →
    -- the actual statement
    (matrix3sumCanonicalSigning Bₗ Bᵣ hXX hYY).IsSigningOf (
      matrix3sumComposition x₀ₗ x₁ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ
    ) := by
  intro x₀ₗ x₀ᵣ x₁ₗ x₁ᵣ x₂ₗ x₂ᵣ y₀ₗ y₀ᵣ y₁ₗ y₁ᵣ y₂ₗ y₂ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ hBₗ₀₀ hBₗ₀₂ hBₗ₂₀ hBₗ₁₂ hBₗ₂₁ hBᵣ₀₀ hBᵣ₀₂ hBᵣ₂₀ hBᵣ₁₂ hBᵣ₂₁
  rintro (iₗ | iᵣ) (jₗ | jᵣ)
  · simp [hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ, matrix3sumComposition]
  · rfl
  · if hx₀ : iᵣ.val = x₀ then
      if hy₀ : jₗ.val = y₀ then
        simp [hx₀, hy₀,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, D₀]
      else if hy₁ : jₗ.val = y₁ then
        have hyy : y₁ ≠ y₀ := sorry
        simp [hx₀, hy₁, hyy,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, D₀]
      else
        have hy₂ : jₗ.val ≠ y₂ := sorry
        have hYₗ : jₗ.val ∈ Yₗ := sorry
        simp [hx₀, hy₀, hy₁, hy₂, hYₗ,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, Dₗ]
    else if hx₁ : iᵣ.val = x₁ then
      have hxx : x₁ ≠ x₀ := sorry
      if hy₀ : jₗ.val = y₀ then
        simp [hx₁, hy₀, hxx,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, D₀]
      else if hy₁ : jₗ.val = y₁ then
        have hyy : y₁ ≠ y₀ := sorry
        simp [hx₁, hy₁, hxx, hyy,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, D₀]
      else
        have hy₂ : jₗ.val ≠ y₂ := sorry
        have hYₗ : jₗ.val ∈ Yₗ := sorry
        simp [hx₀, hx₁, hy₀, hy₁, hy₂, hxx, hYₗ,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, Dₗ]
    else
      have hx₂ : iᵣ.val ≠ x₂ := sorry
      have hXᵣ : iᵣ.val ∈ Xᵣ := sorry
      if hy₀ : jₗ.val = y₀ then
        simp [hx₀, hx₁, hx₂, hy₀, hXᵣ,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, Dᵣ]
      else if hy₁ : jₗ.val = y₁ then
        have hyy : y₁ ≠ y₀ := sorry
        simp [hx₀, hx₁, hx₂, hy₁, hyy, hXᵣ,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, Dᵣ]
      else
        have hy₂ : jₗ.val ≠ y₂ := sorry
        have hYₗ : jₗ.val ∈ Yₗ := sorry
        simp [hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hXᵣ, hYₗ,
          hBₗ, hBₗ₀₀, hBₗ₀₂, hBₗ₂₀, hBₗ₁₂, hBₗ₂₁, Aₗ, x₀ₗ, x₁ₗ, x₂ₗ, y₀ₗ, y₁ₗ, y₂ₗ,
          hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
          matrix3sumComposition, D₀, Dₗ, Dᵣ]
        sorry
  · simp [hBᵣ, hBᵣ₀₀, hBᵣ₀₂, hBᵣ₂₀, hBᵣ₁₂, hBᵣ₂₁, Aᵣ, x₀ᵣ, x₁ᵣ, x₂ᵣ, y₀ᵣ, y₁ᵣ, y₂ᵣ, matrix3sumComposition]

/-private-/ lemma matrix3sumCanonicalSigning_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- assumptions
    ∀ hBₗ' : |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
             |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ ,
    ∀ hBᵣ' : |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
             |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ ,
    -- two just-constructed rows
    let ⟨r₀, r₁, _⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    matrix3sumBottomLeft x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ Dₗ D₀ Dᵣ = c₀ ⊗ r₀ + c₁ ⊗ r₁ :=
  sorry

/-private-/ lemma matrix3sumCanonicalSigning_D_rows {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := matrix3sumBottomLeft x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ Dₗ D₀ Dᵣ
    -- assumptions
    ∀ hBₗ' : |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
             |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ ,
    ∀ hBᵣ' : |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
             |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ ,
    -- three just-constructed rows
    let ⟨r₀, r₁, r₂⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    ∀ i, D i = r₀ ∨ D i = -r₀ ∨ D i = r₁ ∨ D i = -r₁ ∨ D i = r₂ ∨ D i = -r₂ ∨ D i = 0 :=
  sorry

/-private-/ lemma matrix3sumCanonicalSigning_D_cols {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := matrix3sumBottomLeft x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ Dₗ D₀ Dᵣ
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    ∀ j, (D · j) = 0 ∨ (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀ :=
  sorry


-- ## Total unimodularity of constituents

/-private-/ lemma matrix3sumCanonicalSigning_Aᵣ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bᵣ.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ ◫ matrix3sumBottomLeft x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ Dₗ D₀ Dᵣ).IsTotallyUnimodular :=
  sorry

/-private-/ lemma matrix3sumCanonicalSigning_Aₗ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ ⊟ matrix3sumBottomLeft x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ Dₗ D₀ Dᵣ).IsTotallyUnimodular := by
  sorry
