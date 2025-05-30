import Seymour.Matroid.Operations.Sum3.CanonicalSigning


/-- Captures definition 49. -/
/-private-/ structure matrix3sumLike (α : Type) where
  (Xₗ Yₗ Xᵣ Yᵣ : Set α)
  (c₀ c₁ : Xᵣ → ℚ)
  Aₗ : Matrix Xₗ Yₗ ℚ
  Aᵣ : Matrix Xᵣ Yᵣ ℚ
  D : Matrix Xᵣ Yₗ ℚ
  hAₗ : (Aₗ ⊟ D).IsTotallyUnimodular
  hAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular
  hD : ∀ j, (D · j) = 0 ∨ (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀

/-private-/ abbrev matrix3sumLike.matrix {α : Type} (C : matrix3sumLike α) :
    Matrix (C.Xₗ ⊕ C.Xᵣ) (C.Yₗ ⊕ C.Yᵣ) ℚ :=
  ⊞ C.Aₗ 0 C.D C.Aᵣ

def matrix3sumLike.pivotTopLeft {α : Type} [DecidableEq α] (C : matrix3sumLike α) {x : C.Xₗ} {y : C.Yₗ} (hxy : C.Aₗ x y ≠ 0) :
    matrix3sumLike α :=
  ⟨
    C.Xₗ, C.Yₗ, C.Xᵣ, C.Yᵣ,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
  ⟩

lemma matrix3sumLike.pivotTopLeft_eq {α : Type} [DecidableEq α] (C : matrix3sumLike α) {x : C.Xₗ} {y : C.Yₗ} (hxy : C.Aₗ x y ≠ 0) :
    (C.pivotTopLeft hxy).matrix = C.matrix.shortTableauPivot sorry sorry :=
  sorry

/-- Captures lemma 52. -/
/-private-/ lemma matrix3sumLike_TU {α : Type} (C : matrix3sumLike α) :
    C.matrix.IsTotallyUnimodular :=
  sorry


noncomputable def matrix3sum.matrix3sumLike {α : Type} [DecidableEq α] (S : matrix3sum α ℚ) : matrix3sumLike α :=
  ⟨
    S.XAₗ, S.YAₗ, S.XAᵣ, S.YAᵣ,
    sorry,
    sorry,
    S.Aₗ,
    S.Aᵣ,
    S.D,
    sorry,
    sorry,
    sorry,
  ⟩

lemma matrix3sum.Is3sumLike {α : Type} [DecidableEq α] (S : matrix3sum α ℚ) :
    S.Composition = (S.matrix3sumLike).matrix :=
  sorry


/-- Captures lemma 53. -/
/-private-/ lemma matrix3sumCanonicalSigning_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ ℚ} {Bᵣ : Matrix Xᵣ Yᵣ ℚ} (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ : Bₗ.IsTotallyUnimodular) (hBᵣ : Bᵣ.IsTotallyUnimodular) :
    -- TODO propagate the necessary assumptions from `standardRepr3sumComposition.snd`
    (matrix3sumCanonicalSigning Bₗ Bᵣ hXX hYY).IsTotallyUnimodular := by
  sorry

/-- Special function application that binds tighter than anything else. -/
local notation:max f:max"⁀"a:max => f a

lemma matrix3sum.fromStandardRepr_HasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂})
    (hBₗ : Sₗ.B.HasTuSigning) (hBᵣ : Sᵣ.B.HasTuSigning) (h : (matrix3sum.fromStandardRepr hXX hYY).HasFormInter₀₁) :
    (matrix3sum.fromStandardRepr hXX hYY).Composition.HasTuSigning :=
  sorry

lemma matrix3sumComposition_hasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ Z2} {Bᵣ : Matrix Xᵣ Yᵣ Z2}
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ)
    (hBₗ : Bₗ.HasTuSigning) (hBᵣ : Bᵣ.HasTuSigning) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- extract submatrices
    let Aₗ := Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- the necessary parts of "validity" of the 3-sum
    Bₗ x₀ₗ y₀ₗ = 1 →
    Bₗ x₀ₗ y₂ₗ = 1 →
    Bₗ x₂ₗ y₀ₗ = 1 →
    Bₗ x₁ₗ y₂ₗ = 1 →
    Bₗ x₂ₗ y₁ₗ = 1 →
    Bᵣ x₀ᵣ y₀ᵣ = 1 →
    Bᵣ x₀ᵣ y₂ᵣ = 1 →
    Bᵣ x₂ᵣ y₀ᵣ = 1 →
    Bᵣ x₁ᵣ y₂ᵣ = 1 →
    Bᵣ x₂ᵣ y₁ᵣ = 1 →
    -- the actual statement
    (matrix3sumComposition x₀ₗ x₁ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ).HasTuSigning := by
  obtain ⟨Aₗ, hABₗ⟩ := hBₗ
  obtain ⟨Aᵣ, hABᵣ⟩ := hBᵣ
  rw [Matrix.isTuSigningOf_iff] at hABₗ hABᵣ
  obtain ⟨hAₗ, rfl⟩ := hABₗ
  obtain ⟨hAᵣ, rfl⟩ := hABᵣ
  exact (⟨
    matrix3sumCanonicalSigning Aₗ Aᵣ hXX hYY,
    matrix3sumCanonicalSigning_isTotallyUnimodular hXX hYY hAₗ hAᵣ,
    matrix3sumCanonicalSigning_isSigningOf_matrix3sumComposition hXX hYY hAₗ.apply hAᵣ.apply
      hAₗ.apply_abs_eq_one⁀·
      hAₗ.apply_abs_eq_one⁀·
      hAₗ.apply_abs_eq_one⁀·
      hAₗ.apply_abs_eq_one⁀·
      hAₗ.apply_abs_eq_one⁀·
      hAᵣ.apply_abs_eq_one⁀·
      hAᵣ.apply_abs_eq_one⁀·
      hAᵣ.apply_abs_eq_one⁀·
      hAᵣ.apply_abs_eq_one⁀·
      hAᵣ.apply_abs_eq_one⁀·
  ⟩)
