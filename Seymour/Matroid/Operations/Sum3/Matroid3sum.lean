import Seymour.Matroid.Operations.Sum3.MatrixFamily


variable {α : Type} [DecidableEq α]

noncomputable def standardRepr3sumComposition {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  -- extracting submatrices
  let Aₗ := Sₗ.B.Aₗ x₀ₗ x₁ₗ y₂ₗ
  let Dₗ := Sₗ.B.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let D₀ := Sₗ.B.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dᵣ := Sᵣ.B.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  let Aᵣ := Sᵣ.B.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  ⟨
    ⟨
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      -- the standard representation matrix
      (matrix3sumComposition x₀ₗ x₁ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ D₀ = Sᵣ.B.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    -- `D₀` has the correct form
    ∧ (D₀ = 1 ∨ D₀ = !![1, 1; 0, 1])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Sₗ.B x₀ₗ y₂ₗ = 1
    ∧ Sₗ.B x₁ₗ y₂ₗ = 1
    ∧ Sₗ.B x₂ₗ y₀ₗ = 1
    ∧ Sₗ.B x₂ₗ y₁ₗ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ y₂ₗ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Sᵣ.B x₀ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₁ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₀ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₁ᵣ = 1
    ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B x₂ᵣ ⟨y, hy⟩ = 0)
  ⟩

lemma standardRepr3sumComposition_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x₂}) :=
  rfl

lemma standardRepr3sumComposition_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y₂}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
  rfl

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `Mₗ` and `Mᵣ`. -/
structure Matroid.Is3sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : Sₗ.X ∩ Sᵣ.X = {x₁, x₂, x₃}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₁, y₂, y₃}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr3sumComposition hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_X]
  apply Finite.Set.finite_union

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
    -- TODO propagate the necessary assumptions from `standardRepr3sumComposition.snd`
    (matrix3sumComposition x₀ₗ x₁ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ₗ y₁ₗ y₂ₗ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ).HasTuSigning := by
  obtain ⟨Aₗ, hABₗ⟩ := hBₗ
  obtain ⟨Aᵣ, hABᵣ⟩ := hBᵣ
  rw [Matrix.isTuSigningOf_iff] at hABₗ hABᵣ
  obtain ⟨hAₗ, hBAₗ⟩ := hABₗ
  obtain ⟨hAᵣ, hBAᵣ⟩ := hABᵣ
  symm at hBAₗ hBAᵣ
  use matrix3sumCanonicalSigning Aₗ Aᵣ hXX hYY, matrix3sumCanonicalSigning_isTotallyUnimodular Aₗ Aᵣ hXX hYY
  convert matrix3sumCanonicalSigning_isSigningOf_matrix3sumComposition Aₗ Aᵣ hXX hYY

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B.HasTuSigning := by
  -- TODO extract assumptions from `hSS` and plug them below
  obtain ⟨B, hB, hBBB⟩ := matrix3sumComposition_hasTuSigning hXX hYY hXY hYX hSₗ hSᵣ --hSS
  refine ⟨B.toMatrixUnionUnion, hB.toMatrixUnionUnion, fun i j => ?_⟩
  cases hi : i.toSum with
  | inl iₗ =>
    specialize hBBB ◩iₗ
    cases hj : j.toSum with
    | inl jₗ =>
      specialize hBBB ◩jₗ
      rwa [←hi, ←hj] at hBBB
    | inr jᵣ =>
      specialize hBBB ◪jᵣ
      rwa [←hi, ←hj] at hBBB
  | inr iᵣ =>
    specialize hBBB ◪iᵣ
    cases hj : j.toSum with
    | inl jₗ =>
      specialize hBBB ◩jₗ
      rwa [←hi, ←hj] at hBBB
    | inr jᵣ =>
      specialize hBBB ◪jᵣ
      rwa [←hi, ←hj] at hBBB

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, hMMM⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
  · exact hMMM
