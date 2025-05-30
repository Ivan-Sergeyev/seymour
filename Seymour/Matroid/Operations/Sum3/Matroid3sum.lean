import Seymour.Matroid.Operations.Sum3.MatrixFamily


variable {α : Type} [DecidableEq α]

noncomputable def standardRepr3sumComposition {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  let S := matrix3sum.fromStandardRepr hXX hYY
  ⟨
    ⟨
      S.XAₗ ∪ S.XAᵣ,
      S.YAₗ ∪ S.YAᵣ,
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      -- the standard representation matrix
      S.Composition.toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ S.D₀ = Sᵣ.B.D₀ S.x₀ᵣ S.x₁ᵣ S.y₀ᵣ S.y₁ᵣ
    -- `D₀` has the correct form
    ∧ (S.D₀ = 1 ∨ S.D₀ = !![1, 1; 0, 1])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Sₗ.B S.x₀ₗ S.y₂ₗ = 1
    ∧ Sₗ.B S.x₁ₗ S.y₂ₗ = 1
    ∧ Sₗ.B S.x₂ₗ S.y₀ₗ = 1
    ∧ Sₗ.B S.x₂ₗ S.y₁ₗ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ S.y₂ₗ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Sᵣ.B S.x₀ᵣ S.y₂ᵣ = 1
    ∧ Sᵣ.B S.x₁ᵣ S.y₂ᵣ = 1
    ∧ Sᵣ.B S.x₂ᵣ S.y₀ᵣ = 1
    ∧ Sᵣ.B S.x₂ᵣ S.y₁ᵣ = 1
    ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B S.x₂ᵣ ⟨y, hy⟩ = 0)
  ⟩

lemma standardRepr3sumComposition_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x₂}) :=
  rfl

lemma standardRepr3sumComposition_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y₂}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
  rfl

lemma standardRepr3sumComposition_Bₗ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sₗ.B ⟨x₀, hXX.mem3₀ₗ⟩ ⟨y₀, hYY.mem3₀ₗ⟩ = 1 :=
  hSS.right.right.left.casesOn (congr_fun₂ · 0 0) (congr_fun₂ · 0 0)

lemma standardRepr3sumComposition_Bᵣ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sᵣ.B ⟨x₀, hXX.mem3₀ᵣ⟩ ⟨y₀, hYY.mem3₀ᵣ⟩ = 1 := by
  rw [←standardRepr3sumComposition_Bₗ₀₀ hXX hYY hXY hYX hSS]
  exact congr_fun₂ hSS.right.left.symm 0 0

/-- Binary matroid `M` is a result of 3-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop` but treat it as a predicate. -/
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

-- Perhaps a weaker tactic than `tauto` would suffice; enough to destruct `let`s and `and`s.
local macro "valid3sum" : tactic => `(tactic| unfold standardRepr3sumComposition at * <;> tauto)

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B.HasTuSigning := by
  obtain ⟨B, hB, hBBB⟩ :=
    matrix3sumComposition_hasTuSigning
      hXX hYY hXY hYX hSₗ hSᵣ
      (standardRepr3sumComposition_Bₗ₀₀ hXX hYY hXY hYX hSS) (by valid3sum) (by valid3sum) (by valid3sum) (by valid3sum)
      (standardRepr3sumComposition_Bᵣ₀₀ hXX hYY hXY hYX hSS) (by valid3sum) (by valid3sum) (by valid3sum) (by valid3sum)
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
