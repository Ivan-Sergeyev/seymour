import Seymour.Matroid.Sum3Helper


-- ## Convenient API

private lemma Eq.mem3₀ₗ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ₗ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ₗ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

private lemma Eq.mem3₀ᵣ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ᵣ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ᵣ {α : Type} {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α} (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)


-- ## 3-sum of matrices

/-- The 3-sum composition of two matrices. -/
noncomputable def Matrix.ThreeSum {F : Type} [Field F] {α : Type} [DecidableEq α] {x₀ x₁ x' y₀ y₁ y' : α} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ : Matrix Xₗ Yₗ F) (Bᵣ : Matrix Xᵣ Yᵣ F) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x'}).Elem) ((Yₗ \ {y'}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) F × Prop :=
  -- row membership
  let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
  let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
  let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
  let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
  let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
  let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
  -- column membership
  let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
  let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
  let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
  let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
  let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
  let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
  -- top left submatrix
  let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem F := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem F := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- pieces of bottom left submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) F := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) F := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
  let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem F :=
    ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
  let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) F :=
    Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
  let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem F := Dᵣ * D₀ₗ⁻¹ * Dₗ
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) F := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
  -- reindexing for bottom left submatrix
  let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := j
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  -- final bottom left submatrix
  let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem F := D'.submatrix fᵣ fₗ
  -- actual definition
  ⟨
    -- 3-sum defined as a block matrix
    ⊞ Aₗ 0 D Aᵣ,
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x' ∧ x₁ ≠ x') ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y' ∧ y₁ ≠ y'))
    -- index sets of rows and columns do not overlap
    ∧ (Xₗ ⫗ Yₗ ∧ Xₗ ⫗ Yᵣ ∧ Xᵣ ⫗ Yₗ ∧ Xᵣ ⫗ Yᵣ)
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ D₀ₗ = D₀ᵣ
    -- `D₀` has the correct form
    ∧ (D₀ₗ = 1 ∨ D₀ₗ = !![1, 1; 0, 1])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Bₗ x₀ₗ y'ₗ = 1
    ∧ Bₗ x₁ₗ y'ₗ = 1
    ∧ Bₗ x'ₗ y₀ₗ = 1
    ∧ Bₗ x'ₗ y₁ₗ = 1
    ∧ (∀ x, ∀ hx : x ∈ Xₗ, x ≠ x₀ ∧ x ≠ x₁ → Bₗ ⟨x, hx⟩ y'ₗ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Bᵣ x₀ᵣ y'ᵣ = 1
    ∧ Bᵣ x₁ᵣ y'ᵣ = 1
    ∧ Bᵣ x'ᵣ y₀ᵣ = 1
    ∧ Bᵣ x'ᵣ y₁ᵣ = 1
    ∧ (∀ y, ∀ hy : y ∈ Yᵣ, y ≠ y₀ ∧ y ≠ y₁ → Bᵣ x'ᵣ ⟨y, hy⟩ = 0)
  ⟩


-- ## 3-sum of standard representations

/-- The 3-sum composition of two binary matroids given by their stanard representations. -/
noncomputable def standardReprThreeSum {α : Type} [DecidableEq α] {x₀ x₁ x' y₀ y₁ y' : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x'}),
      (Sₗ.Y \ {y'}) ∪ (Sᵣ.Y \ {y₀, y₁}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (
        -- let _ := fun i => Classical.propDecidable (i = x₀);
        (Matrix.ThreeSum Sₗ.A Sᵣ.A hXX hYY).fst.toMatrixUnionUnion),
      inferInstance,
      inferInstance,
      inferInstance,
      inferInstance,
    ⟩,
    (Matrix.ThreeSum Sₗ.A Sᵣ.A hXX hYY).snd
  ⟩

lemma standardReprThreeSum_X {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardReprThreeSum hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x'}) :=
  rfl

lemma standardReprThreeSum_Y {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardReprThreeSum hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y'}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
  rfl

lemma standardReprThreeSum_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.A.HasTuSigning) (hSᵣ : Sᵣ.A.HasTuSigning) :
    (standardReprThreeSum hXX hYY hXY hYX).fst.A.HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  -- use matrix3sumComposition_toCanonicalSigning
  sorry


-- ## 3-sum of matroids

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `Mₗ` and `Mᵣ`. -/
structure Matroid.IsThreeSumOf {α : Type} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) where
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Fintype Sₗ.Y
  hSᵣ : Fintype Sᵣ.Y
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : Sₗ.X ∩ Sᵣ.X = {x₁, x₂, x₃}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₁, y₂, y₃}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hMₗ : Mₗ = Sₗ.toMatroid
  hMᵣ : Mᵣ = Sᵣ.toMatroid
  hM : M = (standardReprThreeSum hXX hYY hXY hYX).fst.toMatroid
  IsValid : (standardReprThreeSum hXX hYY hXY hYX).snd

noncomputable instance Matroid.IsThreeSumOf.finY {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} (hM : M.IsThreeSumOf Mₗ Mᵣ) :
    Fintype (standardReprThreeSum hM.hXX hM.hYY hM.hXY hM.hYX).fst.Y :=
  have := hM.hSₗ
  have := hM.hSᵣ
  Fintype.ofFinite ↑(hM.Sₗ.Y \ {hM.y₃} ∪ hM.Sᵣ.Y \ (hM.y₁ ᕃ {hM.y₂}))

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsThreeSumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.IsThreeSumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finY
  obtain ⟨Sₗ, Sᵣ, hSₗ, hSᵣ, x₁, x₂, x₃, y₁, y₂, y₃, hXX, hYY, hXY, hYX, rfl, rfl, rfl, IsValid⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardReprThreeSum_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
