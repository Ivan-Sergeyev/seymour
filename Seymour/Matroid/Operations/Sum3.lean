import Seymour.Matroid.Operations.Sum3helper


variable {α : Type}

section experimental_lemmas
-- experimental lemmas to help state lemma 19

variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

private lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

private lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

end experimental_lemmas


variable [DecidableEq α]

section StandardMatrixDefinition

/-- The 3-sum composition of two matrices. -/
noncomputable def matrix3sumComposition_standard {F : Type} [Field F] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
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

-- todo: lemmas about parts of the correctness Prop

end StandardMatrixDefinition


section MatroidThreeSum

/-- The 3-sum composition of two binary matroids given by their stanard representations. -/
noncomputable def standardRepr3sumComposition_standard {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
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
      (matrix3sumComposition_standard Sₗ.B Sᵣ.B hXX hYY).fst.toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (matrix3sumComposition_standard Sₗ.B Sᵣ.B hXX hYY).snd
  ⟩

lemma standardRepr3sumComposition_standard_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x'}) :=
  rfl

lemma standardRepr3sumComposition_standard_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y'}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
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
  IsSum : (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition_standard hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_standard_X]
  apply Finite.Set.finite_union

lemma standardRepr3sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.B.HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  -- use matrix3sumComposition_toCanonicalSigning
  sorry

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ

end MatroidThreeSum
