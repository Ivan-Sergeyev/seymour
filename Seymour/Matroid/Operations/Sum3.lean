import Seymour.Matroid.Notions.Regularity
import Seymour.Matrix.PreTUness


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
noncomputable abbrev matrix3sumComposition {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
    (D₀ : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
    Matrix (X₁ ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ Y₂) β :=
  -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
  let D₁₂ : Matrix X₂ Y₁ β := D₂ * D₀⁻¹ * D₁
  Matrix.fromBlocks A₁ 0 (Matrix.fromBlocks D₁ D₀ D₁₂ D₂) A₂

-- /-- `Matrix`-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
-- noncomputable abbrev matrix3sumComposition {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
--     (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
--     (z₁ : Y₁ → β) (z₂ : X₂ → β) (D : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
--     Matrix ((X₁ ⊕ Unit) ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ (Unit ⊕ Y₂)) β :=
--   -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
--   let D₁₂ : Matrix X₂ Y₁ β := D₂ * D⁻¹ * D₁
--   Matrix.fromBlocks
--     (Matrix.fromRows A₁ (Matrix.replicateRow Unit (Sum.elim z₁ ![1, 1]))) 0
--     (Matrix.fromBlocks D₁ D D₁₂ D₂) (Matrix.fromCols (Matrix.replicateCol Unit (Sum.elim ![1, 1] z₂)) A₂)

/-- `StandardRepr`-level 3-sum of two matroids.
    The second part checks legitimacy (invertibility of a certain 2x2 submatrix and
    specific `1`s and `0`s on concrete positions). -/
noncomputable def standardRepr3sumComposition {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    StandardRepr α Z2 × Prop :=
  have hxxx₁ : {x₁, x₂, x₃} ⊆ S₁.X := hXX.symm.subset.trans Set.inter_subset_left
  have hxxx₂ : {x₁, x₂, x₃} ⊆ S₂.X := hXX.symm.subset.trans Set.inter_subset_right
  have hyyy₁ : {y₁, y₂, y₃} ⊆ S₁.Y := hYY.symm.subset.trans Set.inter_subset_left
  have hyyy₂ : {y₁, y₂, y₃} ⊆ S₂.Y := hYY.symm.subset.trans Set.inter_subset_right
  have x₁inX₁ : x₁ ∈ S₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
  have x₁inX₂ : x₁ ∈ S₂.X := hxxx₂ (Set.mem_insert x₁ {x₂, x₃})
  have x₂inX₁ : x₂ ∈ S₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₂inX₂ : x₂ ∈ S₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₃inX₁ : x₃ ∈ S₁.X := hxxx₁ (by simp)
  have x₃inX₂ : x₃ ∈ S₂.X := hxxx₂ (by simp)
  have y₁inY₁ : y₁ ∈ S₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
  have y₁inY₂ : y₁ ∈ S₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
  have y₂inY₁ : y₂ ∈ S₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₂inY₂ : y₂ ∈ S₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₃inY₁ : y₃ ∈ S₁.Y := hyyy₁ (by simp)
  have y₃inY₂ : y₃ ∈ S₂.Y := hyyy₂ (by simp)
  -- The actual definition starts here:
  let A₁ₗ : Matrix (S₁.X \ {x₂, x₃}).Elem (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 :=
    Matrix.of (fun i j => S₁.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let A₁ᵣ : Matrix (S₁.X \ {x₂, x₃}).Elem (Fin 2) Z2 :=
    Matrix.of (fun i j => S₁.B ⟨i, Set.mem_of_mem_diff i.property⟩ (![⟨y₁, y₁inY₁⟩, ⟨y₂, y₂inY₁⟩] j))
  let A₁ : Matrix (S₁.X \ {x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    Matrix.fromCols A₁ₗ A₁ᵣ
  let A₂ₗ : Matrix (Fin 2) (S₂.Y \ {y₁, y₂}).Elem Z2 :=
    Matrix.of (fun i j => S₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let A₂ᵣ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (S₂.Y \ {y₁, y₂}).Elem Z2 :=
    Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂}).Elem Z2 := -- the bottom right submatrix
    Matrix.fromRows A₂ₗ A₂ᵣ
  let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
    Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₁, y₁inY₁⟩, ⟨y₂, y₂inY₁⟩] j))
  let D_₂ : Matrix (Fin 2) (Fin 2) Z2 := -- the middle left 2x2 submatrix
    Matrix.of (fun i j => S₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₁, y₁inY₂⟩, ⟨y₂, y₂inY₂⟩] j))
  let D₁ : Matrix (Fin 2) (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let D₂ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₁, y₁inY₂⟩, ⟨y₂, y₂inY₂⟩] j))
  ⟨
    ⟨
      (S₁.X \ {x₂, x₃}) ∪ (S₂.X \ {x₁}),
      (S₁.Y \ {y₃}) ∪ (S₂.Y \ {y₁, y₂}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨
          ⟨S₁.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, S₂.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩
        ⟩,
      Matrix.of (fun i j =>
        matrix3sumComposition A₁ A₂ D_₁ D₁ D₂ (
          if hi₁ : i.val ∈ S₁.X \ {x₂, x₃} then ◩⟨i, hi₁⟩ else
          if hi₂ : i.val ∈ S₂.X \ {x₁, x₂, x₃} then ◪◪⟨i, hi₂⟩ else
          if hx₂ : i.val = x₂ then ◪◩0 else
          if hx₃ : i.val = x₃ then ◪◩1 else
          False.elim (by aesop) -- todo: refactor - there's probably an easier way to prove this
          -- sorry -- use instead of aesop for faster compilation
          -- old version: (i.property.elim hi₁ (by simp_all)).elim
        ) (
          if hj₁ : j.val ∈ S₁.Y \ {y₁, y₂, y₃} then ◩◩⟨j, hj₁⟩ else
          if hj₂ : j.val ∈ S₂.Y \ {y₁, y₂} then ◪⟨j, hj₂⟩ else
          if hy₁ : j.val = y₁ then ◩◪0 else
          if hy₂ : j.val = y₂ then ◩◪1 else
          False.elim (by aesop) -- todo: refactor - there's probably an easier way to prove this
          -- sorry -- use instead of aesop for faster compilation
          -- old version: (j.property.elim (by simp_all) hj₂).elim
        )
      ),
      inferInstance,
      inferInstance,
    ⟩,
    IsUnit D_₁ ∧ D_₁ = D_₂ -- the matrix `D_₁ = D_₂` (called D-bar in the book) is invertible
    ∧ S₁.B ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩ = 1
    ∧ S₁.B ⟨x₁, x₁inX₁⟩ ⟨y₂, y₂inY₁⟩ = 1
    ∧ S₁.B ⟨x₂, x₂inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ S₁.B ⟨x₃, x₃inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ S₂.B ⟨x₁, x₁inX₂⟩ ⟨y₁, y₁inY₂⟩ = 1
    ∧ S₂.B ⟨x₁, x₁inX₂⟩ ⟨y₂, y₂inY₂⟩ = 1
    ∧ S₂.B ⟨x₂, x₂inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ S₂.B ⟨x₃, x₃inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ S₁.X, x ≠ x₂ ∧ x ≠ x₃ → S₁.B ⟨x, hx⟩ ⟨y₃, y₃inY₁⟩ = 0) -- the rest of the rightmost column is `0`s
    ∧ (∀ y : α, ∀ hy : y ∈ S₂.Y, y ≠ y₂ ∧ y ≠ y₁ → S₂.B ⟨x₁, x₁inX₂⟩ ⟨y, hy⟩ = 0) -- the rest of the topmost row is `0`s
  ⟩

/-- Binary matroid `M` is a result of 3-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is3sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  S : StandardRepr α Z2
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  hS₁ : Finite S₁.X
  hS₂ : Finite S₂.X
  hM : S.toMatroid = M
  hM₁ : S₁.toMatroid = M₁
  hM₂ : S₂.toMatroid = M₂
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}
  hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}
  hXY : S₁.X ⫗ S₂.Y
  hYX : S₁.Y ⫗ S₂.X
  IsSum : (standardRepr3sumComposition hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition hXX hYY hXY hYX).snd

lemma standardRepr3sumComposition_X {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = (S₁.X \ {x₂, x₃}) ∪ (S₂.X \ {x₁}) :=
  rfl

lemma standardRepr3sumComposition_Y {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = (S₁.Y \ {y₃}) ∪ (S₂.Y \ {y₁, y₂}) :=
  rfl

local macro "finish3B" : tactic => `(tactic| simp_all [standardRepr3sumComposition, Equiv.sumAssoc, Matrix.toMatrixUnionUnion])

set_option maxHeartbeats 6000000 in
lemma standardRepr3sumComposition_B {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B =
    have hxxx₁ : {x₁, x₂, x₃} ⊆ S₁.X := hXX.symm.subset.trans Set.inter_subset_left
    have hxxx₂ : {x₁, x₂, x₃} ⊆ S₂.X := hXX.symm.subset.trans Set.inter_subset_right
    have hyyy₁ : {y₁, y₂, y₃} ⊆ S₁.Y := hYY.symm.subset.trans Set.inter_subset_left
    have hyyy₂ : {y₁, y₂, y₃} ⊆ S₂.Y := hYY.symm.subset.trans Set.inter_subset_right
    have x₁inX₁ : x₁ ∈ S₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
    have x₁inX₂ : x₁ ∈ S₂.X := hxxx₂ (Set.mem_insert x₁ {x₂, x₃})
    have x₂inX₁ : x₂ ∈ S₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    have x₂inX₂ : x₂ ∈ S₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    have x₃inX₁ : x₃ ∈ S₁.X := hxxx₁ (by simp)
    have x₃inX₂ : x₃ ∈ S₂.X := hxxx₂ (by simp)
    have y₁inY₁ : y₁ ∈ S₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
    have y₁inY₂ : y₁ ∈ S₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
    have y₂inY₁ : y₂ ∈ S₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    have y₂inY₂ : y₂ ∈ S₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    have y₃inY₁ : y₃ ∈ S₁.Y := hyyy₁ (by simp)
    have y₃inY₂ : y₃ ∈ S₂.Y := hyyy₂ (by simp)
    -- The actual definition starts here:
    let A₁ₗ : Matrix (S₁.X \ {x₂, x₃}).Elem (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 :=
      Matrix.of (fun i j => S₁.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let A₁ᵣ : Matrix (S₁.X \ {x₂, x₃}).Elem (Fin 2) Z2 :=
      Matrix.of (fun i j => S₁.B ⟨i, Set.mem_of_mem_diff i.property⟩ (![⟨y₁, y₁inY₁⟩, ⟨y₂, y₂inY₁⟩] j))
    let A₁ : Matrix (S₁.X \ {x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
      Matrix.fromCols A₁ₗ A₁ᵣ
    let A₂ₗ : Matrix (Fin 2) (S₂.Y \ {y₁, y₂}).Elem Z2 :=
      Matrix.of (fun i j => S₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let A₂ᵣ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (S₂.Y \ {y₁, y₂}).Elem Z2 :=
      Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂}).Elem Z2 := -- the bottom right submatrix
      Matrix.fromRows A₂ₗ A₂ᵣ
    let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
      Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₁, y₁inY₁⟩, ⟨y₂, y₂inY₁⟩] j))
    let D_₂ : Matrix (Fin 2) (Fin 2) Z2 := -- the middle left 2x2 submatrix
      Matrix.of (fun i j => S₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₁, y₁inY₂⟩, ⟨y₂, y₂inY₂⟩] j))
    let D₁ : Matrix (Fin 2) (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
      Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let D₂ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
      Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₁, y₁inY₂⟩, ⟨y₂, y₂inY₂⟩] j))
    ((matrix3sumComposition A₁ A₂ D_₁ D₁ D₂).submatrix
      (Sum.map id (fun i : (S₂.X \ {x₁}).Elem =>
          if hx₂ : i.val = x₂ then ◩0 else
          if hx₃ : i.val = x₃ then ◩1 else
          ◪⟨i, by obtain ⟨_, _⟩ := i; simp_all; simp_all⟩)
      )
      (Sum.map (fun j : (S₁.Y \ {y₃}).Elem =>
          if hy₁ : j.val = y₁ then ◪0 else
          if hy₂ : j.val = y₂ then ◪1 else
          ◩⟨j, by obtain ⟨_, _⟩ := j; simp_all; simp_all⟩)
          id
      )
    ).toMatrixUnionUnion
    := by sorry
  -- have hX := standardRepr3sumComposition_X hXX hYY hXY hYX
  -- have hY := standardRepr3sumComposition_Y hXX hYY hXY hYX
  -- ext i j
  -- if hi : i.val ∈ S₂.X then
  --   if hix₁ : i = x₁ then
  --     if hj : j.val ∈ S₁.Y then
  --       if hjy₁ : j = y₁ then
  --         finish3B
  --       else if hjy₂ : j = y₂ then
  --         finish3B
  --       else if hjy₃ : j = y₃ then
  --         finish3B
  --       else
  --         finish3B
  --     else
  --       have hjY₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃}
  --       · exact in_of_in_union_of_ni_left j.property hj
  --       finish3B
  --   else if hix₂ : i = x₂ then
  --     if hj : j.val ∈ S₁.Y then
  --       if hjy₁ : j = y₁ then
  --         finish3B
  --       else if hjy₂ : j = y₂ then
  --         finish3B
  --       else if hjy₃ : j = y₃ then
  --         finish3B
  --       else
  --         finish3B
  --     else
  --       have hjY₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃}
  --       · exact in_of_in_union_of_ni_left j.property hj
  --       finish3B
  --   else if hix₃ : i = x₃ then
  --     if hj : j.val ∈ S₁.Y then
  --       if hjy₁ : j = y₁ then
  --         finish3B
  --       else if hjy₂ : j = y₂ then
  --         finish3B
  --       else if hjy₃ : j = y₃ then
  --         finish3B
  --       else
  --         finish3B
  --     else
  --       have hjY₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃}
  --       · exact in_of_in_union_of_ni_left j.property hj
  --       finish3B
  --   else
  --     have hiX₂ : i.val ∈ S₂.X \ {x₁, x₂, x₃}
  --     · simp [*]
  --     have hiX₁ : i.val ∉ S₁.X
  --     · exact ni_of_in_wo_of_inter_right hXX hiX₂
  --     if hj : j.val ∈ S₁.Y then
  --       if hjy₁ : j = y₁ then
  --         finish3B
  --       else if hjy₂ : j = y₂ then
  --         finish3B
  --       else if hjy₃ : j = y₃ then
  --         finish3B
  --       else
  --         finish3B
  --     else
  --       have hjY₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃}
  --       · exact in_of_in_union_of_ni_left j.property hj
  --       finish3B
  -- else
  --   have hiX₁ : i.val ∈ S₁.X \ {x₁, x₂, x₃}
  --   · exact in_of_in_union_of_ni_right i.property hi
  --   if hj : j.val ∈ S₁.Y then
  --     if hjy₁ : j = y₁ then
  --       finish3B
  --     else if hjy₂ : j = y₂ then
  --       finish3B
  --     else if hjy₃ : j = y₃ then
  --       finish3B
  --     else
  --       finish3B
  --   else
  --     have hjY₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃}
  --     · exact in_of_in_union_of_ni_left j.property hj
  --     finish3B

instance Matroid.Is3sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_X]
  apply Finite.Set.finite_union

lemma standardRepr3sumComposition_hasTuSigning {α : Type} [DecidableEq α] {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.HasTuSigning := by
  -- invoke `matrix3sumComposition_toCanonicalSigning_TU`
  sorry

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  -- invoke `standardRepr3sumComposition_hasTuSigning`
  sorry

section AuxiliaryLemmas

-- lemma 14 in the write-up
lemma Matrix.Z2_2x2_nonsingular_form (A : Matrix (Fin 2) (Fin 2) Z2) (hA : IsUnit A) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, A.submatrix f g = 1 ∨ A.submatrix f g = !![1, 1; 0, 1] := by
  sorry

-- recipe for flipping signs in 3 × 3 matrix, works in both cases!
def Matrix.toCanonicalSigning_3x3_constructive (A : Matrix (Fin 3) (Fin 3) ℚ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  ⟨![1, A 0 0 * A 1 0, A 0 0 * A 1 0 * A 1 2 * A 2 2], ![A 0 0, A 0 1, A 0 0 * A 1 0 * A 1 2]⟩

-- lemma 15 in the write-up
-- todo: make constructive (definition with explicit formula?)
lemma Matrix.toCanonicalSigning_3x3₁ (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA : A.IsTuSigningOf (!![1, 1, 0; 1, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) Z2)) :
    ∃ x : Fin 3 → ℚ, ∃ y : Fin 3 → ℚ,
    ∀ i j, A i j * x i * y j = !![1, 1, 0; 1, 0, 1; 0, -1, 1] i j := by
  sorry

-- lemma 16 in the write-up
-- todo: make constructive (definition with explicit formula?)
lemma Matrix.toCanonicalSigning_3x3₂ (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA : A.IsTuSigningOf (!![1, 1, 0; 1, 1, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) Z2)) :
    ∃ x : Fin 3 → ℚ, ∃ y : Fin 3 → ℚ,
    ∀ i j, A i j * x i * y j = !![1, 1, 0; 1, 1, 1; 0, 1, 1] i j := by
  sorry

lemma Matrix.toCanonicalSigning_3x3_constructive₁ (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA : A.IsTuSigningOf (!![1, 1, 0; 1, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) Z2)) :
    let x := A.toCanonicalSigning_3x3_constructive.fst;
    let y := A.toCanonicalSigning_3x3_constructive.snd;
    ∀ i j, A i j * x i * y j = !![1, 1, 0; 1, 0, 1; 0, -1, 1] i j := by
  sorry

lemma Matrix.toCanonicalSigning_3x3_constructive₂ (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hA : A.IsTuSigningOf (!![1, 1, 0; 1, 1, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) Z2)) :
    let x := A.toCanonicalSigning_3x3_constructive.fst;
    let y := A.toCanonicalSigning_3x3_constructive.snd;
    ∀ i j, A i j * x i * y j = !![1, 1, 0; 1, 1, 1; 0, 1, 1] i j := by
  sorry

-- possible refactor: reinstate `β`
def matrix3sumComposition_B₁ {X₁ Y₁ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) :
    Matrix (X₁ ⊕ (Fin 2)) ((Y₁ ⊕ Fin 2) ⊕ Fin 1) ℚ :=
  Matrix.fromBlocks A₁ 0 (Matrix.fromCols D₁ D₀) !![1; 1]

def matrix3sumComposition_B₂ {X₂ Y₂ : Set α}
    (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ) :
    Matrix (Fin 1 ⊕ (Fin 2 ⊕ X₂)) (Fin 2 ⊕ Y₂) ℚ :=
  Matrix.fromBlocks !![1, 1] 0 (Matrix.fromRows D₀ D₂) A₂

noncomputable def matrix3sumComposition_toCanonicalSigning {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂) :
    Matrix (X₁ ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ Y₂) ℚ
    :=
    -- get multiplication factors to get 3×3 matrix containing `D₀` to canonical form
    let D₀_ext := !![A₁ x₁ ◪0, A₁ x₁ ◪1, 0; D₀ 0 0, D₀ 0 1, A₂ ◩0 y₃; D₀ 1 0, D₀ 1 1, A₂ ◩1 y₃];
    let D₀_row_mult := D₀_ext.toCanonicalSigning_3x3_constructive.fst;
    let D₀_col_mult := D₀_ext.toCanonicalSigning_3x3_constructive.snd;
    -- extend multiplication factors to vectors over corresponding domains
    let A₁_row_mult : X₁ → ℚ := fun i => if i = x₁ then D₀_row_mult 0 else 1;
    let A₁_col_mult : Y₁ ⊕ Fin 2 → ℚ := fun j => j.casesOn 1 ![D₀_col_mult 0, D₀_col_mult 1];
    let A₂_row_mult : Fin 2 ⊕ X₂ → ℚ := fun i => i.casesOn ![D₀_row_mult 1, D₀_row_mult 2] 1;
    let A₂_col_mult : Y₂ → ℚ := fun j => if j = y₃ then D₀_col_mult 2 else 1;
    -- apply multiplication factors to all matrices
    let A₁' := Matrix.of (fun i j => A₁ i j * A₁_row_mult i * A₁_col_mult j);
    let A₂' := Matrix.of (fun i j => A₂ i j * A₂_row_mult i * A₂_col_mult j);
    let D₀' := Matrix.of (fun i j => D₀ i j * D₀_row_mult i * D₀_col_mult j);
    let D₁' := Matrix.of (fun i j => D₁ i j * ![D₀_row_mult 1, D₀_row_mult 2] i);
    let D₂' := Matrix.of (fun i j => D₂ i j * ![D₀_col_mult 0, D₀_col_mult 1] j);
    -- manually define signing for bottom left corner
    let D₁₂' := D₂' * D₀⁻¹ * D₁';
    -- compose signed matrix
    Matrix.fromBlocks A₁' 0 (Matrix.fromBlocks D₁' D₀' D₁₂' D₂') A₂'

-- note: this is probably unnecessary, as we obtain TU signings of all submatrices from TU signings of B₁ and B₂
private def Matrix.IsSigningOf {X Y : Type} (A : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  ∀ i j, |A i j| = (U i j).val

private lemma Matrix.IsTuSigningOf.isSigningOf {X Y : Type} {A : Matrix X Y ℚ} {n : ℕ} {U : Matrix X Y (ZMod n)}
    (hAU : A.IsTuSigningOf U) :
    A.IsSigningOf U :=
  hAU.right

lemma matrix3sumComposition_toCanonicalSigning_isSigning {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) Z2) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ Z2)
    (D₀ : Matrix (Fin 2) (Fin 2) Z2) (D₁ : Matrix (Fin 2) Y₁ Z2) (D₂ : Matrix X₂ (Fin 2) Z2)
    (x₁ : X₁) (y₃ : Y₂)
    :
    ∀ A₁' A₂' D₀' D₁' D₂',
    A₁'.IsSigningOf A₁ →
    A₂'.IsSigningOf A₂ →
    D₀'.IsSigningOf D₀ →
    D₁'.IsSigningOf D₁ →
    D₂'.IsSigningOf D₂ →
    (matrix3sumComposition_toCanonicalSigning A₁' A₂' D₀' D₁' D₂' x₁ y₃).support = matrix3sumComposition A₁ A₂ D₀ D₁ D₂
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_A₁_TU {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).toBlocks₁₁.IsTotallyUnimodular
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_D_TU {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).toBlocks₂₁.IsTotallyUnimodular
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_zero {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).toBlocks₁₂ = 0
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_A₂_TU {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).toBlocks₂₂.IsTotallyUnimodular
    := by
  sorry

-- definition of d-tilde (and e-tilde)
-- lemma about columns of D being copies of d-tilde, a-tilde, b-tilde up to multiplication by 0, ±1
-- lemma about columns of D remaining copies of d-tilde, a-tilde, b-tilde up to multiplication by 0, ±1 after pivot in A₁
-- lemmas about structure of B after pivoting

lemma matrix3sumComposition_toCanonicalSigning_PreTU_1 {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).IsPreTU 1
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_PreTU_2 {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).IsPreTU 2
    := by
  sorry

lemma matrix3sumComposition_toCanonicalSigning_TU {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
    (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ)
    (x₁ : X₁) (y₃ : Y₂)
    (hD₀ : D₀.IsTuSigningOf (1 : Matrix (Fin 2) (Fin 2) Z2) ∨
           D₀.IsTuSigningOf (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) Z2))
    (hB₁ : (matrix3sumComposition_B₁ A₁ D₀ D₁).IsTotallyUnimodular)
    (hB₂ : (matrix3sumComposition_B₂ A₂ D₀ D₂).IsTotallyUnimodular) :
    (matrix3sumComposition_toCanonicalSigning A₁ A₂ D₀ D₁ D₂ x₁ y₃).IsTotallyUnimodular
    := by
  sorry
  -- todo: inductive proof of PreTUness for every `k`

end AuxiliaryLemmas
