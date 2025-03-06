import Seymour.Matroid.Notions.Regularity


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
noncomputable abbrev matrix3sumComposition {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
    (z₁ : Y₁ → β) (z₂ : X₂ → β) (D : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
    Matrix ((X₁ ⊕ Unit) ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ (Unit ⊕ Y₂)) β :=
  -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
  let D₁₂ : Matrix X₂ Y₁ β := D₂ * D⁻¹ * D₁
  Matrix.fromBlocks
    (Matrix.fromRows A₁ (Matrix.row Unit (Sum.elim z₁ ![1, 1]))) 0
    (Matrix.fromBlocks D₁ D D₁₂ D₂) (Matrix.fromCols (Matrix.col Unit (Sum.elim ![1, 1] z₂)) A₂)

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
  have y₃inY₁ : y₃ ∈ S₁.Y := hyyy₁ (by simp)
  have y₃inY₂ : y₃ ∈ S₂.Y := hyyy₂ (by simp)
  have y₂inY₁ : y₂ ∈ S₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₂inY₂ : y₂ ∈ S₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₁inY₁ : y₁ ∈ S₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
  have y₁inY₂ : y₁ ∈ S₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
  -- The actual definition starts here:
  let A₁ : Matrix (S₁.X \ {x₁, x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    Matrix.of (fun i j => S₁.B
        ⟨i.val, Set.mem_of_mem_diff i.property⟩
        (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩]))
  let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
    Matrix.of (fun i j => S₂.B
        (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
        ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₁ : (S₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
    (fun j => S₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₂ : (S₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
    (fun i => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
  let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
    Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))
  let D_₂ : Matrix (Fin 2) (Fin 2) Z2 := -- the middle left 2x2 submatrix
    Matrix.of (fun i j => S₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  let D₁ : Matrix (Fin 2) (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let D₂ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  ⟨
    ⟨
      (S₁.X \ {x₁, x₂, x₃}) ∪ S₂.X,
      S₁.Y ∪ (S₂.Y \ {y₁, y₂, y₃}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨S₁.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨hXY.disjoint_sdiff_right.disjoint_sdiff_left, S₂.hXY.disjoint_sdiff_right⟩⟩,
      Matrix.of (fun i j =>
        matrix3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂ (
          if hi₁ : i.val ∈ S₁.X \ {x₁, x₂, x₃} then ◩◩⟨i, hi₁⟩ else
          if hi₂ : i.val ∈ S₂.X \ {x₁, x₂, x₃} then ◪◪⟨i, hi₂⟩ else
          if hx₁ : i.val = x₁ then ◩◪() else
          if hx₂ : i.val = x₂ then ◪◩0 else
          if hx₃ : i.val = x₃ then ◪◩1 else
          (i.property.elim hi₁ (by simp_all)).elim
        ) (
          if hj₁ : j.val ∈ S₁.Y \ {y₁, y₂, y₃} then ◩◩⟨j, hj₁⟩ else
          if hj₂ : j.val ∈ S₂.Y \ {y₁, y₂, y₃} then ◪◪⟨j, hj₂⟩ else
          if hy₁ : j.val = y₁ then ◩◪1 else
          if hy₂ : j.val = y₂ then ◩◪0 else
          if hy₃ : j.val = y₃ then ◪◩() else
          (j.property.elim (by simp_all) hj₂).elim
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
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = (S₁.X \ {x₁, x₂, x₃}) ∪ S₂.X :=
  rfl

lemma standardRepr3sumComposition_Y {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = S₁.Y ∪ (S₂.Y \ {y₁, y₂, y₃}) :=
  rfl

lemma standardRepr3sumComposition_B {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B =
    have hxxx₁ : {x₁, x₂, x₃} ⊆ S₁.X := hXX.symm.subset.trans Set.inter_subset_left
    have hxxx₂ : {x₁, x₂, x₃} ⊆ S₂.X := hXX.symm.subset.trans Set.inter_subset_right
    have hyyy₁ : {y₁, y₂, y₃} ⊆ S₁.Y := hYY.symm.subset.trans Set.inter_subset_left
    have hyyy₂ : {y₁, y₂, y₃} ⊆ S₂.Y := hYY.symm.subset.trans Set.inter_subset_right
    have x₁inX₁ : x₁ ∈ S₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
    have x₂inX₁ : x₂ ∈ S₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    have x₂inX₂ : x₂ ∈ S₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    have x₃inX₁ : x₃ ∈ S₁.X := hxxx₁ (by simp)
    have x₃inX₂ : x₃ ∈ S₂.X := hxxx₂ (by simp)
    have y₃inY₂ : y₃ ∈ S₂.Y := hyyy₂ (by simp)
    have y₂inY₁ : y₂ ∈ S₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    have y₂inY₂ : y₂ ∈ S₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    have y₁inY₁ : y₁ ∈ S₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
    have y₁inY₂ : y₁ ∈ S₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
    let A₁ : Matrix (S₁.X \ {x₁, x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
      Matrix.of (fun i j => S₁.B
          ⟨i.val, Set.mem_of_mem_diff i.property⟩
          (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩]))
    let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
      Matrix.of (fun i j => S₂.B
          (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
          ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let z₁ : (S₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
      (fun j => S₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let z₂ : (S₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
      (fun i => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
    let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
      Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))
    let D₁ : Matrix (Fin 2) (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
      Matrix.of (fun i j => S₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    let D₂ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
      Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
    ((matrix3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂).submatrix
      ((Equiv.sumAssoc (S₁.X \ {x₁, x₂, x₃}).Elem Unit (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem)).invFun ∘
        Sum.map id (fun i : S₂.X =>
          if hx₁ : i.val = x₁ then ◩() else
          if hx₂ : i.val = x₂ then ◪◩0 else
          if hx₃ : i.val = x₃ then ◪◩1 else
          ◪(◪⟨i, by simp_all⟩)))
      ((Equiv.sumAssoc ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Unit (S₂.Y \ {y₁, y₂, y₃}).Elem).toFun ∘
        Sum.map (fun j : S₁.Y =>
          if hy₁ : j.val = y₁ then ◩◪1 else
          if hy₂ : j.val = y₂ then ◩◪0 else
          if hy₃ : j.val = y₃ then ◪() else
          ◩(◩⟨j, by simp_all⟩)) id)
      ).toMatrixUnionUnion
    := by
  ext i j
  rw [standardRepr3sumComposition_X] at i
  rw [standardRepr3sumComposition_Y] at j
  if hi : i.val ∈ S₂.X then
    if hj : j.val ∈ S₁.Y then
      sorry
    else
      sorry
  else
    if hj : j.val ∈ S₁.Y then
      sorry
    else
      sorry

instance Matroid.Is3sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_X]
  apply Finite.Set.finite_union

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  sorry
