import Seymour.Matroid.Notions.Regularity
import Seymour.Matroid.Operations.Sum2
import Seymour.Matrix.Pivoting
import Seymour.Matrix.Determinants
import Seymour.Matrix.PreTUness


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
noncomputable abbrev matrix3sumComposition {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
    (z₁ : Y₁ → β) (z₂ : X₂ → β) (D : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
    Matrix ((X₁ ⊕ Unit) ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ (Unit ⊕ Y₂)) β :=
  -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
  let D₁₂ : Matrix X₂ Y₁ β := D₂ * D⁻¹ * D₁
  Matrix.fromBlocks
    (Matrix.fromRows A₁ (Matrix.replicateRow Unit (Sum.elim z₁ ![1, 1]))) 0
    (Matrix.fromBlocks D₁ D D₁₂ D₂) (Matrix.fromCols (Matrix.replicateCol Unit (Sum.elim ![1, 1] z₂)) A₂)

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
  let A₁ : Matrix (S₁.X \ {x₁, x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    Matrix.of (fun i j => S₁.B
        ⟨i.val, Set.mem_of_mem_diff i.property⟩
        (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₁, y₁inY₁⟩, ⟨y₂, y₂inY₁⟩]))
  let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
    Matrix.of (fun i j => S₂.B
        (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
        ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₁ : (S₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
    (fun j => S₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₂ : (S₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
    (fun i => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
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
          if hy₁ : j.val = y₁ then ◩◪0 else
          if hy₂ : j.val = y₂ then ◩◪1 else
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

local macro "finish3B" : tactic => `(tactic| simp_all [standardRepr3sumComposition, Equiv.sumAssoc, Matrix.toMatrixUnionUnion])

set_option maxHeartbeats 6000000 in
lemma standardRepr3sumComposition_B {S₁ S₂ : StandardRepr α Z2} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}) (hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    -- (standardRepr3sumComposition hXX hYY hXY hYX).fst.B =
    -- have hxxx₁ : {x₁, x₂, x₃} ⊆ S₁.X := hXX.symm.subset.trans Set.inter_subset_left
    -- have hxxx₂ : {x₁, x₂, x₃} ⊆ S₂.X := hXX.symm.subset.trans Set.inter_subset_right
    -- have hyyy₁ : {y₁, y₂, y₃} ⊆ S₁.Y := hYY.symm.subset.trans Set.inter_subset_left
    -- have hyyy₂ : {y₁, y₂, y₃} ⊆ S₂.Y := hYY.symm.subset.trans Set.inter_subset_right
    -- have x₁inX₁ : x₁ ∈ S₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
    -- have x₂inX₁ : x₂ ∈ S₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    -- have x₂inX₂ : x₂ ∈ S₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
    -- have x₃inX₁ : x₃ ∈ S₁.X := hxxx₁ (by simp)
    -- have x₃inX₂ : x₃ ∈ S₂.X := hxxx₂ (by simp)
    -- have y₁inY₁ : y₁ ∈ S₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
    -- have y₁inY₂ : y₁ ∈ S₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
    -- have y₂inY₁ : y₂ ∈ S₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    -- have y₂inY₂ : y₂ ∈ S₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
    -- have y₃inY₂ : y₃ ∈ S₂.Y := hyyy₂ (by simp)
    -- let A₁ : Matrix (S₁.X \ {x₁, x₂, x₃}).Elem ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    --   Matrix.of (fun i j => S₁.B
    --       ⟨i.val, Set.mem_of_mem_diff i.property⟩
    --       (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₁, sorry⟩, ⟨y₂, sorry⟩]))
    -- let A₂ : Matrix (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem) (S₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
    --   Matrix.of (fun i j => S₂.B
    --       (i.casesOn ![⟨x₂, sorry⟩, ⟨x₃, sorry⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
    --       ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    -- let z₁ : (S₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
    --   (fun j => S₁.B ⟨x₁, sorry⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    -- let z₂ : (S₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
    --   (fun i => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, sorry⟩)
    -- let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
    --   Matrix.of (fun i j => S₁.B (![⟨x₂, sorry⟩, ⟨x₃, sorry⟩] i) (![⟨y₁, sorry⟩, ⟨y₂, sorry⟩] j))
    -- let D₁ : Matrix (Fin 2) (S₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
    --   Matrix.of (fun i j => S₁.B (![⟨x₂, sorry⟩, ⟨x₃, sorry⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
    -- let D₂ : Matrix (S₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
    --   Matrix.of (fun i j => S₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₁, sorry⟩, ⟨y₂, sorry⟩] j))
    -- ((matrix3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂).submatrix
    --   ((Equiv.sumAssoc (S₁.X \ {x₁, x₂, x₃}).Elem Unit (Fin 2 ⊕ (S₂.X \ {x₁, x₂, x₃}).Elem)).invFun ∘
    --     Sum.map id (fun i : S₂.X =>
    --       if hx₁ : i.val = x₁ then ◩() else
    --       if hx₂ : i.val = x₂ then ◪◩0 else
    --       if hx₃ : i.val = x₃ then ◪◩1 else
    --       ◪◪⟨i, by simp_all⟩))
    --   ((Equiv.sumAssoc ((S₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Unit (S₂.Y \ {y₁, y₂, y₃}).Elem).toFun ∘
    --     Sum.map (fun j : S₁.Y =>
    --       if hy₁ : j.val = y₁ then ◩◪0 else
    --       if hy₂ : j.val = y₂ then ◩◪1 else
    --       if hy₃ : j.val = y₃ then ◪() else
    --       ◩◩⟨j, by simp_all⟩) id)
    --   ).toMatrixUnionUnion
    True
    := by
  sorry
  -- -- This proof is not worth optimizing because we might be throwing it away soon.
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

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  sorry


section ProposedRefactor

private def remap_two_elem_to_set {X : Set α} {x₁ x₂ : α} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) : ({x₁, x₂} : Set α).Elem → X :=
  fun i => (
    if hix₁ : i = x₁ then ⟨x₁, hx₁⟩ else
    if hic₂ : i = x₂ then ⟨x₂, hx₂⟩ else
    False.elim (by
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self]))

private def remap_two_elem_to_type {Y : Type} (x₁ x₂ : α) (y₁ y₂ : Y) : ({x₁, x₂} : Set α).Elem → Y :=
  fun i => (
    if hix₁ : i = x₁ then y₁ else
    if hic₂ : i = x₂ then y₂ else
    False.elim (by
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self]))

private def remap_fin2_to_type {Y : Type} (y₁ y₂ : Y) : Fin 2 → Y := ![y₁, y₂]

lemma set_reunion_2 {Y₁ : Set α} {c₁ c₂ c₃ : α} (hc₁ : c₁ ∈ Y₁) (hc₂ : c₂ ∈ Y₁) (hc₃ : c₃ ∈ Y₁) :
    Y₁ \ {c₁, c₂, c₃} ∪ {c₁, c₂} = Y₁ \ {c₃} := by
  -- have t : ((Y₁ \ {c₁, c₂}) \ {c₃}) ∪ {c₁, c₂} = Y₁ \ {c₃} := by aesop
  -- aesop
  ext y
  -- aesop
  -- tauto_set
  sorry

def matrix3sumComposition_standard_2 {β : Type} [Field β] {X₁ Y₁ X₂ Y₂ : Set α}
  {r₁ r₂ r₃ c₁ c₂ c₃ : α}
  [∀ x, Decidable (x ∈ X₁ \ {r₁, r₂, r₃})] [∀ x, Decidable (x ∈ X₂ \ {r₁, r₂, r₃})] -- for toMatrixUnionUnion
  [∀ y, Decidable (y ∈ Y₁ \ {c₁, c₂, c₃})] [∀ y, Decidable (y ∈ Y₂ \ {c₁, c₂, c₃})] -- for toMatrixUnionUnion
  (B₁ : Matrix X₁ Y₁ β) (B₂ : Matrix X₂ Y₂ β)
  (hX₁X₂ : X₁ ∩ X₂ = {r₁, r₂, r₃}) (hY₁Y₂ : Y₁ ∩ Y₂ = {c₁, c₂, c₃}) :
  Matrix ((X₁ \ {r₁, r₂}).Elem ⊕ (X₂ \ {r₃}).Elem) ((Y₁ \ {c₃}).Elem ⊕ (Y₂ \ {c₁, c₂}).Elem) β :=
  -- row and column membership
  have hrX₁ : {r₁, r₂, r₃} ⊆ X₁ := hX₁X₂.symm.subset.trans Set.inter_subset_left
  have hrX₂ : {r₁, r₂, r₃} ⊆ X₂ := hX₁X₂.symm.subset.trans Set.inter_subset_right
  have hcY₁ : {c₁, c₂, c₃} ⊆ Y₁ := hY₁Y₂.symm.subset.trans Set.inter_subset_left
  have hcY₂ : {c₁, c₂, c₃} ⊆ Y₂ := hY₁Y₂.symm.subset.trans Set.inter_subset_right
  have r₁inX₁ : r₁ ∈ X₁ := hrX₁ (Set.mem_insert r₁ {r₂, r₃})
  have r₁inX₂ : r₁ ∈ X₂ := hrX₂ (Set.mem_insert r₁ {r₂, r₃})
  have r₂inX₁ : r₂ ∈ X₁ := hrX₁ (Set.insert_comm r₁ r₂ {r₃} ▸ Set.mem_insert r₂ {r₁, r₃})
  have r₂inX₂ : r₂ ∈ X₂ := hrX₂ (Set.insert_comm r₁ r₂ {r₃} ▸ Set.mem_insert r₂ {r₁, r₃})
  have r₃inX₁ : r₃ ∈ X₁ := hrX₁ (by simp)
  have r₃inX₂ : r₃ ∈ X₂ := hrX₂ (by simp)
  have c₁inY₁ : c₁ ∈ Y₁ := hcY₁ (Set.mem_insert c₁ {c₂, c₃})
  have c₁inY₂ : c₁ ∈ Y₂ := hcY₂ (Set.mem_insert c₁ {c₂, c₃})
  have c₂inY₁ : c₂ ∈ Y₁ := hcY₁ (Set.insert_comm c₁ c₂ {c₃} ▸ Set.mem_insert c₂ {c₁, c₃})
  have c₂inY₂ : c₂ ∈ Y₂ := hcY₂ (Set.insert_comm c₁ c₂ {c₃} ▸ Set.mem_insert c₂ {c₁, c₃})
  have c₃inY₁ : c₃ ∈ Y₁ := hcY₁ (by simp)
  have c₃inY₂ : c₃ ∈ Y₂ := hcY₂ (by simp)
  -- rows and columns of the 2x2 submatrix
  let r₁r₂X₁ : ({r₁, r₂} : Set α).Elem → X₁ := remap_two_elem_to_set r₁inX₁ r₂inX₁
  let r₁r₂X₂ : ({r₁, r₂} : Set α).Elem → X₂ := remap_two_elem_to_set r₁inX₂ r₂inX₂
  let c₁c₂Y₁ : ({c₁, c₂} : Set α).Elem → Y₁ := remap_two_elem_to_set c₁inY₁ c₂inY₁
  let c₁c₂Y₂ : ({c₁, c₂} : Set α).Elem → Y₂ := remap_two_elem_to_set c₁inY₂ c₂inY₂
  -- submatrices
  let D₀₁ : Matrix (Fin 2) (Fin 2) β :=
    !![B₁ ⟨r₁, r₁inX₁⟩ ⟨c₁, c₁inY₁⟩, B₁ ⟨r₁, r₁inX₁⟩ ⟨c₂, c₂inY₁⟩; B₁ ⟨r₂, r₂inX₁⟩ ⟨c₁, c₁inY₁⟩, B₁ ⟨r₂, r₂inX₁⟩ ⟨c₂, c₂inY₁⟩]
  -- let D₀₂ : Matrix (Fin 2) (Fin 2) β := -- not needed for the construction, only for correctness:
  --   !![B₂ ⟨r₁, r₁inX₂⟩ ⟨c₁, c₁inY₂⟩, B₂ ⟨r₁, r₁inX₂⟩ ⟨c₂, c₂inY₂⟩; B₂ ⟨r₂, r₂inX₂⟩ ⟨c₁, c₁inY₂⟩, B₂ ⟨r₂, r₂inX₂⟩ ⟨c₂, c₂inY₂⟩]
  -- let D₁ : Matrix (Fin 2) (Y₁ \ {c₁, c₂, c₃}).Elem β := B₁.submatrix r₁r₂X₁ Set.diff_subset.elem
  sorry
  -- let D₀₁ : Matrix ({r₁, r₂} : Set α).Elem ({c₁, c₂} : Set α).Elem β := B₁.submatrix r₁r₂X₁ c₁c₂Y₁
  -- let D₀₂ : Matrix ({r₁, r₂} : Set α).Elem ({c₁, c₂} : Set α).Elem β := B₂.submatrix r₁r₂X₂ c₁c₂Y₂
  -- let D₁ : Matrix ({r₁, r₂} : Set α).Elem (Y₁ \ {c₁, c₂, c₃}).Elem β := B₁.submatrix r₁r₂X₁ Set.diff_subset.elem
  -- let D₂ : Matrix (X₂ \ {r₁, r₂, r₃}).Elem ({c₁, c₂} : Set α).Elem β := B₂.submatrix Set.diff_subset.elem c₁c₂Y₂
  -- let A₁ : Matrix (X₁ \ {r₁, r₂}).Elem (Y₁ \ {c₃}).Elem β := B₁.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- let A₂ : Matrix (X₂ \ {r₃}).Elem (Y₂ \ {c₁, c₂}).Elem β := B₂.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- -- invert D₀ by hand
  -- let detD₀ : β :=
  --   B₁ ⟨r₁, r₁inX₁⟩ ⟨c₁, c₁inY₁⟩ * B₁ ⟨r₂, r₂inX₁⟩ ⟨c₂, c₂inY₁⟩ - B₁ ⟨r₁, r₁inX₁⟩ ⟨c₂, c₂inY₁⟩ * B₁ ⟨r₂, r₂inX₁⟩ ⟨c₁, c₁inY₁⟩
  -- let D₀₁_inv : Matrix ({c₁, c₂} : Set α).Elem ({r₁, r₂} : Set α).Elem β :=
  --   detD₀⁻¹ • Matrix.of (fun (i : ({c₁, c₂} : Set α).Elem) (j : ({r₁, r₂} : Set α).Elem) =>
  --     if hic₁ : i = c₁ then
  --       if hjr₁ : j = r₁ then
  --         B₁ ⟨r₂, r₂inX₁⟩ ⟨c₂, c₂inY₁⟩
  --       else if hjr₂ : j = r₂ then
  --         - B₁ ⟨r₁, r₁inX₁⟩ ⟨c₂, c₂inY₁⟩
  --       else False.elim (by
  --         obtain ⟨_, _⟩ := j
  --         simp_all only
  --         simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
  --     else if hic₂ : i = c₂ then
  --       if hjr₁ : j = r₁ then
  --         - B₁ ⟨r₂, r₂inX₁⟩ ⟨c₁, c₁inY₁⟩
  --       else if hjr₂ : j = r₂ then
  --         B₁ ⟨r₁, r₁inX₁⟩ ⟨c₁, c₁inY₁⟩
  --       else False.elim (by
  --         obtain ⟨_, _⟩ := j
  --         simp_all only
  --         simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
  --       else False.elim (by
  --         obtain ⟨_, _⟩ := i
  --         simp_all only
  --         simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
  --   )
  -- -- cotinue normally
  -- let D₁₂ : Matrix (X₂ \ {r₁, r₂, r₃}).Elem (Y₁ \ {c₁, c₂, c₃}).Elem β := D₂ * D₀₁_inv * D₁
  -- have uX₂ : {r₁, r₂} ∪ X₂ \ {r₁, r₂, r₃} = X₂ \ {r₃} := Set.union_comm _ _ ▸ set_reunion_2 r₁inX₂ r₂inX₂ r₃inX₂
  -- have uY₁ : Y₁ \ {c₁, c₂, c₃} ∪ {c₁, c₂} = Y₁ \ {c₃} := set_reunion_2 c₁inY₁ c₂inY₁ c₃inY₁
  -- let D : Matrix (X₂ \ {r₃}).Elem (Y₁ \ {c₃}).Elem β := uX₂ ▸ uY₁ ▸ (Matrix.fromBlocks D₁ D₀₁ D₁₂ D₂).toMatrixUnionUnion
  -- Matrix.fromBlocks A₁ 0 D A₂

-- latest version
-- def matrix3sumComposition_standard {β : Type} [Field β] {X₁ Y₁ X₂ Y₂ : Set α}
--   {r₁ r₂ r₃ c₁ c₂ c₃ : α}
--   [∀ x, Decidable (x ∈ X₁ \ {r₁, r₂, r₃})] [∀ x, Decidable (x ∈ X₂ \ {r₁, r₂, r₃})] -- for toMatrixUnionUnion
--   [∀ y, Decidable (y ∈ Y₁ \ {c₁, c₂, c₃})] [∀ y, Decidable (y ∈ Y₂ \ {c₁, c₂, c₃})] -- for toMatrixUnionUnion
--   (B₁ : Matrix X₁ Y₁ β) (B₂ : Matrix X₂ Y₂ β)
--   (hX₁Y₁ : X₁ ⫗ Y₁) (hX₂Y₂ : X₂ ⫗ Y₂)
--   (hX₁X₂ : X₁ ∩ X₂ = {r₁, r₂, r₃}) (hY₁Y₂ : Y₁ ∩ Y₂ = {c₁, c₂, c₃})
--   (hX₁Y₂ : X₁ ⫗ Y₂) (hY₁X₂ : Y₁ ⫗ X₂)
--   -- todo: add that r₁ r₂ r₃ c₁ c₂ c₃ are all distinct
--    :
--   Matrix ((X₁ \ {r₁, r₂}).Elem ⊕ (X₂ \ {r₃}).Elem) ((Y₁ \ {c₃}).Elem ⊕ (Y₂ \ {c₁, c₂}).Elem) β × Prop
--   :=
--   -- row and column membership
--   have hrX₁ : {r₁, r₂, r₃} ⊆ X₁ := hX₁X₂.symm.subset.trans Set.inter_subset_left
--   have hrX₂ : {r₁, r₂, r₃} ⊆ X₂ := hX₁X₂.symm.subset.trans Set.inter_subset_right
--   have hcY₁ : {c₁, c₂, c₃} ⊆ Y₁ := hY₁Y₂.symm.subset.trans Set.inter_subset_left
--   have hcY₂ : {c₁, c₂, c₃} ⊆ Y₂ := hY₁Y₂.symm.subset.trans Set.inter_subset_right
--   have r₁inX₁ : r₁ ∈ X₁ := hrX₁ (Set.mem_insert r₁ {r₂, r₃})
--   have r₁inX₂ : r₁ ∈ X₂ := hrX₂ (Set.mem_insert r₁ {r₂, r₃})
--   have r₂inX₁ : r₂ ∈ X₁ := hrX₁ (Set.insert_comm r₁ r₂ {r₃} ▸ Set.mem_insert r₂ {r₁, r₃})
--   have r₂inX₂ : r₂ ∈ X₂ := hrX₂ (Set.insert_comm r₁ r₂ {r₃} ▸ Set.mem_insert r₂ {r₁, r₃})
--   have r₃inX₁ : r₃ ∈ X₁ := hrX₁ (by simp)
--   have r₃inX₂ : r₃ ∈ X₂ := hrX₂ (by simp)
--   have c₁inY₁ : c₁ ∈ Y₁ := hcY₁ (Set.mem_insert c₁ {c₂, c₃})
--   have c₁inY₂ : c₁ ∈ Y₂ := hcY₂ (Set.mem_insert c₁ {c₂, c₃})
--   have c₂inY₁ : c₂ ∈ Y₁ := hcY₁ (Set.insert_comm c₁ c₂ {c₃} ▸ Set.mem_insert c₂ {c₁, c₃})
--   have c₂inY₂ : c₂ ∈ Y₂ := hcY₂ (Set.insert_comm c₁ c₂ {c₃} ▸ Set.mem_insert c₂ {c₁, c₃})
--   have c₃inY₁ : c₃ ∈ Y₁ := hcY₁ (by simp)
--   have c₃inY₂ : c₃ ∈ Y₂ := hcY₂ (by simp)
--   -- rows and columns of the 2x2 submatrix
--   let r₁r₂X₁ : ({r₁, r₂} : Set α).Elem → X₁ := two_elem_remap r₁inX₁ r₂inX₁
--   let r₁r₂X₂ : ({r₁, r₂} : Set α).Elem → X₂ := two_elem_remap r₁inX₂ r₂inX₂
--   let c₁c₂Y₁ : ({c₁, c₂} : Set α).Elem → Y₁ := two_elem_remap c₁inY₁ c₂inY₁
--   let c₁c₂Y₂ : ({c₁, c₂} : Set α).Elem → Y₂ := two_elem_remap c₁inY₂ c₂inY₂
--   -- submatrices
--   let D₀₁ : Matrix ({r₁, r₂} : Set α).Elem ({c₁, c₂} : Set α).Elem β := B₁.submatrix r₁r₂X₁ c₁c₂Y₁
--   let D₀₂ : Matrix ({r₁, r₂} : Set α).Elem ({c₁, c₂} : Set α).Elem β := B₂.submatrix r₁r₂X₂ c₁c₂Y₂
--   let D₁ : Matrix ({r₁, r₂} : Set α).Elem (Y₁ \ {c₁, c₂, c₃}).Elem β := B₁.submatrix r₁r₂X₁ Set.diff_subset.elem
--   let D₂ : Matrix (X₂ \ {r₁, r₂, r₃}).Elem ({c₁, c₂} : Set α).Elem β := B₂.submatrix Set.diff_subset.elem c₁c₂Y₂
--   let A₁ : Matrix (X₁ \ {r₁, r₂}).Elem (Y₁ \ {c₃}).Elem β := B₁.submatrix Set.diff_subset.elem Set.diff_subset.elem
--   let A₂ : Matrix (X₂ \ {r₃}).Elem (Y₂ \ {c₁, c₂}).Elem β := B₂.submatrix Set.diff_subset.elem Set.diff_subset.elem
--   -- invert D₀ by hand
--   let detD₀ : β :=
--     B₁ ⟨r₁, r₁inX₁⟩ ⟨c₁, c₁inY₁⟩ * B₁ ⟨r₂, r₂inX₁⟩ ⟨c₂, c₂inY₁⟩ - B₁ ⟨r₁, r₁inX₁⟩ ⟨c₂, c₂inY₁⟩ * B₁ ⟨r₂, r₂inX₁⟩ ⟨c₁, c₁inY₁⟩
--   let D₀₁_inv : Matrix ({c₁, c₂} : Set α).Elem ({r₁, r₂} : Set α).Elem β :=
--     detD₀⁻¹ • Matrix.of (fun (i : ({c₁, c₂} : Set α).Elem) (j : ({r₁, r₂} : Set α).Elem) =>
--       if hic₁ : i = c₁ then
--         if hjr₁ : j = r₁ then
--           B₁ ⟨r₂, r₂inX₁⟩ ⟨c₂, c₂inY₁⟩
--         else if hjr₂ : j = r₂ then
--           - B₁ ⟨r₁, r₁inX₁⟩ ⟨c₂, c₂inY₁⟩
--         else False.elim (by
--           obtain ⟨_, _⟩ := j
--           simp_all only
--           simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
--       else if hic₂ : i = c₂ then
--         if hjr₁ : j = r₁ then
--           - B₁ ⟨r₂, r₂inX₁⟩ ⟨c₁, c₁inY₁⟩
--         else if hjr₂ : j = r₂ then
--           B₁ ⟨r₁, r₁inX₁⟩ ⟨c₁, c₁inY₁⟩
--         else False.elim (by
--           obtain ⟨_, _⟩ := j
--           simp_all only
--           simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
--         else False.elim (by
--           obtain ⟨_, _⟩ := i
--           simp_all only
--           simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self])
--     )
--   -- cotinue normally
--   let D₁₂ : Matrix (X₂ \ {r₁, r₂, r₃}).Elem (Y₁ \ {c₁, c₂, c₃}).Elem β := D₂ * D₀₁_inv * D₁
--   have uX₂ : {r₁, r₂} ∪ X₂ \ {r₁, r₂, r₃} = X₂ \ {r₃} := Set.union_comm _ _ ▸ set_reunion_2 r₁inX₂ r₂inX₂ r₃inX₂
--   have uY₁ : Y₁ \ {c₁, c₂, c₃} ∪ {c₁, c₂} = Y₁ \ {c₃} := set_reunion_2 c₁inY₁ c₂inY₁ c₃inY₁
--   let D : Matrix (X₂ \ {r₃}).Elem (Y₁ \ {c₃}).Elem β := uX₂ ▸ uY₁ ▸ (Matrix.fromBlocks D₁ D₀₁ D₁₂ D₂).toMatrixUnionUnion
--   ⟨Matrix.fromBlocks A₁ 0 D A₂, sorry⟩

end ProposedRefactor

section CanonicalSigning

lemma Matrix.Z2_2x2_nonsingular_form (A : Matrix (Fin 2) (Fin 2) Z2) (hA : IsUnit A) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, A.submatrix f g = 1 ∨ A.submatrix f g = !![1, 1; 0, 1] := by
  sorry

def Matrix.toCanonicalSigning_3x3 (A : Matrix (Fin 3) (Fin 3) ℚ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  ⟨![1, A 0 0 * A 1 0, A 0 0 * A 1 0 * A 1 2 * A 2 2], ![A 0 0, A 0 1, A 0 0 * A 1 0 * A 1 2]⟩

noncomputable def matrix3sumComposition_toCanonicalSigning {X₁ Y₁ X₂ Y₂ : Set α}
  (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
  (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ) (x₁ : X₁) (y₃ : Y₂) :
    Matrix (X₁ ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ Y₂) ℚ :=
  -- get multiplication factors to get 3×3 matrix containing D₀ to canonical form
  let D₀_ext := !![A₁ x₁ (.inr 0), A₁ x₁ (.inr 1), 0; D₀ 0 0, D₀ 0 1, A₂ (.inl 0) y₃; D₀ 1 0, D₀ 1 1, A₂ (.inl 1) y₃];
  let D₀_row_mult := D₀_ext.toCanonicalSigning_3x3.fst;
  let D₀_col_mult := D₀_ext.toCanonicalSigning_3x3.snd;
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

end CanonicalSigning

section OuterProducts

def matrix3sumComposition_outerProducts {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
  (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) (r₁ : Y₁ → β) (r₂ : Y₁ → β) (c₁ : X₂ → β) (c₂ : X₂ → β) :
  Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 ((fun i j => c₁ i * r₁ j) + (fun i j => c₂ i * r₂ j)) A₂

lemma matrix3sumComposition_outerProducts_pivotA₁_A₁ {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ) (i : X₁) (j : Y₁) :
    let B := (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂)
    (B.shortTableauPivot ◩i ◩j).submatrix Sum.inl Sum.inl = A₁.shortTableauPivot i j := by
  intro B
  exact (B.submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm

lemma matrix3sumComposition_outerProducts_pivotA₁_zero {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ) (i : X₁) (j : Y₁) :
    let B := (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂)
    (B.shortTableauPivot ◩i ◩j).submatrix Sum.inl Sum.inr = 0 := by
  intro B
  ext i' j'
  exact B.shortTableauPivot_zero i ◩j Sum.inl Sum.inr (by simp) (by simp [matrix3sumComposition_outerProducts, B]) i' j'

lemma matrix3sumComposition_outerProducts_pivotA₁_D {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hAij : A₁ i j = 1 ∨ A₁ i j = -1) :
    let B := (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂)
    (B.shortTableauPivot ◩i ◩j).submatrix Sum.inr Sum.inl = sorry := by
  sorry

lemma matrix3sumComposition_outerProducts_pivotA₁_A₂ {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hAij : A₁ i j = 1 ∨ A₁ i j = -1) :
    let B := (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂)
    (B.shortTableauPivot ◩i ◩j).submatrix Sum.inr Sum.inr = A₂ := by
  intro B
  exact B.shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr (by aesop) (by aesop) (by aesop)

lemma matrix3sumComposition_outerProducts_shortTableauPivotA₁ {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hAij : A₁ i j = 1 ∨ A₁ i j = -1) :
    let B := (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂)
    B.shortTableauPivot ◩i ◩j =
    matrix3sumComposition_outerProducts (A₁.shortTableauPivot i j) A₂ (sorry) (sorry) c₁ c₂ := by
  sorry

lemma matrix3sumComposition_IsTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₁ : Y₁ → ℚ) (r₂ : Y₁ → ℚ) (c₁ : X₂ → ℚ) (c₂ : X₂ → ℚ)
    (hA₁ : (▬r₁ ⊟ ▬r₂ ⊟ A₁).IsTotallyUnimodular) (hA₂ : (▮c₁ ◫ ▮c₂ ◫ A₂).IsTotallyUnimodular)
    (hc₁c₂ : ∀ i, (c₁ - c₂) i ∈ SignType.cast.range) (hr₁r₂ : ∀ j, (r₁ + r₂) j ∈ SignType.cast.range) :
    (matrix3sumComposition_outerProducts A₁ A₂ r₁ r₂ c₁ c₂).IsTotallyUnimodular
    := by
  sorry

end OuterProducts
