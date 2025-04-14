import Seymour.Matroid.Notions.Regularity
import Seymour.Matroid.Operations.Sum2


variable {α : Type} [DecidableEq α]

section StandardMatrixDefinition

/-- The 3-sum composition of two matrices. -/
noncomputable def matrix3sumComposition_standard {β : Type} [Field β] {X₁ Y₁ X₂ Y₂ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ X₁ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ X₂ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Y₁ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Y₂ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (B₁ : Matrix X₁ Y₁ β) (B₂ : Matrix X₂ Y₂ β) (hX₁X₂ : X₁ ∩ X₂ = {x₀, x₁, x'}) (hY₁Y₂ : Y₁ ∩ Y₂ = {y₀, y₁, y'}) :
    Matrix ((X₁ \ {x₀, x₁}).Elem ⊕ (X₂ \ {x'}).Elem) ((Y₁ \ {y'}).Elem ⊕ (Y₂ \ {y₀, y₁}).Elem) β × Prop :=
  -- row membership
  have hrX₁ : {x₀, x₁, x'} ⊆ X₁ := hX₁X₂.symm.subset.trans Set.inter_subset_left
  have hrX₂ : {x₀, x₁, x'} ⊆ X₂ := hX₁X₂.symm.subset.trans Set.inter_subset_right
  have x₀inX₁ : x₀ ∈ X₁ := hrX₁ (Set.mem_insert x₀ {x₁, x'})
  have x₀inX₂ : x₀ ∈ X₂ := hrX₂ (Set.mem_insert x₀ {x₁, x'})
  have x₁inX₁ : x₁ ∈ X₁ := hrX₁ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x₁inX₂ : x₁ ∈ X₂ := hrX₂ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x'inX₁ : x' ∈ X₁ := hrX₁ (by simp) -- not needed for definition, only for correctness
  have x'inX₂ : x' ∈ X₂ := hrX₂ (by simp) -- not needed for definition, only for correctness
  -- column membership
  have hcY₁ : {y₀, y₁, y'} ⊆ Y₁ := hY₁Y₂.symm.subset.trans Set.inter_subset_left
  have hcY₂ : {y₀, y₁, y'} ⊆ Y₂ := hY₁Y₂.symm.subset.trans Set.inter_subset_right
  have y₀inY₁ : y₀ ∈ Y₁ := hcY₁ (Set.mem_insert y₀ {y₁, y'})
  have y₀inY₂ : y₀ ∈ Y₂ := hcY₂ (Set.mem_insert y₀ {y₁, y'})
  have y₁inY₁ : y₁ ∈ Y₁ := hcY₁ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y₁inY₂ : y₁ ∈ Y₂ := hcY₂ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y'inY₁ : y' ∈ Y₁ := hcY₁ (by simp) -- not needed for definition, only for correctness
  have y'inY₂ : y' ∈ Y₂ := hcY₂ (by simp) -- not needed for definition, only for correctness
  -- pieces of bottom left submatrix
  let D₀₁ : Matrix (Fin 2) (Fin 2) β :=
    !![B₁ ⟨x₀, x₀inX₁⟩ ⟨y₀, y₀inY₁⟩, B₁ ⟨x₀, x₀inX₁⟩ ⟨y₁, y₁inY₁⟩; B₁ ⟨x₁, x₁inX₁⟩ ⟨y₀, y₀inY₁⟩, B₁ ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩]
  let D₀₂ : Matrix (Fin 2) (Fin 2) β := -- not needed for definition, only for correctness
    !![B₂ ⟨x₀, x₀inX₂⟩ ⟨y₀, y₀inY₂⟩, B₂ ⟨x₀, x₀inX₂⟩ ⟨y₁, y₁inY₂⟩; B₂ ⟨x₁, x₁inX₂⟩ ⟨y₀, y₀inY₂⟩, B₂ ⟨x₁, x₁inX₂⟩ ⟨y₁, y₁inY₂⟩]
  let D₁ : Matrix (Fin 2) (Y₁ \ {y₀, y₁, y'}).Elem β :=
    ![B₁ ⟨x₀, x₀inX₁⟩ ∘ Set.diff_subset.elem, B₁ ⟨x₁, x₁inX₁⟩ ∘ Set.diff_subset.elem]
  let D₂ : Matrix (X₂ \ {x₀, x₁, x'}).Elem (Fin 2) β :=
    Matrix.of (fun i => ![B₂ (Set.diff_subset.elem i) ⟨y₀, y₀inY₂⟩, B₂ (Set.diff_subset.elem i) ⟨y₁, y₁inY₂⟩])
  let D₁₂ : Matrix (X₂ \ {x₀, x₁, x'}).Elem (Y₁ \ {y₀, y₁, y'}).Elem β := D₂ * D₀₁⁻¹ * D₁
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (X₂ \ {x₀, x₁, x'}).Elem) ((Y₁ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) β := Matrix.fromBlocks D₁ D₀₁ D₁₂ D₂
  -- reindexing for bottom left submatrix
  have fX₂ : (X₂ \ {x'}).Elem → Fin 2 ⊕ (X₂ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ X₂ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  have fY₁ : (Y₁ \ {y'}).Elem → (Y₁ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Y₁ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := j
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  -- final bottom left submatrix
  let D : Matrix (X₂ \ {x'}).Elem (Y₁ \ {y'}).Elem β := Matrix.of (fun i j => D' (fX₂ i) (fY₁ j))
  -- top left submatrix
  let A₁ : Matrix (X₁ \ {x₀, x₁}).Elem (Y₁ \ {y'}).Elem β := B₁.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let A₂ : Matrix (X₂ \ {x'}).Elem (Y₂ \ {y₀, y₁}).Elem β := B₂.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- actual definition
  ⟨
    Matrix.fromBlocks A₁ 0 D A₂,
    X₁ ⫗ Y₁ ∧ X₁ ⫗ Y₂ ∧ X₂ ⫗ Y₁ ∧ X₂ ⫗ Y₂ -- rows and columns do not overlap
    ∧ IsUnit D₀₁ -- `D₀` is invertible
    ∧ D₀₁ = D₀₂ -- `D₀` is the same in `B₁` and `B₂`
    ∧ B₁ ⟨x₀, x₀inX₁⟩ ⟨y', y'inY₁⟩ = 1 -- `B₁` has correct structure outside of `A₁`, `D₁`, and `D₀`
    ∧ B₁ ⟨x₁, x₁inX₁⟩ ⟨y', y'inY₁⟩ = 1
    ∧ B₁ ⟨x', x'inX₁⟩ ⟨y₀, y₀inY₁⟩ = 1
    ∧ B₁ ⟨x', x'inX₁⟩ ⟨y₁, y₁inY₁⟩ = 1
    ∧ (∀ x, ∀ hx : x ∈ X₁, x ≠ x₀ ∧ x ≠ x₁ → B₁ ⟨x, hx⟩ ⟨y', y'inY₁⟩ = 0)
    ∧ B₂ ⟨x₀, x₀inX₂⟩ ⟨y', y'inY₂⟩ = 1 -- `B₂` has correct structure outside of `A₂`, `D₂`, and `D₀`
    ∧ B₂ ⟨x₁, x₁inX₂⟩ ⟨y', y'inY₂⟩ = 1
    ∧ B₂ ⟨x', x'inX₂⟩ ⟨y₀, y₀inY₂⟩ = 1
    ∧ B₂ ⟨x', x'inX₂⟩ ⟨y₁, y₁inY₂⟩ = 1
    ∧ (∀ y, ∀ hy : y ∈ Y₂, y ≠ y₀ ∧ y ≠ y₁ → B₂ ⟨x', x'inX₂⟩ ⟨y, hy⟩ = 0)
  ⟩

/-- The 3-sum composition of two binary matroids given by their stanard representations. -/
noncomputable def standardRepr3sumComposition_standard {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      (S₁.X \ {x₀, x₁}) ∪ (S₂.X \ {x'}),
      (S₁.Y \ {y'}) ∪ (S₂.Y \ {y₀, y₁}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨S₁.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, S₂.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (matrix3sumComposition_standard S₁.B S₂.B hXX hYY).fst.toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (matrix3sumComposition_standard S₁.B S₂.B hXX hYY).snd
  ⟩

lemma standardRepr3sumComposition_standard_X {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.X = (S₁.X \ {x₀, x₁}) ∪ (S₂.X \ {x'}) :=
  rfl

lemma standardRepr3sumComposition_standard_Y {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.Y = (S₁.Y \ {y'}) ∪ (S₂.Y \ {y₀, y₁}) :=
  rfl

end StandardMatrixDefinition


section AlternativeMatrixDefinition

omit [DecidableEq α] in
/-- Alternative definition of 3-sum composition using sum of two outer products of vectors to define bottom left submatrix. -/
def matrix3sumCompositionAlt {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) (r₀ : Y₁ → β) (r₁ : Y₁ → β) (c₀ : X₂ → β) (c₁ : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 ((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) A₂

omit [DecidableEq α] in
private lemma matrix3sumCompositionAlt_eq_fromRows {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) (r₀ : Y₁ → β) (r₁ : Y₁ → β) (c₀ : X₂ → β) (c₁ : X₂ → β) :
    matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁ = (A₁ ◫ 0) ⊟ (((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) ◫ A₂) := by
  rfl

private lemma matrix3sumCompositionAlt_isPreTU_1 {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {r₀ : Y₁ → ℚ} {r₁ : Y₁ → ℚ} {c₀ : X₂ → ℚ} {c₁ : X₂ → ℚ}
    (hA₁ : (▬r₀ ⊟ ▬r₁ ⊟ A₁).IsTotallyUnimodular) (hA₂ : (▮c₀ ◫ ▮c₁ ◫ A₂).IsTotallyUnimodular)
    (hcc : ∀ i : X₂, (c₀ - c₁) i ∈ SignType.cast.range) (hrr : ∀ j : Y₁, (r₀ + r₁) j ∈ SignType.cast.range) :
    (matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  have hA₁ : A₁.IsTotallyUnimodular := hA₁.comp_rows Sum.inr
  have hA₂ : A₂.IsTotallyUnimodular := hA₂.comp_cols Sum.inr
  cases f 0 with
  | inl i₁ => cases g 0 with
    | inl j₁ => exact hA₁.apply i₁ j₁
    | inr j₂ => exact zero_in_signTypeCastRange
  | inr i₂ => cases g 0 with
    | inl j₁ =>
      unfold matrix3sumCompositionAlt
      rw [Matrix.fromBlocks_apply₂₁, Pi.add_apply, Pi.add_apply]
      -- todo: follows from `c₀`, `c₁`, `c₀ - c₁`, `r₀`, `r₁`, `r₀ + r₁` all being {0, ±1} vectors
      sorry
    | inr j₂ => exact hA₂.apply i₂ j₂

/-
Does not hold!
Counterexample:
`A₂ := !![0]`
`c₀ := ![1]`
`c₁ := ![1]`
-/
private lemma matrix3sumCompositionAlt_bottom_isTotallyUnimodular_aux {X₂ Y₂ : Set α}
    {A₂ : Matrix X₂ Y₂ ℚ} {c₀ : X₂ → ℚ} {c₁ : X₂ → ℚ}
    (hA₂ : (▮c₀ ◫ ▮c₁ ◫ A₂).IsTotallyUnimodular) (hcc : ∀ i : X₂, (c₀ - c₁) i ∈ SignType.cast.range) :
    (▮0 ◫ ▮(-c₀-c₁) ◫ ▮(c₀-c₁) ◫ ▮(c₁-c₀) ◫ ▮(c₀+c₁) ◫ ▮(-c₀) ◫ ▮(-c₁) ◫ ▮c₀ ◫ ▮c₁ ◫ A₂).IsTotallyUnimodular := by
  sorry

attribute [local simp] neg_add_eq_sub in
attribute [local simp ←] sub_eq_add_neg in
set_option maxHeartbeats 500000 in
/-- In our settings `D ◫ A₂` is totally unimodular.-/
private lemma matrix3sumCompositionAlt_bottom_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {r₀ : Y₁ → ℚ} {r₁ : Y₁ → ℚ} {c₀ : X₂ → ℚ} {c₁ : X₂ → ℚ}
    (hA₁ : (▬r₀ ⊟ ▬r₁ ⊟ A₁).IsTotallyUnimodular) (hA₂ : (▮c₀ ◫ ▮c₁ ◫ A₂).IsTotallyUnimodular)
    (hcc : ∀ i : X₂, (c₀ - c₁) i ∈ SignType.cast.range) :
    (((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) ◫ A₂).IsTotallyUnimodular := by
  convert
    (matrix3sumCompositionAlt_bottom_isTotallyUnimodular_aux hA₂ hcc).submatrix id
      (fun y : Y₁.Elem ⊕ Y₂.Elem => y.casesOn
        (fun y' =>
          match hs₀ : (hA₁.apply ◩◩() y').choose with
          | .zero =>
            match hs₁ : (hA₁.apply ◩◪() y').choose with
            | .zero => ◩◩◩◩◩◩◩◩◩()
            | .pos => ◩◪()
            | .neg => ◩◩◩◪()
          | .pos =>
            match hs₁ : (hA₁.apply ◩◪() y').choose with
            | .zero => ◩◩◪()
            | .pos => ◩◩◩◩◩◪()
            | .neg => ◩◩◩◩◩◩◩◪()
          | .neg =>
            match hs₁ : (hA₁.apply ◩◪() y').choose with
            | .zero => ◩◩◩◩◪()
            | .pos => ◩◩◩◩◩◩◪()
            | .neg => ◩◩◩◩◩◩◩◩◪()
        )
        Sum.inr
      )
  ext i j
  cases j with
  | inl j' =>
    cases hs₀ : (hA₁.apply ◩◩() j').choose with
    | zero =>
      cases hs₁ : (hA₁.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
    | pos =>
      cases hs₁ : (hA₁.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
    | neg =>
      cases hs₁ : (hA₁.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hA₁.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hA₁.apply ◩◪() j').choose_spec.symm
        aesop
  | inr => simp

/-- Expresses how row vector of first outer product changes after pivot in `A₁`. -/
private def matrix3sumCompositionAlt_pivotA₁_Dr₀ {X₁ Y₁ X₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (r₀ : Y₁ → ℚ) (r₁ : Y₁ → ℚ) (c₀ : X₂ → ℚ) (c₁ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hij : A₁ i j = 1 ∨ A₁ i j = -1) : Y₁ → ℚ :=
  -- todo: find explicit formula
  sorry

/-- Expresses how row vector of second outer product changes after pivot in `A₁`. -/
private def matrix3sumCompositionAlt_pivotA₁_Dr₁ {X₁ Y₁ X₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (r₀ : Y₁ → ℚ) (r₁ : Y₁ → ℚ) (c₀ : X₂ → ℚ) (c₁ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hij : A₁ i j = 1 ∨ A₁ i j = -1) : Y₁ → ℚ :=
  -- todo: find explicit formula
  sorry

private lemma matrix3sumCompositionAlt_pivotA₁_Dr₀r₁_properties_preserved {X₁ Y₁ X₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (r₀ : Y₁ → ℚ) (r₁ : Y₁ → ℚ) (c₀ : X₂ → ℚ) (c₁ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hij : A₁ i j = 1 ∨ A₁ i j = -1)
    (hA₁ : (▬r₀ ⊟ ▬r₁ ⊟ A₁).IsTotallyUnimodular) (hA₂ : (▮c₀ ◫ ▮c₁).IsTotallyUnimodular)
    (hc₀c₁ : ∀ i, (c₀ - c₁) i ∈ SignType.cast.range) (hr₀r₁ : ∀ j, (r₀ + r₁) j ∈ SignType.cast.range) :
    let r₀' : Y₁ → ℚ := matrix3sumCompositionAlt_pivotA₁_Dr₀ A₁ r₀ r₁ c₀ c₁ hij
    let r₁' : Y₁ → ℚ := matrix3sumCompositionAlt_pivotA₁_Dr₁ A₁ r₀ r₁ c₀ c₁ hij
    (▬r₀' ⊟ ▬r₁' ⊟ A₁).IsTotallyUnimodular ∧ ∀ j, (r₀' + r₁') j ∈ SignType.cast.range := by
  sorry

private lemma matrix3sumCompositionAlt_shortTableauPivot {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (r₀ : Y₁ → ℚ) (r₁ : Y₁ → ℚ) (c₀ : X₂ → ℚ) (c₁ : X₂ → ℚ)
    {i : X₁} {j : Y₁} (hij : A₁ i j = 1 ∨ A₁ i j = -1) :
    let B := (matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁)
    let r₀' : Y₁ → ℚ := matrix3sumCompositionAlt_pivotA₁_Dr₀ A₁ r₀ r₁ c₀ c₁ hij
    let r₁' : Y₁ → ℚ := matrix3sumCompositionAlt_pivotA₁_Dr₁ A₁ r₀ r₁ c₀ c₁ hij
    B.shortTableauPivot ◩i ◩j = matrix3sumCompositionAlt (A₁.shortTableauPivot i j) A₂ r₀' r₁' c₀ c₁ := by
  intro B r₀' r₁'
  have hBA₁ : (B.shortTableauPivot ◩i ◩j).toBlocks₁₁ = A₁.shortTableauPivot i j
  · exact (B.submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm
  have hB0 : (B.shortTableauPivot ◩i ◩j).toBlocks₁₂ = 0
  · ext i' j'
    exact B.shortTableauPivot_zero i ◩j Sum.inl Sum.inr (by simp) (by simp [matrix3sumCompositionAlt, B]) i' j'
  have hBD : (B.shortTableauPivot ◩i ◩j).toBlocks₂₁ = ((c₀ · * r₀' ·) + (c₁ · * r₁' ·))
  · sorry
  have hBA₂ : (B.shortTableauPivot ◩i ◩j).toBlocks₂₂ = A₂
  · exact B.shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr (by simp) (by simp) (fun _ => rfl)
  rw [←(B.shortTableauPivot ◩i ◩j).fromBlocks_toBlocks, hBA₁, hB0, hBD, hBA₂]
  rfl

private lemma matrix3sumCompositionAlt_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {r₀ : Y₁ → ℚ} {r₁ : Y₁ → ℚ} {c₀ : X₂ → ℚ} {c₁ : X₂ → ℚ}
    (hrrA₁ : (▬r₀ ⊟ ▬r₁ ⊟ A₁).IsTotallyUnimodular) (hccA₂ : (▮c₀ ◫ ▮c₁ ◫ A₂).IsTotallyUnimodular)
    (hcc : ∀ i : X₂, (c₀ - c₁) i ∈ SignType.cast.range) (hrr : ∀ j : Y₁, (r₀ + r₁) j ∈ SignType.cast.range) :
    (matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  cases k with
  | zero => simp [Matrix.IsPreTU]
  | succ m => induction m generalizing A₁ A₂ r₀ r₁ c₀ c₁ with
    | zero => exact matrix3sumCompositionAlt_isPreTU_1 hrrA₁ hccA₂ hcc hrr
    | succ n ih =>
      have hA₁ : A₁.IsTotallyUnimodular := hrrA₁.comp_rows Sum.inr
      have hA₂ : A₂.IsTotallyUnimodular := hccA₂.comp_cols Sum.inr
      by_contra contr
      obtain ⟨f, g, hAfg⟩ := exists_submatrix_of_not_isPreTU contr
      wlog hf : f.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁).submatrix_det_zero_of_not_injective_left hf
      wlog hg : g.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁).submatrix_det_zero_of_not_injective_right hg
      obtain ⟨i₁, x₁, hix₁⟩ : ∃ i₁ : Fin (n + 2), ∃ x₁ : X₁, f i₁ = ◩x₁
      · have isTU := matrix3sumCompositionAlt_bottom_isTotallyUnimodular hrrA₁ hccA₂ hcc
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix3sumCompositionAlt_eq_fromRows] at hAfg
        by_contra! hfX₁
        apply hAfg
        convert isTU (n + 2) (fn_of_sum_ne_inl hfX₁) g using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfX₁ i]
        rfl
      obtain ⟨j₀, y₀, hjy₀, hAxy0⟩ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Y₁, g j₀ = ◩y₀ ∧ A₁ x₁ y₀ ≠ 0
      · by_contra! hgY₁ -- because the `i₁`th row cannot be all `0`s
        apply hAfg
        convert zero_in_signTypeCastRange
        apply Matrix.det_eq_zero_of_row_eq_zero i₁
        intro z
        rw [matrix3sumCompositionAlt_eq_fromRows, Matrix.submatrix_apply, hix₁, Matrix.fromRows_apply_inl]
        cases hgz : g z with
        | inl => exact hgY₁ z _ hgz
        | inr => simp
      have hAxy1 : A₁ x₁ y₀ = 1 ∨ A₁ x₁ y₀ = -1
      · obtain ⟨s, hs⟩ := hA₁.apply x₁ y₀
        cases s with
        | zero =>
          exfalso
          apply hAxy0
          exact hs.symm
        | pos =>
          left
          exact hs.symm
        | neg =>
          right
          exact hs.symm
      obtain ⟨f', g', -, -, impossible⟩ := corollary1 hAfg i₁ j₀ (by convert hAxy1 <;> simp [matrix3sumCompositionAlt, *])
      apply impossible
      rw [(matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁).submatrix_shortTableauPivot hf hg, Matrix.submatrix_submatrix,
        hix₁, hjy₀, matrix3sumCompositionAlt_shortTableauPivot A₁ A₂ r₀ r₁ c₀ c₁ hAxy1]
      apply ih _ hccA₂ hcc _
      · sorry
      · sorry

end AlternativeMatrixDefinition


section ConversionStandardAlternative

lemma matrix3sumComposition_standard_toAlt_eq {β : Type} [Field β] {X₁ Y₁ X₂ Y₂ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ X₁ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ X₂ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Y₁ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Y₂ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (B₁ : Matrix X₁ Y₁ β) (B₂ : Matrix X₂ Y₂ β) (hX₁X₂ : X₁ ∩ X₂ = {x₀, x₁, x'}) (hY₁Y₂ : Y₁ ∩ Y₂ = {y₀, y₁, y'})
    {B} (hB : B = matrix3sumComposition_standard B₁ B₂ hX₁X₂ hY₁Y₂) :
    -- question: what is the correct way to introduce `B`, so that we have access to both `B.fst` and `B.snd`?
    -- note: this definition doesn't make sense unless `B.snd` is satisfied
    -- for example, `B₁` and `B₂` have to match on their intersection

    -- row and column membership
    have hrX₁ : {x₀, x₁, x'} ⊆ X₁ := hX₁X₂.symm.subset.trans Set.inter_subset_left
    have x₀inX₁ : x₀ ∈ X₁ := hrX₁ (Set.mem_insert x₀ {x₁, x'})
    have x₁inX₁ : x₁ ∈ X₁ := hrX₁ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have hcY₁ : {y₀, y₁, y'} ⊆ Y₁ := hY₁Y₂.symm.subset.trans Set.inter_subset_left
    have hcY₂ : {y₀, y₁, y'} ⊆ Y₂ := hY₁Y₂.symm.subset.trans Set.inter_subset_right
    have y₀inY₁ : y₀ ∈ Y₁ := hcY₁ (Set.mem_insert y₀ {y₁, y'})
    have y₀inY₂ : y₀ ∈ Y₂ := hcY₂ (Set.mem_insert y₀ {y₁, y'})
    have y₁inY₁ : y₁ ∈ Y₁ := hcY₁ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inY₂ : y₁ ∈ Y₂ := hcY₂ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    -- take submatrices of B₁ and B₂
    let A₁ : Matrix (X₁ \ {x₀, x₁}).Elem (Y₁ \ {y'}).Elem β := B₁.submatrix Set.diff_subset.elem Set.diff_subset.elem
    let A₂ : Matrix (X₂ \ {x'}).Elem (Y₂ \ {y₀, y₁}).Elem β := B₂.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- take columns from B₂
    let c₀ : (X₂ \ {x'}).Elem → β := fun i => B₂ (Set.diff_subset.elem i) ⟨y₀, y₀inY₂⟩
    let c₁ : (X₂ \ {x'}).Elem → β := fun i => B₂ (Set.diff_subset.elem i) ⟨y₁, y₁inY₂⟩
    -- take rows of B₁, but multiplied by `D₀⁻¹` on the left
    let v₀ : (Y₁ \ {y'}).Elem → β := B₁ ⟨x₀, x₀inX₁⟩ ∘ Set.diff_subset.elem
    let v₁ : (Y₁ \ {y'}).Elem → β := B₁ ⟨x₁, x₁inX₁⟩ ∘ Set.diff_subset.elem
    let D₀₁ : Matrix (Fin 2) (Fin 2) β :=
      !![B₁ ⟨x₀, x₀inX₁⟩ ⟨y₀, y₀inY₁⟩, B₁ ⟨x₀, x₀inX₁⟩ ⟨y₁, y₁inY₁⟩; B₁ ⟨x₁, x₁inX₁⟩ ⟨y₀, y₀inY₁⟩, B₁ ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩]
    let r₀ : (Y₁ \ {y'}).Elem → β := fun i => (D₀₁⁻¹ 0 0) * (v₀ i) + (D₀₁⁻¹ 0 1) * (v₁ i)
    let r₁ : (Y₁ \ {y'}).Elem → β := fun i => (D₀₁⁻¹ 1 0) * (v₀ i) + (D₀₁⁻¹ 1 1) * (v₁ i)
    -- statement
    B.fst = matrix3sumCompositionAlt A₁ A₂ r₀ r₁ c₀ c₁ := by
  intro _ _ _ _ _ _ _ _ _ A₁ A₂ c₀ c₁ v₀ v₁ D₀₁ r₀ r₁

  have hB₁₁ : B.fst.toBlocks₁₁ = A₁ := hB ▸ rfl
  have hB₁₂ : B.fst.toBlocks₁₂ = 0 := hB ▸ rfl
  have hB₂₂ : B.fst.toBlocks₂₂ = A₂ := hB ▸ rfl

  have hB₂₁ : B.fst.toBlocks₂₁ = (c₀ · * r₀ ·) + (c₁ · * r₁ ·) := by
    rw [hB]
    unfold matrix3sumComposition_standard
    simp_all only [HasSubset.Subset.elem, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
      false_or, Matrix.toBlocks_fromBlocks₂₁]
    ext i j
    simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or,
      Matrix.of_apply, Pi.add_apply]
    -- todo: need to use properties from `B.snd`
    if hi : i = x₀ then
      if hj : j = y₀ then
        -- aesop
        sorry
      else
        sorry
    else
      sorry

  rw [←B.fst.fromBlocks_toBlocks, hB₁₁, hB₁₂, hB₂₁, hB₂₂]
  rfl

end ConversionStandardAlternative


section CanonicalSigning

private lemma Matrix.Z2_2x2_nonsingular_form (A : Matrix (Fin 2) (Fin 2) Z2) (hA : IsUnit A) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, A.submatrix f g = 1 ∨ A.submatrix f g = !![1, 1; 0, 1] := by
  sorry

private def Matrix.toCanonicalSigning_3x3 (A : Matrix (Fin 3) (Fin 3) ℚ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  ⟨![1, A 0 0 * A 1 0, A 0 0 * A 1 0 * A 1 2 * A 2 2], ![A 0 0, A 0 1, A 0 0 * A 1 0 * A 1 2]⟩

-- todo: modify this definition to produce components of `matrix3sumCompositionAlt` + new assumptions
private noncomputable def matrix3sumComposition_toCanonicalSigning {X₁ Y₁ X₂ Y₂ : Set α}
  (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) ℚ) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ ℚ)
  (D₀ : Matrix (Fin 2) (Fin 2) ℚ) (D₁ : Matrix (Fin 2) Y₁ ℚ) (D₂ : Matrix X₂ (Fin 2) ℚ) (x₁ : X₁) (y₃ : Y₂) :
    Matrix (X₁ ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ Y₂) ℚ :=
  -- get multiplication factors to get 3×3 matrix containing `D₀` to canonical form
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


section MatroidThreeSum

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `M₁` and `M₂`. -/
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
  IsSum : (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition_standard hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_standard_X]
  apply Finite.Set.finite_union

lemma standardRepr3sumComposition_hasTuSigning {α : Type} [DecidableEq α] {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X)
    (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
    ((standardRepr3sumComposition_standard hXX hYY hXY hYX).fst).HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hS₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hS₂
  -- use matrix3sumComposition_toCanonicalSigning
  sorry

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂

end MatroidThreeSum
