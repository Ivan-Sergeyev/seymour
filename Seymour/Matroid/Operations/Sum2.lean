import Seymour.Basic.Sets
import Seymour.Matrix.Pivoting
import Seymour.Matrix.MinimalTUViolation
import Seymour.Matroid.Notions.Regularity


variable {α : Type} [DecidableEq α]

section MatrixLevel

/-- Operands of 2-sum composition on matrix level. -/
structure Matrix_2sum.Operands (X₁ Y₁ X₂ Y₂ : Set α) (β : Type) where
  A₁ : Matrix X₁ Y₁ β
  x : Y₁ → β
  A₂ : Matrix X₂ Y₂ β
  y : X₂ → β

def Matrix_2sum.Operands.B₁ {X₁ Y₁ X₂ Y₂ : Set α} {β : Type} (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ β) :=
  Matrix.fromRows Operands.A₁ (Matrix.row Unit Operands.x)

def Matrix_2sum.Operands.B₂ {X₁ Y₁ X₂ Y₂ : Set α} {β : Type} (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ β) :=
  Matrix.fromCols (Matrix.col Unit Operands.y) Operands.A₂

def Matrix_2sum.D {X₁ Y₁ X₂ Y₂ : Set α} {β : Type} [Semiring β] (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ β) :=
  fun i j => Operands.y i * Operands.x j

def Matrix.IsRankOne {X Y : Set α} {β : Type} [Ring β] (A : Matrix X Y β) : Prop :=
  ∃ x : Y → β, ∀ i : X, A i = x ∨ A i = -x ∨ A i = 0

/-- 2-sum composition on matrix level. -/
abbrev Matrix_2sum.Composition {X₁ Y₁ X₂ Y₂ : Set α} {β : Type} [Semiring β] (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks Operands.A₁ 0 (Matrix_2sum.D Operands) Operands.A₂

lemma Matrix_2sum.Composition_isTotallyUnimodular_left {X₁ Y₁ X₂ Y₂ : Set α} (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ)
    (hB₁ : Operands.B₁.IsTotallyUnimodular) :
    (Matrix.fromRows Operands.A₁ (Matrix_2sum.D Operands)).IsTotallyUnimodular :=
  sorry

lemma Matrix_2sum.Composition_isTotallyUnimodular_bottom {X₁ Y₁ X₂ Y₂ : Set α} (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ)
    (hB₁ : Operands.B₂.IsTotallyUnimodular) :
    (Matrix.fromCols (Matrix_2sum.D Operands) Operands.A₂).IsTotallyUnimodular :=
  sorry

/-- The property that a 2-sum composition contains a minimal violation matrix of order `k`.
  (This doesn't actually hold, but rather is used in proof by contradiction.) -/
def Matrix_2sum.Composition_contains_MVM {X₁ Y₁ X₂ Y₂ : Set α} {β : Type} [CommRing β]
    (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ β) (k : ℕ) : Prop :=
  (Matrix_2sum.Composition Operands).ContainsMinimalTUViolating k

/-- If a 2-sum composition of TU matrices contains a minimal violating matrix of order `k ≥ 3`,
  then there is a 2-sum composition of TU matrices containing a minimal violating matrix of order `k - 1`. -/
lemma Matrix_2sum.Composition_contains_smaller_MVM {X₁ Y₁ X₂ Y₂ : Set α} {k : ℕ}
    (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ)
    (hB₁ : Operands.B₁.IsTotallyUnimodular) (hB₂ : Operands.B₂.IsTotallyUnimodular)
    (hk : k ≥ 3) (hMVM : Matrix_2sum.Composition_contains_MVM Operands k) :
    ∃ Operands' : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ,
      Operands'.B₁.IsTotallyUnimodular ∧ Operands'.B₂.IsTotallyUnimodular ∧
      Matrix_2sum.Composition_contains_MVM Operands' (k - 1) :=
  sorry

/-- No 2-sum composition of TU matrices contains a 2 × 2 minimal violating matrix. -/
lemma Matrix_2sum.Composition_contains_no_2x2_MVM {X₁ Y₁ X₂ Y₂ : Set α} {k : ℕ}
    (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ)
    (hB₁ : Operands.B₁.IsTotallyUnimodular) (hB₂ : Operands.B₂.IsTotallyUnimodular) :
    ¬Matrix_2sum.Composition_contains_MVM Operands 2 :=
  sorry

/-- 2-sum composition of TU matrices is TU. -/
lemma Matrix_2sum.Composition_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α} (Operands : Matrix_2sum.Operands X₁ Y₁ X₂ Y₂ ℚ)
    (hB₁ : Operands.B₁.IsTotallyUnimodular) (hB₂ : Operands.B₂.IsTotallyUnimodular) :
    (Matrix_2sum.Composition Operands).IsTotallyUnimodular := by
  sorry

end MatrixLevel


section StandardReprLevel

variable {α : Type} [DecidableEq α] [∀ a, ∀ X : Set α, Decidable (a ∈ X)] -- fixme: some things break without this hack

structure StandardRepr_2sum.Operands (α : Type) [DecidableEq α] where
  a : α
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  ha : S₁.X ∩ S₂.Y = {a}
  hXY : S₂.X ⫗ S₁.Y

def StandardRepr_2sum.Operands.from {S₁ S₂ : StandardRepr α Z2} {a : α} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
    StandardRepr_2sum.Operands α :=
  ⟨a, S₁, S₂, ha, hXY⟩

-- -- todo: the following lines don't seem to help resolve the issues with inferring decidability on α
-- def StandardRepr_2sum.Operands.decmemX₁ (Operands : StandardRepr_2sum.Operands α) := Operands.S₁.decmemX
-- def StandardRepr_2sum.Operands.decmemY₁ (Operands : StandardRepr_2sum.Operands α) := Operands.S₁.decmemY
-- def StandardRepr_2sum.Operands.decmemX₂ (Operands : StandardRepr_2sum.Operands α) := Operands.S₂.decmemX
-- def StandardRepr_2sum.Operands.decmemY₂ (Operands : StandardRepr_2sum.Operands α) := Operands.S₂.decmemY

-- attribute [instance] StandardRepr_2sum.Operands.decmemX₁
-- attribute [instance] StandardRepr_2sum.Operands.decmemY₁
-- attribute [instance] StandardRepr_2sum.Operands.decmemX₂
-- attribute [instance] StandardRepr_2sum.Operands.decmemY₂

def StandardRepr_2sum.Operands.X₁ma (Operands : StandardRepr_2sum.Operands α) := Operands.S₁.X \ {Operands.a}
def StandardRepr_2sum.Operands.Y₁ (Operands : StandardRepr_2sum.Operands α) := Operands.S₁.Y
def StandardRepr_2sum.Operands.X₂ (Operands : StandardRepr_2sum.Operands α) := Operands.S₂.X
def StandardRepr_2sum.Operands.Y₂ma (Operands : StandardRepr_2sum.Operands α) := Operands.S₂.Y \ {Operands.a}

def StandardRepr_2sum.Operands.a_in_S₁_X (Operands : StandardRepr_2sum.Operands α) :
    Operands.a ∈ Operands.S₁.X :=
  Set.mem_of_mem_inter_left (by rw [Operands.ha]; rfl)

def StandardRepr_2sum.Operands.a_in_S₂_Y (Operands : StandardRepr_2sum.Operands α) :
    Operands.a ∈ Operands.S₂.Y :=
  Set.mem_of_mem_inter_right (by rw [Operands.ha]; rfl)

def StandardRepr_2sum.Operands.intoMatrixOperands (Operands : StandardRepr_2sum.Operands α) :
    Matrix_2sum.Operands Operands.X₁ma Operands.Y₁ Operands.X₂ Operands.Y₂ma Z2 where
  A₁ := Operands.S₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  x := Operands.S₁.B ⟨Operands.a, Operands.a_in_S₁_X⟩ -- the bottom row of `B₁`
  A₂ := (Operands.S₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  y := (Operands.S₂.B · ⟨Operands.a, Operands.a_in_S₂_Y⟩) -- the left column of `B₂`

lemma StandardRepr_2sum.Operands.Disjoint_union_X_union_Y (Operands : StandardRepr_2sum.Operands α) :
    Operands.X₁ma ∪ Operands.X₂ ⫗ Operands.Y₁ ∪ Operands.Y₂ma := by
  rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
  exact ⟨⟨Operands.S₁.hXY.disjoint_sdiff_left, Operands.hXY⟩,
          ⟨disjoint_of_singleton_inter_both_wo Operands.ha, Operands.S₂.hXY.disjoint_sdiff_right⟩⟩

def StandardRepr_2sum.Composition (Operands : StandardRepr_2sum.Operands α) :
    StandardRepr α Z2 where
  X := Operands.X₁ma ∪ Operands.X₂
  Y := Operands.Y₁ ∪ Operands.Y₂ma
  hXY := Operands.Disjoint_union_X_union_Y
  B := (Matrix_2sum.Composition Operands.intoMatrixOperands).toMatrixUnionUnion -- fixme: fails without the decidability hack
  decmemX := inferInstance -- fixme: fails without the decidability hack
  decmemY := inferInstance -- fixme: fails without the decidability hack

lemma StandardRepr_2sum.Composition.X_eq (Operands : StandardRepr_2sum.Operands α) :
    (StandardRepr_2sum.Composition Operands).X = Operands.X₁ma ∪ Operands.X₂ :=
  rfl

def StandardRepr_2sum.IsCompositionValid (Operands : StandardRepr_2sum.Operands α) : Prop :=
  Operands.S₁.X ⫗ Operands.S₂.X ∧
  Operands.S₁.Y ⫗ Operands.S₂.Y ∧
  Operands.intoMatrixOperands.x ≠ 0 ∧
  Operands.intoMatrixOperands.y ≠ 0

lemma StandardRepr_2sum.Composition.B_eq (Operands : StandardRepr_2sum.Operands α) :
    ∃ haX₁ : Operands.a ∈ Operands.S₁.X, ∃ haY₂ : Operands.a ∈ Operands.S₂.Y,
      (StandardRepr_2sum.Composition Operands).B =
      (Matrix_2sum.Composition
        ⟨(Operands.S₁.B ∘ Set.diff_subset.elem),
        (Operands.S₁.B ⟨Operands.a, haX₁⟩),
        (Operands.S₂.B · ∘ Set.diff_subset.elem),
        (Operands.S₂.B · ⟨Operands.a, haY₂⟩)⟩
      ).toMatrixUnionUnion :=
  have haXY : Operands.a ∈ Operands.S₁.X ∩ Operands.S₂.Y := Operands.ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma StandardRepr_2sum.Composition_hasTuSigning {Operands : StandardRepr_2sum.Operands α}
    (hS₁ : Operands.S₁.HasTuSigning) (hS₂ : Operands.S₂.HasTuSigning) :
    (StandardRepr_2sum.Composition Operands).HasTuSigning := by
  let S₁ := Operands.S₁
  let S₂ := Operands.S₂
  let a := Operands.a
  let haX₁ := Operands.a_in_S₁_X
  let haY₂ := Operands.a_in_S₂_Y

  obtain ⟨B₁, hB₁, hBB₁⟩ := hS₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hS₂
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepr_2sum.Composition.B_eq Operands
  let x' : S₁.Y.Elem → ℚ := B₁ ⟨a, haX₁⟩
  let y' : S₂.X.Elem → ℚ := (B₂ · ⟨a, haY₂⟩)
  let A₁' : Matrix (S₁.X \ {a}).Elem S₁.Y.Elem ℚ := B₁ ∘ Set.diff_subset.elem
  let A₂' : Matrix S₂.X.Elem (S₂.Y \ {a}).Elem ℚ := (B₂ · ∘ Set.diff_subset.elem)
  have hA₁ :
    ∀ i : (S₁.X \ {a}).Elem, ∀ j : S₁.Y.Elem,
      |A₁' i j| = (S₁.B (Set.diff_subset.elem i) j).val
  · intro i j
    exact hBB₁ (Set.diff_subset.elem i) j
  have hA₂ :
    ∀ i : S₂.X.Elem, ∀ j : (S₂.Y \ {a}).Elem,
      |A₂' i j| = (S₂.B i (Set.diff_subset.elem j)).val
  · intro i j
    exact hBB₂ i (Set.diff_subset.elem j)
  have hx' : ∀ j, |x' j| = (S₁.B ⟨a, haX₁⟩ j).val
  · intro j
    exact hBB₁ ⟨a, haX₁⟩ j
  have hy' : ∀ i, |y' i| = (S₂.B i ⟨a, haY₂⟩).val
  · intro i
    exact hBB₂ i ⟨a, haY₂⟩
  let B' := Matrix_2sum.Composition ⟨A₁', x', A₂', y'⟩ -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply Matrix_2sum.Composition_isTotallyUnimodular
    · convert hB₁.comp_rows
        (fun i : (S₁.X \ {a}).Elem ⊕ Unit => i.casesOn Set.diff_subset.elem (fun _ => ⟨a, haX₁⟩))
      aesop
    · convert hB₂.comp_cols
        (fun j : Unit ⊕ (S₂.Y \ {a}).Elem => j.casesOn (fun _ => ⟨a, haY₂⟩) Set.diff_subset.elem)
      aesop
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all [B']
        sorry -- fixme: automatic inference doesn't pierce definitions, have to unfold manually?
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        simp only [Matrix.fromBlocks_apply₂₁, B', hx', hy', abs_mul]
        -- apply Z2val_toRat_mul_Z2val_toRat
        sorry -- fixme: automatic inference doesn't pierce definitions, have to unfold manually?
      | inr j₂ =>
        specialize hA₂ i₂ j₂
        -- simp_all [x', y', A₁', A₂', B']
        sorry -- fixme: automatic inference doesn't pierce definitions, have to unfold manually?

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is2sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  Operands : StandardRepr_2sum.Operands α
  hM₁ : M₁ = Operands.S₁.toMatroid
  hM₂ : M₂ = Operands.S₂.toMatroid
  hM : M = (StandardRepr_2sum.Composition Operands).toMatroid
  IsSumValid : StandardRepr_2sum.IsCompositionValid Operands
  hS₁ : Finite Operands.S₁.X
  hS₂ : Finite Operands.S₂.X

instance Matroid.Is2sumOf.finX₁ma {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) :
    Finite hM.Operands.X₁ma := by
  have finX₁ := hM.hS₁
  apply Finite.Set.finite_diff

instance Matroid.Is2sumOf.finX₂ {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) :
    Finite hM.Operands.X₂ := by
  exact hM.hS₂

instance Matroid.Is2sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) :
    Finite (StandardRepr_2sum.Composition hM.Operands).X := by
  rw [StandardRepr_2sum.Composition.X_eq]
  apply Finite.Set.finite_union

/-- Any 2-sum of regular matroids is a regular matroid.
    This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, rfl, rfl, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply StandardRepr_2sum.Composition_hasTuSigning
  · exact hM₁
  · exact hM₂
