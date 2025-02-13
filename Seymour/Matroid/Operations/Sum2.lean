import Seymour.Matroid.Notions.Regularity
import Seymour.ForMathlib.SetTheory
import Seymour.ForMathlib.MatrixPivot


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix_2sumComposition {β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

/-- `StandardRepresentation`-level 2-sum of two matroids.
The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def StandardRepr_2sum {a : α} {S₁ S₂ : StandardRepr α Z2} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
    StandardRepr α Z2 × Prop :=
  let A₁ : Matrix (S₁.X \ {a}).Elem S₁.Y.Elem Z2 := S₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  let A₂ : Matrix S₂.X.Elem (S₂.Y \ {a}).Elem Z2 := (S₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  let x : S₁.Y.Elem → Z2 := S₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
  let y : S₂.X.Elem → Z2 := (S₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
  ⟨
    ⟨
      (S₁.X \ {a}) ∪ S₂.X,
      S₁.Y ∪ (S₂.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨S₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_inter_both_wo ha, S₂.hXY.disjoint_sdiff_right⟩⟩,
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (S₁.X ⫗ S₂.X ∧ S₁.Y ⫗ S₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is2sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  S : StandardRepr α Z2
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  hM : S.toMatroid = M
  hM₁ : S₁.toMatroid = M₁
  hM₂ : S₂.toMatroid = M₂
  a : α
  ha : S₁.X ∩ S₂.Y = {a}
  hXY : S₂.X ⫗ S₁.Y
  IsSum : (StandardRepr_2sum ha hXY).fst = S
  IsValid : (StandardRepr_2sum ha hXY).snd

lemma Matrix_2sumComposition_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) (x : Y₁ → ℚ) (y : X₂ → ℚ) :
    (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  sorry

lemma StandardRepr_2sum_B {S₁ S₂ : StandardRepr α Z2} {a : α} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
    ∃ haX₁ : a ∈ S₁.X, ∃ haY₂ : a ∈ S₂.Y,
      (StandardRepr_2sum ha hXY).fst.B =
      (Matrix_2sumComposition
        (S₁.B ∘ Set.diff_subset.elem)
        (S₁.B ⟨a, haX₁⟩)
        (S₂.B · ∘ Set.diff_subset.elem)
        (S₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ S₁.X ∩ S₂.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma StandardRepr_2sum_hasTuSigning {S₁ S₂ : StandardRepr α Z2} {a : α} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y)
    (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
    (StandardRepr_2sum ha hXY).fst.HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hS₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hS₂
  obtain ⟨haX₁, haY₂, hB⟩ := StandardRepr_2sum_B ha hXY
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
  let B' := Matrix_2sumComposition A₁' x' A₂' y' -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply Matrix_2sumComposition_isTotallyUnimodular
    · apply hB₁.comp_rows
    · apply hB₂.comp_cols
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all [B']
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        simp only [Matrix.fromBlocks_apply₂₁, B', hx', hy', abs_mul]
        apply Z2val_toRat_mul_Z2val_toRat
      | inr j₂ =>
        specialize hA₂ i₂ j₂
        simp_all [x', y', A₁', A₂', B']

/-- Any 2-sum of regular matroids is a regular matroid.
This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨_, _, _, rfl, rfl, rfl, _, _, _, rfl, -⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply StandardRepr_2sum_hasTuSigning
  · exact hM₁
  · exact hM₂
