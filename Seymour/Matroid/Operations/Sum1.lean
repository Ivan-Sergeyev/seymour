import Seymour.Matroid.Notions.Regularity


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev Matrix_1sumComposition {β : Type} [Zero β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 0 A₂

/-- `StandardRepr`-level 1-sum of two matroids.
It checks that everything is disjoint (returned as `.snd` of the output). -/
def StandardRepr_1sumComposition {M₁ M₂ : StandardRepr α Z2} (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      M₁.X ∪ M₂.X,
      M₁.Y ∪ M₂.Y,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨M₁.hXY, hYX.symm⟩, ⟨hXY, M₂.hXY⟩⟩,
      (Matrix_1sumComposition M₁.B M₂.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y
  ⟩

/-- Binary matroid `M` is a result of 1-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is1sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  B : StandardRepr α Z2
  B₁ : StandardRepr α Z2
  B₂ : StandardRepr α Z2
  hM : B.toMatroid = M
  hM₁ : B₁.toMatroid = M₁
  hM₂ : B₂.toMatroid = M₂
  hXY : B₁.X ⫗ B₂.Y
  hYX : B₁.Y ⫗ B₂.X
  is1sum : B = (StandardRepr_1sumComposition hXY hYX).fst
  isValid : (StandardRepr_1sumComposition hXY hYX).snd

/-- Matroid constructed from a valid 1-sum of binary matroids is the same as disjoint sum of matroids constructed from them. -/
lemma StandardRepr_1sumComposition_as_disjoint_sum {M₁ M₂ : StandardRepr α Z2} {hXY : M₁.X ⫗ M₂.Y} {hYX : M₁.Y ⫗ M₂.X}
    (valid : (StandardRepr_1sumComposition hXY hYX).snd) :
    (StandardRepr_1sumComposition hXY hYX).fst.toMatroid = Matroid.disjointSum M₁.toMatroid M₂.toMatroid (by
      simp [StandardRepr.toMatroid, StandardRepr.toVectorMatroid, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  ext
  · sorry
  · sorry

/-- A valid 1-sum of binary matroids is commutative. -/
lemma StandardRepr_1sumComposition_comm {M₁ M₂ : StandardRepr α Z2} {hXY : M₁.X ⫗ M₂.Y} {hYX : M₁.Y ⫗ M₂.X}
    (valid : (StandardRepr_1sumComposition hXY hYX).snd) :
    (StandardRepr_1sumComposition hXY hYX).fst.toMatroid = (StandardRepr_1sumComposition hYX.symm hXY.symm).fst.toMatroid := by
  rw [
    StandardRepr_1sumComposition_as_disjoint_sum valid,
    StandardRepr_1sumComposition_as_disjoint_sum ⟨valid.left.symm, valid.right.symm⟩,
    Matroid.disjointSum_comm]

lemma StandardRepr_1sumComposition_hasTuSigning {M₁ M₂ : StandardRepr α Z2}
    (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) (hM₁ : M₁.HasTuSigning) (hM₂ : M₂.HasTuSigning) :
    (StandardRepr_1sumComposition hXY hYX).fst.HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hM₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hM₂
  have hB : (StandardRepr_1sumComposition hXY hYX).fst.B = (Matrix_1sumComposition M₁.B M₂.B).toMatrixUnionUnion
  · rfl
  let B' := Matrix_1sumComposition B₁ B₂ -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · exact (Matrix.fromBlocks_isTotallyUnimodular hB₁ hB₂).toMatrixUnionUnion
  · intro i j
    simp only [hB, B', Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hBB₁ i₁ j₁
        simp_all
      | inr j₂ =>
        simp_all
    | inr i₂ =>
      cases j.toSum with
      | inl j₁ =>
        simp_all
      | inr j₂ =>
        specialize hBB₂ i₂ j₂
        simp_all

/-- Any 1-sum of regular matroids is a regular matroid.
This is the first of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is1sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is1sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  obtain ⟨_, _, _, rfl, rfl, rfl, -, -, rfl, -⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply StandardRepr_1sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂
