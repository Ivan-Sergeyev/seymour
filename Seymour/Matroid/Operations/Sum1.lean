import Seymour.Matroid.Notions.Regularity


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev Matrix_1sumComposition {β : Type} [Zero β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (A₂ : Matrix X₂ Y₂ β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 0 A₂

/-- `StandardRepr`-level 1-sum of two matroids.
It checks that everything is disjoint (returned as `.snd` of the output). -/
def StandardRepr_1sumComposition {S₁ S₂ : StandardRepr α Z2} (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      S₁.X ∪ S₂.X,
      S₁.Y ∪ S₂.Y,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨S₁.hXY, hYX.symm⟩, ⟨hXY, S₂.hXY⟩⟩,
      (Matrix_1sumComposition S₁.B S₂.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    S₁.X ⫗ S₂.X ∧ S₁.Y ⫗ S₂.Y
  ⟩

/-- Matroid `M` is a result of 1-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is1sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  S : StandardRepr α Z2
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  hS : Finite S.X -- TODO infer automatically
  hS₁ : Finite S₁.X
  hS₂ : Finite S₂.X
  hM : S.toMatroid = M
  hM₁ : S₁.toMatroid = M₁
  hM₂ : S₂.toMatroid = M₂
  hXY : S₁.X ⫗ S₂.Y
  hYX : S₁.Y ⫗ S₂.X
  IsSum : (StandardRepr_1sumComposition hXY hYX).fst = S
  IsValid : (StandardRepr_1sumComposition hXY hYX).snd

/-- Matroid constructed from a valid 1-sum of binary matroids is the same as disjoint sum of matroids constructed from them. -/
lemma StandardRepr_1sumComposition_as_disjointSum {S₁ S₂ : StandardRepr α Z2} {hXY : S₁.X ⫗ S₂.Y} {hYX : S₁.Y ⫗ S₂.X}
    (valid : (StandardRepr_1sumComposition hXY hYX).snd) :
    (StandardRepr_1sumComposition hXY hYX).fst.toMatroid = Matroid.disjointSum S₁.toMatroid S₂.toMatroid (by
      simp [StandardRepr.toMatroid, StandardRepr.toVectorMatroid, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  ext I hI
  · simp only [StandardRepr.toMatroid_E, Set.mem_union, Matroid.disjointSum_ground_eq, StandardRepr_1sumComposition]
    tauto
  · simp only [StandardRepr.toMatroid_indep_iff, Matroid.disjointSum_indep_iff, StandardRepr.toMatroid_E,
      Set.inter_subset_right, exists_true_left]
    constructor <;> intro linearlyI
    · sorry
    · use hI
      sorry

/-- A valid 1-sum of binary matroids is commutative. -/
lemma StandardRepr_1sumComposition_comm {S₁ S₂ : StandardRepr α Z2} {hXY : S₁.X ⫗ S₂.Y} {hYX : S₁.Y ⫗ S₂.X}
    (valid : (StandardRepr_1sumComposition hXY hYX).snd) :
    (StandardRepr_1sumComposition hXY hYX).fst.toMatroid = (StandardRepr_1sumComposition hYX.symm hXY.symm).fst.toMatroid := by
  rw [
    StandardRepr_1sumComposition_as_disjointSum valid,
    StandardRepr_1sumComposition_as_disjointSum ⟨valid.left.symm, valid.right.symm⟩,
    Matroid.disjointSum_comm]

lemma StandardRepr_1sumComposition_hasTuSigning {S₁ S₂ : StandardRepr α Z2}
    (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
    (StandardRepr_1sumComposition hXY hYX).fst.HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hS₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hS₂
  have hB : (StandardRepr_1sumComposition hXY hYX).fst.B = (Matrix_1sumComposition S₁.B S₂.B).toMatrixUnionUnion
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
  obtain ⟨_, _, _, _, _, _, rfl, rfl, rfl, _, _, rfl, -⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply StandardRepr_1sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂

#print axioms StandardRepr_1sumComposition_hasTuSigning
