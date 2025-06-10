import Seymour.Matroid.Properties.Regularity

/-!
# Matroid 1-sum

Here we study the 1-sum of matroids (starting with the 1-sum of matrices).
-/

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev matrix1sumComposition {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

variable {α : Type} [DecidableEq α]

/-- `StandardRepr`-level 1-sum of two matroids.
    It checks that everything is disjoint (returned as `.snd` of the output). -/
def standardRepr1sumComposition {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      (matrix1sumComposition Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  ⟩

/-- Matroid `M` is a result of 1-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop` but treat it as a predicate. -/
structure Matroid.Is1sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr1sumComposition hXY hYX).fst = S
  IsValid : (standardRepr1sumComposition hXY hYX).snd

instance Matroid.Is1sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is1sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, Sₗ, Sᵣ, _, _, _, _, _, _, _, rfl, _⟩ := hM
  exact Finite.Set.finite_union Sₗ.X Sᵣ.X

/-- Matroid constructed from a valid 1-sum of binary matroids is the same as disjoint sum of matroids constructed from them. -/
lemma standardRepr1sumComposition_eq_disjointSum {Sₗ Sᵣ : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (valid : (standardRepr1sumComposition hXY hYX).snd) :
    (standardRepr1sumComposition hXY hYX).fst.toMatroid = Matroid.disjointSum Sₗ.toMatroid Sᵣ.toMatroid (by
      simp [StandardRepr.toMatroid, StandardRepr.toVectorMatroid, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  ext I hI
  · simp only [StandardRepr.toMatroid_E, Set.mem_union, Matroid.disjointSum_ground_eq, standardRepr1sumComposition]
    tauto
  · simp only [StandardRepr.toMatroid_indep_iff, Matroid.disjointSum_indep_iff, StandardRepr.toMatroid_E,
      Set.inter_subset_right, exists_true_left]
    constructor
    <;> intro linearlyI
    · sorry
    · use hI
      sorry

/-- A valid 1-sum of binary matroids is commutative. -/
lemma standardRepr1sumComposition_comm {Sₗ Sᵣ : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (valid : (standardRepr1sumComposition hXY hYX).snd) :
    (standardRepr1sumComposition hXY hYX).fst.toMatroid = (standardRepr1sumComposition hYX.symm hXY.symm).fst.toMatroid := by
  rw [
    standardRepr1sumComposition_eq_disjointSum valid,
    standardRepr1sumComposition_eq_disjointSum ⟨valid.left.symm, valid.right.symm⟩,
    Matroid.disjointSum_comm]

lemma standardRepr1sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr1sumComposition hXY hYX).fst.B.HasTuSigning :=
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  ⟨_, (Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ).toMatrixUnionUnion, (fun i j =>
    show |((matrix1sumComposition Bₗ Bᵣ ∘ _) i ∘ _) j| = ZMod.val (((_ ∘ _) i ∘ _) j)
    from Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸
      i.toSum.casesOn (fun iₗ => j.toSum.casesOn (hBBₗ iₗ) ↓abs_zero) (fun iᵣ => j.toSum.casesOn ↓abs_zero (hBBᵣ iᵣ)))⟩

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is1sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is1sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr1sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
