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

private lemma standardRepr1sumComposition_eq_disjointSum_aux_full {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ Z2) (Aᵣ : Matrix Xᵣ Yᵣ Z2) (hYY : Yₗ ⫗ Yᵣ) :
    (⊞ Aₗ 0 0 Aᵣ).toMatrixUnionUnion.toMatroid = Matroid.disjointSum Aₗ.toMatroid Aᵣ.toMatroid hYY := by
  ext I hI
  · simp
  sorry

/-- Matroid constructed from a valid 1-sum of binary matroids is the same as disjoint sum of matroids constructed from them. -/
lemma standardRepr1sumComposition_eq_disjointSum {Sₗ Sᵣ : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (valid : (standardRepr1sumComposition hXY hYX).snd) :
    (standardRepr1sumComposition hXY hYX).fst.toMatroid = Matroid.disjointSum Sₗ.toMatroid Sᵣ.toMatroid (by
      simp [StandardRepr.toMatroid, StandardRepr.toFull, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
  convert standardRepr1sumComposition_eq_disjointSum_aux_full Sₗ.toFull Sᵣ.toFull (by aesop)
  have hXXYY : (Sₗ.X ∪ Sᵣ.X) ∪ (Sₗ.Y ∪ Sᵣ.Y) = (Sₗ.X ∪ Sₗ.Y) ∪ (Sᵣ.X ∪ Sᵣ.Y)
  · tauto_set
  ext I hI
  · simp [standardRepr1sumComposition]
    tauto_set
  have hXX : Sₗ.X ⫗ Sᵣ.X := sorry -- Is it needed? Then add as assumption!
  have hYY : Sₗ.Y ⫗ Sᵣ.Y := sorry -- Is it needed? Then add as assumption!
  have hXYₗ := Sₗ.hXY
  have hXYᵣ := Sᵣ.hXY
  rw [Matrix.toMatroid_indep_iff_submatrix, StandardRepr.toMatroid_indep_iff_submatrix]
  constructor
  <;> intro ⟨hI, hISS⟩
  <;> use hXXYY ▸ hI
  · convert hISS
    ext i j
    cases hj : j.toSum with
    | inl jₗ =>
      simp [standardRepr1sumComposition, matrix1sumComposition, StandardRepr.toFull_def, hj]
      if hiXₗ : i.val ∈ Sₗ.X then
        simp_all [Matrix.toMatrixUnionUnion]
        generalize_proofs hhi
        if hji : j = ⟨i.val, hhi⟩ then
          have hjₗ : jₗ = ⟨i, hiXₗ⟩
          · simp_all
          rw [hji, hjₗ, Matrix.one_apply_eq, Matrix.one_apply_eq]
        else
          have hjₗ : jₗ ≠ ⟨i, hiXₗ⟩
          · intro contr
            apply hji
            apply SetCoe.ext
            have hjj : j.val = jₗ.val
            · have := toSum_toUnion j
              simp_all
            simp [hjj, congr_arg Subtype.val contr]
          rw [Matrix.one_apply_ne hji, Matrix.one_apply_ne hjₗ]
      else
        have hiXᵣ : i.val ∈ Sᵣ.X
        · sorry
        simp_all [Matrix.toMatrixUnionUnion]
        generalize_proofs hiXYXY hiXX
        dsimp [standardRepr1sumComposition] at hiXX
        have hiₗ : i.val ∈ Sₗ.X ∪ Sₗ.Y
        · sorry
        if hji : j = ⟨i.val, hiXX⟩ then
          rw [hji, Matrix.one_apply_eq]
          sorry
        else
          sorry
    | inr jᵣ => sorry
  · convert hISS
    ext i j
    cases hj : j.toSum with
    | inl jₗ =>
      simp [standardRepr1sumComposition, matrix1sumComposition, StandardRepr.toFull_def, hj]
      if hiXₗ : i.val ∈ Sₗ.X then
        simp_all [Matrix.toMatrixUnionUnion]
        generalize_proofs hhi
        if hji : j = ⟨i.val, hhi⟩ then
          have hjₗ : jₗ = ⟨i, hiXₗ⟩
          · simp_all
          rw [hji, hjₗ, Matrix.one_apply_eq, Matrix.one_apply_eq]
        else
          have hjₗ : jₗ ≠ ⟨i, hiXₗ⟩
          · intro contr
            apply hji
            apply SetCoe.ext
            have hjj : j.val = jₗ.val
            · have := toSum_toUnion j
              simp_all
            simp [hjj, congr_arg Subtype.val contr]
          rw [Matrix.one_apply_ne hji, Matrix.one_apply_ne hjₗ]
      else
        have hiXᵣ : i.val ∈ Sᵣ.X
        · sorry
        sorry
    | inr jᵣ => sorry

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
