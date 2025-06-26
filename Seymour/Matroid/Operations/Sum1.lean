import Seymour.Matroid.Properties.Regularity

/-!
# Matroid 1-sum

Here we study the 1-sum of matroids (starting with the 1-sum of matrices).
-/

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrixSum1 {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

variable {α : Type} [DecidableEq α]

/-- `StandardRepr`-level 1-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum1 {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  open scoped Classical in if
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  then
    some ⟨
      -- row indices
      Sₗ.X ∪ Sᵣ.X,
      -- col indices
      Sₗ.Y ∪ Sᵣ.Y,
      -- row and col indices are disjoint
      by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
         exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      -- standard representation matrix
      (matrixSum1 Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      -- decidability of row indices
      inferInstance,
      -- decidability of col indices
      inferInstance⟩
    else
      none

/-- Binary matroid `M` is a result of 1-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop` but treat it as a predicate. -/
structure Matroid.Is1sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hXₗ : Finite Sₗ.X
  hXᵣ : Finite Sᵣ.X
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  hS : standardReprSum1 hXY hYX = some S

-- private lemma standardReprSum1_eq_disjointSum_aux_full {Xₗ Yₗ Xᵣ Yᵣ : Set α}
--     [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Yᵣ)]
--     (Aₗ : Matrix Xₗ Yₗ Z2) (Aᵣ : Matrix Xᵣ Yᵣ Z2) (hYY : Yₗ ⫗ Yᵣ) :
--     (⊞ Aₗ 0 0 Aᵣ).toMatrixUnionUnion.toMatroid = Matroid.disjointSum Aₗ.toMatroid Aᵣ.toMatroid hYY := by
--   ext I hI
--   · simp
--   sorry

-- lemma standardReprSum1_eq_disjointSum {Sₗ Sᵣ : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
--     (valid : (standardReprSum1 hXY hYX).snd) :
--     (standardReprSum1 hXY hYX).fst.toMatroid = Matroid.disjointSum Sₗ.toMatroid Sᵣ.toMatroid (by
--       simp [StandardRepr.toMatroid, StandardRepr.toFull, Set.disjoint_union_left, Set.disjoint_union_right]
--       exact ⟨⟨valid.left, hYX⟩, ⟨hXY, valid.right⟩⟩) := by
--   convert standardReprSum1_eq_disjointSum_aux_full Sₗ.toFull Sᵣ.toFull (by aesop)
--   have hXXYY : (Sₗ.X ∪ Sᵣ.X) ∪ (Sₗ.Y ∪ Sᵣ.Y) = (Sₗ.X ∪ Sₗ.Y) ∪ (Sᵣ.X ∪ Sᵣ.Y)
--   · tauto_set
--   ext I hI
--   · simp [standardReprSum1]
--     tauto_set
--   have hXX : Sₗ.X ⫗ Sᵣ.X := sorry -- Is it needed? Then add as assumption!
--   have hYY : Sₗ.Y ⫗ Sᵣ.Y := sorry -- Is it needed? Then add as assumption!
--   have hXYₗ := Sₗ.hXY
--   have hXYᵣ := Sᵣ.hXY
--   rw [Matrix.toMatroid_indep_iff_submatrix, StandardRepr.toMatroid_indep_iff_submatrix]
--   constructor
--   <;> intro ⟨hI, hISS⟩
--   <;> use hXXYY ▸ hI
--   · convert hISS
--     ext i j
--     cases hj : j.toSum with
--     | inl jₗ =>
--       simp [standardReprSum1, matrixSum1, StandardRepr.toFull_def, hj]
--       if hiXₗ : i.val ∈ Sₗ.X then
--         simp_all [Matrix.toMatrixUnionUnion]
--         generalize_proofs hhi
--         if hji : j = ⟨i.val, hhi⟩ then
--           have hjₗ : jₗ = ⟨i, hiXₗ⟩
--           · simp_all
--           rw [hji, hjₗ, Matrix.one_apply_eq, Matrix.one_apply_eq]
--         else
--           have hjₗ : jₗ ≠ ⟨i, hiXₗ⟩
--           · intro contr
--             apply hji
--             apply SetCoe.ext
--             have hjj : j.val = jₗ.val
--             · have := toSum_toUnion j
--               simp_all
--             simp [hjj, congr_arg Subtype.val contr]
--           rw [Matrix.one_apply_ne hji, Matrix.one_apply_ne hjₗ]
--       else
--         have hiXᵣ : i.val ∈ Sᵣ.X
--         · sorry
--         simp_all [Matrix.toMatrixUnionUnion]
--         generalize_proofs hiXYXY hiXX
--         dsimp [standardReprSum1] at hiXX
--         have hiₗ : i.val ∈ Sₗ.X ∪ Sₗ.Y
--         · sorry
--         if hji : j = ⟨i.val, hiXX⟩ then
--           rw [hji, Matrix.one_apply_eq]
--           sorry
--         else
--           sorry
--     | inr jᵣ => sorry
--   · convert hISS
--     ext i j
--     cases hj : j.toSum with
--     | inl jₗ =>
--       simp [standardReprSum1, matrixSum1, StandardRepr.toFull_def, hj]
--       if hiXₗ : i.val ∈ Sₗ.X then
--         simp_all [Matrix.toMatrixUnionUnion]
--         generalize_proofs hhi
--         if hji : j = ⟨i.val, hhi⟩ then
--           have hjₗ : jₗ = ⟨i, hiXₗ⟩
--           · simp_all
--           rw [hji, hjₗ, Matrix.one_apply_eq, Matrix.one_apply_eq]
--         else
--           have hjₗ : jₗ ≠ ⟨i, hiXₗ⟩
--           · intro contr
--             apply hji
--             apply SetCoe.ext
--             have hjj : j.val = jₗ.val
--             · have := toSum_toUnion j
--               simp_all
--             simp [hjj, congr_arg Subtype.val contr]
--           rw [Matrix.one_apply_ne hji, Matrix.one_apply_ne hjₗ]
--       else
--         have hiXᵣ : i.val ∈ Sᵣ.X
--         · sorry
--         sorry
--     | inr jᵣ => sorry

-- lemma standardReprSum1_comm {Sₗ Sᵣ : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
--     (valid : (standardReprSum1 hXY hYX).snd) :
--     (standardReprSum1 hXY hYX).fst.toMatroid = (standardReprSum1 hYX.symm hXY.symm).fst.toMatroid := by
--   rw [
--     standardReprSum1_eq_disjointSum valid,
--     standardReprSum1_eq_disjointSum ⟨valid.left.symm, valid.right.symm⟩,
--     Matroid.disjointSum_comm]

lemma standardReprSum1_X {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.X = Sₗ.X ∪ Sᵣ.X := by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm

lemma standardReprSum1_Y {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ Sᵣ.Y := by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm

lemma standardReprSum1_hasTuSigning {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hS : standardReprSum1 hXY hYX = some S) :
    S.B.HasTuSigning := by
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  have hSX : S.X = Sₗ.X ∪ Sᵣ.X := standardReprSum1_X hS
  have hSY : S.Y = Sₗ.Y ∪ Sᵣ.Y := standardReprSum1_Y hS
  have hSB : S.B = (matrixSum1 Sₗ.B Sᵣ.B).toMatrixElemElem hSX hSY
  · simp_rw [standardReprSum1, Option.ite_none_right_eq_some] at hS
    aesop
  use (matrixSum1 Bₗ Bᵣ).toMatrixElemElem hSX hSY
  use (Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ).toMatrixElemElem hSX hSY
  rw [hSB]
  intro i j
  simp only [Matrix.toMatrixElemElem_apply]
  cases (hSX ▸ i).toSum with
  | inl iₗ => cases (hSY ▸ j).toSum with
    | inl jₗ => exact hBBₗ iₗ jₗ
    | inr jᵣ => exact abs_zero
  | inr iᵣ => cases (hSY ▸ j).toSum with
    | inl jₗ => exact abs_zero
    | inr jᵣ => exact hBBᵣ iᵣ jᵣ

lemma Matroid.Is1sumOf.finite_X {M Mₗ Mᵣ : Matroid α} (hM : M.Is1sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hS⟩ := hM
  exact standardReprSum1_X hS ▸ Finite.Set.finite_union ..

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is1sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is1sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finite_X
  obtain ⟨_, _, _, _, _, _, _, rfl, rfl, rfl, hS⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum1_hasTuSigning hMₗ hMᵣ hS

/--
info: 'Matroid.Is1sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is1sumOf.isRegular
-- TODO document in `Seymour.lean` and remove here
