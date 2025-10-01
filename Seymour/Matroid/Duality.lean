import Seymour.Matroid.Regularity

/-!
# Matroid Duality

Here we study the duals of matroids given by their standard representation.
-/

open scoped Matrix

variable {α R : Type*} [DecidableEq α]

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual [DivisionRing R] (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.Bᵀ -- the sign is chosen following Oxley (it does not change the resulting matroid)
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of dual is the original standard representation. -/
lemma StandardRepr.dual_dual [DivisionRing R] (S : StandardRepr α R) : S✶✶ = S := by
  simp [StandardRepr.dual]

lemma StandardRepr.dual_indices_union_eq [DivisionRing R] (S : StandardRepr α R) : S✶.X ∪ S✶.Y = S.X ∪ S.Y :=
  Set.union_comm S.Y S.X

@[simp]
lemma StandardRepr.dual_ground [DivisionRing R] (S : StandardRepr α R) : S✶.toMatroid.E = S.toMatroid.E :=
  S.dual_indices_union_eq

open scoped Matrix Set.Notation

universe um in
lemma HELPER_rank_ge_rank_of_submatrix {n : Type*} {n₀ : Type*} {m m₀ : Type um} [Field R] [Fintype n₀] [Fintype n] (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) : (A.submatrix r c).rank ≤ A.rank := by
  simp only [← Matrix.cRank_toNat_eq_rank]
  apply Cardinal.toNat_le_toNat
  · exact Matrix.cRank_submatrix_le A r c
  · have h1 : A.cRank ≤ ↑(Fintype.card n) := by
      exact Matrix.cRank_le_card_width A
    have h2 : (↑(Fintype.card n) : Cardinal) < Cardinal.aleph0 := Cardinal.nat_lt_aleph0 (Fintype.card n)
    exact lt_of_le_of_lt h1 h2

lemma HELPER_rank_of_StandRepr_is_X [Field R] (S : StandardRepr α R) 
  [Matroid.RankFinite S.toMatroid] [Fintype S.X] [Fintype S.Y] [Fintype ↑(S.X ∪ S.Y)] [Fintype (↑S.X ⊕ ↑S.Y)]
  : S.toFull.rank = Fintype.card S.X := by
  apply ge_antisymm
  · rw [← Matrix.rank_one (n := S.X) (R := R)]
    change Matrix.rank 1 ≤ ((Matrix.reindex (Equiv.refl S.X) S.hXY.equivSumUnion) (1 ◫ S.B)).rank
    rw [Matrix.rank_reindex]
    exact HELPER_rank_ge_rank_of_submatrix (A := 1 ◫ S.B) (r := id) (c := Sum.inl)
  · exact Matrix.rank_le_card_height _

lemma HELPER_separate_card {X Y : Set α} [Fintype X] [Fintype Y] (disjoint: X ⫗ Y) : #↑(X ∪ Y) = #X + #Y := by
  rw [← Set.toFinset_card X, ← Set.toFinset_card Y, ← Set.toFinset_card (X ∪ Y)]
  rw [Set.toFinset_union, Finset.card_union_eq_card_add_card.mpr]
  rw [Set.disjoint_toFinset]
  exact disjoint

theorem StandardRepr.textbook_general 
   [Field R] 
  (S : StandardRepr α R)
  [Fintype S.X] [Fintype S.Y]
    (h_null_basis : LinearIndependent R (S✶.toFull) ∧ 
      Submodule.span R (Set.range (S✶.dual_indices_union_eq ▸ S✶.toFull)) = LinearMap.ker S.toFull.mulVecLin
    )
  [Matroid.RankFinite S.toMatroid]
  (B : Set α)
  : S.toMatroid.IsBase B ↔ S✶.toMatroid.IsBase ((S.X ∪ S.Y) \ B) := by
  sorry

/-
  Now, this is the statement of the theorem we usually see in textbooks.

  There are two proofs we can go for:
  1. Textbook "Matroid Theory" (Oxley)
     Section "2.2 Duals of representable matroids", Theorem 2.2.8.
  2. Textbook "Matroids: A Geometric Introduction" (Gordon & McNulty)
     Section "6.1.3 Duality and the Rank–Nullity Theorem", Lemma 6.8 AND Exercise 10 [that asks us to prove Theorem 6.6].

  The proof in the Gordon & McNulty textbook is much more wordy, but seems easier to formalise in Lean.

  `StandardRepr.textbook` below corresponds to the proof of Theorem 6.6.
  `StandardRepr.textbook_general` corresponds to the proof of Theorem 6.8.
  `StandardRepr.textbook_general` is more general than what we need, and we use it to prove `StandardRepr.textbook`.
-/
theorem StandardRepr.textbook [Field R] (S : StandardRepr α R) 
  [Matroid.RankFinite S.toMatroid] (B : Set α) [Fintype S.X] [Fintype S.Y] [ Fintype (↑S.X ⊕ ↑S.Y)]:
  S.toMatroid.IsBase B ↔ S✶.toMatroid.IsBase ((S.X ∪ S.Y) \ B) := by
  -- Can be prettified later
  have : Fintype ↑(S✶.X ∪ S✶.Y) := by rw [StandardRepr.dual_indices_union_eq]; infer_instance
  have : Fintype ↑(S✶✶.X ∪ S✶✶.Y) := by simp [StandardRepr.dual]; infer_instance
  have : Fintype S✶.X := by simp [StandardRepr.dual]; infer_instance
  have : Fintype S✶.Y := by simp [StandardRepr.dual]; infer_instance
  let ourMatrix := S.toFull.mulVecLin

  -- Step 1: apply StandardRepr.textbook_general
  apply StandardRepr.textbook_general

  -- Step 2: find rank of S✶ is S.Y, and rows of S✶ are linearly independent (we will need this for both subgoals of step 3)
  have rank_of_dual_is_Y : S✶.toFull.rank = #S.Y := by
    have dual_X_eq_Y : S✶.X = S.Y := by simp [StandardRepr.dual]
    have rank_eq_card_dual_X : S✶.toFull.rank = #S✶.X := by
      apply ge_antisymm
      · rw [← Matrix.rank_one (n := S✶.X) (R := R)]
        change Matrix.rank (1 : Matrix S✶.X S✶.X R) ≤ ((Matrix.reindex (Equiv.refl S✶.X) S✶.hXY.equivSumUnion) (1 ◫ S✶.B)).rank
        rw [Matrix.rank_reindex]
        exact HELPER_rank_ge_rank_of_submatrix (A := 1 ◫ S✶.B) (r := id) (c := Sum.inl)
      · exact Matrix.rank_le_card_height _
    simp [dual_X_eq_Y, rank_eq_card_dual_X]
  have rows_of_dual_are_linearly_independent : LinearIndependent (ι := ↑S✶.X) R S✶.toFull := by
    refine (linearIndependent_iff_card_eq_finrank_span (K := R) (b := S✶.toFull)).2 ?_
    have h_span : Module.finrank R (Submodule.span R (Set.range (S✶.toFull))) = S✶.toFull.rank := Eq.symm (Matrix.rank_eq_finrank_span_row S✶.toFull)
    have h_rows : S✶.toFull.rank = Fintype.card S✶.X := by
      have hXeqY : Fintype.card S✶.X = Fintype.card S.Y := Fintype.card_congr' rfl
      simpa [hXeqY]
    exact (h_span.trans h_rows).symm

  -- Step 3: Show that the rows of S✶ form a basis of nullspace of S
  constructor
  · -- Linear independence of S✶.toFull
    exact rows_of_dual_are_linearly_independent
  · -- Span of S✶'s rows = nullspace of S
    -- Step 4: Show that the rank of S's nullspace is #S.Y
    have dimension_of_nullspace_is_Y : Module.finrank R (LinearMap.ker ourMatrix) = #S.Y := by
      -- 1. Find matrix rank
      have range_dim : Module.finrank R (LinearMap.range ourMatrix) = #S.X := HELPER_rank_of_StandRepr_is_X S
      -- 2. Find width
      have domain_dim : Module.finrank R (↑(S.X ∪ S.Y) → R) = #↑(S.X ∪ S.Y) := Module.finrank_fintype_fun_eq_card R
      -- 3. Apply rank-nullity: range_dim + ker_dim = domain_dim
      have rank_nullity_theorem := LinearMap.finrank_range_add_finrank_ker ourMatrix
      rw [domain_dim, range_dim] at rank_nullity_theorem
      -- 4. Just do some algebra
      linarith [HELPER_separate_card S.hXY]

    -- Step 5: Show that each row of S✶ is in nullspace of S [not finished]

    -- Step 6: Since #S.Y rows of the dual are linearly independent (`rows_of_dual_are_linearly_independent`) + they live in a nullspace of S (`step 5`) + that nullspace has rank #S.Y (`dimension_of_nullspace_is_Y`), they span this space
    sorry

/-
  This is the ground work leading to the theorem present in textbooks.
  No matter what proof we go for (Oxley or Gordon), we need this preparatory work.
  Should be refactored.
-/
lemma StandardRepr.toMatroid_dual_eq [Field R] (S : StandardRepr α R) [Matroid.RankFinite S.toMatroid] :
    S.toMatroid✶ = S✶.toMatroid := by
  apply Matroid.ext_isBase
  · ext I
    rw [Matroid.dual_ground, StandardRepr.dual_ground]
  intros B B_is_in_ground
  have equiv := Set.diff_diff_cancel_left B_is_in_ground
  -- These can be filled in later
  have finite_1 : Fintype ↑S.X := by sorry
  have finite_2 : Fintype ↑S.Y := by sorry
  constructor

  intro isBase
  rw [← equiv]

  apply (StandardRepr.textbook S ((S.X ∪ S.Y) \ B)).mp
  apply Matroid.IsBase.compl_isBase_of_dual
  exact isBase

  intro isBase
  rw [← equiv] at isBase ⊢
  apply Matroid.IsBase.compl_isBase_dual
  apply (StandardRepr.textbook S ((S.X ∪ S.Y) \ B)).mpr
  exact isBase

lemma StandardRepr.is_TU_iff [DecidableEq α] (S : StandardRepr α ℚ) :
    S.toFull.IsTotallyUnimodular ↔ S.B.IsTotallyUnimodular := by
  constructor
  · intro h_toFull_TU
    have h_block_TU : ((1 : Matrix S.X S.X ℚ) ◫ S.B).IsTotallyUnimodular := by
      let h_equiv_symm := S.hXY.equivSumUnion.symm
      exact (Matrix.reindex_isTotallyUnimodular (1 ◫ S.B) (Equiv.refl ↑S.X) h_equiv_symm.symm).→ h_toFull_TU
    exact (Matrix.one_fromCols_isTotallyUnimodular_iff S.B).→ h_block_TU
  · intro h_B_TU
    have h_block_TU : ((1 : Matrix S.X S.X ℚ) ◫ S.B).IsTotallyUnimodular := by
      rw [Matrix.one_fromCols_isTotallyUnimodular_iff]
      exact h_B_TU
    exact Matrix.IsTotallyUnimodular.submatrix _ _ h_block_TU

lemma Matroid.IsRegular.dual {M : Matroid α} [Matroid.RankFinite M] (hM : M.IsRegular)  :
    M✶.IsRegular := by
  obtain ⟨X, Y, A, A_TU, eq_1⟩ := hM
  have exists_TU : ∃ S : StandardRepr α ℚ, S.toMatroid = A.toMatroid ∧ S.B.IsTotallyUnimodular := by
    let ⟨G, G_base⟩ := M.exists_isBase
    have hAG_base : A.toMatroid.IsBase G := by simp only [eq_1, G_base]
    have finite : Fintype G := (IsBase.finite G_base).fintype
    have ⟨S, a, b, c⟩ := A.exists_standardRepr_isBase_isTotallyUnimodular hAG_base A_TU
    exact ⟨S, b, c⟩
  obtain ⟨S, eq_2, S_TU⟩ := exists_TU 
  have finite : S.toMatroid.RankFinite := by rwa [eq_2, eq_1]
  have : Fintype S.X := sorry
  have : Fintype S.Y := sorry
  rw [← eq_1, ← eq_2, StandardRepr.toMatroid_dual_eq S]
  use S✶.X, S✶.X ∪ S✶.Y, S✶.toFull
  refine ⟨?_, by rfl⟩
  rw [StandardRepr.is_TU_iff]
  apply Matrix.IsTotallyUnimodular.neg
  exact Matrix.IsTotallyUnimodular.transpose S_TU
