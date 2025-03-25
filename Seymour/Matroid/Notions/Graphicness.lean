import Seymour.Matroid.Notions.Regularity


/-- Column of a node-edge incidence matrix is either all 0,
    or has exactly one +1 entry, exactly one -1 entry, and all other elements 0. -/
def IsIncidenceMatrixColumn {m : Type} [DecidableEq m] (v : m → ℚ) : Prop :=
  (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ v x₁ = 1 ∧ v x₂ = -1 ∧ (∀ i, i ≠ x₁ → i ≠ x₂ → v i = 0))

-- under additional assumption that m is nonempty, IsIncidenceMatrixColumn v is equivalent to:
-- ∃ x₁ x₂ : m, v = Function.update (0 : m → ℚ) x₁ 1 + Function.update (0 : m → ℚ) x₂ (-1)

/-- Matrix is called graphic iff it is a node-edge incidence matrix of a (directed) graph. -/
def Matrix.IsGraphic {m n : Type} [DecidableEq m] (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, IsIncidenceMatrixColumn (A · y)

/-- Every element of a column of a node-edge incidence matrix is 1, 0, or -1 -/
lemma IsIncidenceMatrixColumn.isSign {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    ∀ i : m, v i ∈ Set.range SignType.cast := by
  intro i
  cases hv with
  | inl hv =>
      use .zero
      simp [hv]
  | inr hv =>
      obtain ⟨x₁, x₂, hx₁x₂, hvx₁, hvx₂, hvnx₁x₂⟩ := hv
      specialize hvnx₁x₂ i
      by_cases hix₁ : i = x₁
      · rw [hix₁, hvx₁]
        use .pos
        rfl
      by_cases hix₂ : i = x₂
      · rw [hix₂, hvx₂]
        use .neg
        rfl
      rw [hvnx₁x₂ hix₁ hix₂]
      use .zero
      rfl

/-- Every element of a graphic matrix is 1, 0, or -1 -/
lemma Matrix.IsGraphic.isSign {m n : Type} [DecidableEq m] {A : Matrix m n ℚ} (hA : A.IsGraphic) (x : m) (y : n) :
    A x y ∈ Set.range SignType.cast :=
  (hA y).isSign x

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
-- future refactor: it's proably easier to unfold the defintion in-place to get this result
lemma IsIncidenceMatrixColumn.zero_or_two_nonzeros {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ ∀ i, i ≠ x₁ → i ≠ x₂ → v i = 0) := by
  cases hv with
  | inl hv =>
      left
      exact hv
  | inr hv =>
      right
      obtain ⟨x₁, x₂, hx₁x₂, -, -, hvnx₁x₂⟩ := hv
      exact ⟨x₁, x₂, hx₁x₂, hvnx₁x₂⟩

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
lemma Matrix.IsGraphic.col_zero_or_two_nonzeros {m n : Type} [DecidableEq m] {A : Matrix m n ℚ} (hA : A.IsGraphic) (y : n) :
    ((A · y) = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ ∀ i, i ≠ x₁ → i ≠ x₂ → (A · y) i = 0) :=
  (hA y).zero_or_two_nonzeros


variable {α : Type} [DecidableEq α]

/-- Matroid is graphic iff it can be represented by a graphic matrix. -/
def Matroid.IsGraphic (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ (VectorMatroid.mk X Y A).toMatroid = M

/-- Matroid is cographic iff its dual is graphic. -/
def Matroid.IsCographic (M : Matroid α) : Prop :=
  M✶.IsGraphic

-- We follow the proof from https://math.stackexchange.com/a/4801275/1184658
/-- Node-edge incidence matrix is totally unimodular. -/
lemma Matrix.IsGraphic.isTotallyUnimodular {X Y : Set α} {A : Matrix X Y ℚ} (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  rw [IsGraphic] at hA
  intro k
  induction k with
  | zero =>
    simp_rw [submatrix_empty, det_fin_zero, Set.mem_range]
    intros
    exact ⟨.pos, by simp⟩
  | succ k h => induction k with
    | zero =>
      simp only [Nat.reduceAdd, det_unique, Fin.default_eq_zero, Fin.isValue, submatrix_apply, Set.mem_range]
      intro f g hf hg
      have := Matrix.IsGraphic.isSign hA (f 0) (g 0)
      rw [Set.mem_range] at this
      exact this
    | succ k h =>
      intro f g hf hg
      rw [Set.mem_range]
      by_cases h₀ : ∃ j, (∀ i, (A.submatrix f g) i j = 0)
      · rw [Matrix.det_eq_zero_of_column_eq_zero h₀.choose h₀.choose_spec]
        use .zero
        simp
      by_cases h₁ : ∃ j k, (∀ i, i ≠ k ↔ (A.submatrix f g) i j = 0)
      · sorry
      by_cases h₂ : ∀ j, ∃ k l, (∀ i, (i ≠ k ∧ i ≠ l) ↔ (A.submatrix f g) i j = 0)
      · use .zero
        simp only [SignType.zero_eq_zero, SignType.coe_zero]
        symm
        by_contra h
        have hl := Matrix.linearIndependent_rows_of_det_ne_zero h
        rw [Fintype.linearIndependent_iff] at hl
        have := hl (fun g ↦ 1)
        simp_rw [one_smul, one_ne_zero, forall_const, imp_false] at this
        absurd this
        sorry -- follows by linearly dependent rows
      push_neg at h₂
      have := Matrix.IsGraphic.col_zero_or_two_nonzeros hA
      sorry -- follows by contradiction

/-- Graphic matroid is regular. -/
theorem Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  obtain ⟨X, Y, A, hA, hMA⟩ := hM
  exact ⟨X, Y, A, hA.isTotallyUnimodular, hMA⟩

/-- Cographic matroid is regular. -/
theorem Matroid.IsCographic.isRegular {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  sorry
