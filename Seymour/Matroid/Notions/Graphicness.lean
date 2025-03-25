import Seymour.Matroid.Notions.Regularity


/-- Column of a node-edge incidence matrix is either all `0`,
    or has exactly one `+1` entry, exactly one `-1` entry, and all other elements `0`. -/
def IsIncidenceMatrixColumn {m : Type} [DecidableEq m] (v : m → ℚ) : Prop :=
  (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ v x₁ = 1 ∧ v x₂ = -1 ∧ (∀ i : m, i ≠ x₁ → i ≠ x₂ → v i = 0))

-- under additional assumption that `m` is nonempty, `IsIncidenceMatrixColumn v` is equivalent to:
-- `∃ x₁ x₂ : m, v = Function.update (0 : m → ℚ) x₁ 1 + Function.update (0 : m → ℚ) x₂ (-1)`

/-- Matrix is called graphic iff it is a node-edge incidence matrix of a (directed) graph. -/
def Matrix.IsGraphic {m n : Type} [DecidableEq m] (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, IsIncidenceMatrixColumn (A · y)

/-- Every element of a column of a node-edge incidence matrix is `1`, `0`, or `-1`. -/
lemma IsIncidenceMatrixColumn.elem_in_signTypeCastRange {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    ∀ i : m, v i ∈ SignType.cast.range := by
  intro i
  cases hv with
  | inl hv =>
    use SignType.zero
    simp [hv]
  | inr hv =>
    obtain ⟨x₁, x₂, hxx, hvx₁, hvx₂, hvnxx⟩ := hv
    by_cases hix₁ : i = x₁
    · rw [hix₁, hvx₁]
      exact ⟨SignType.pos, rfl⟩
    by_cases hix₂ : i = x₂
    · rw [hix₂, hvx₂]
      exact ⟨SignType.neg, rfl⟩
    rw [hvnxx i hix₁ hix₂]
    exact ⟨SignType.zero, rfl⟩

/-- Every element of a graphic matrix is 1, 0, or -1 -/
lemma Matrix.IsGraphic.elem_in_signTypeCastRange {m n : Type} [DecidableEq m] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) (x : m) (y : n) :
    A x y ∈ SignType.cast.range :=
  (hA y).elem_in_signTypeCastRange x

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
    obtain ⟨x₁, x₂, hxx, -, -, hvnxx⟩ := hv
    exact ⟨x₁, x₂, hxx, hvnxx⟩

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
  intro k
  cases k with
  | zero =>
    simp_rw [Matrix.submatrix_empty, Matrix.det_fin_zero, Set.mem_range]
    intros
    exact ⟨SignType.pos, by simp⟩
  | succ k => induction k with
    | zero =>
      simp only [Nat.reduceAdd, Matrix.det_unique, Fin.default_eq_zero, Fin.isValue, Matrix.submatrix_apply, Set.mem_range]
      intro f g _ _
      exact hA.elem_in_signTypeCastRange (f 0) (g 0)
    | succ k ih =>
      intro f g hf hg
      rw [Set.mem_range]
      by_cases hAfg : ∃ j, (∀ i, (A.submatrix f g) i j = 0)
      · rw [Matrix.det_eq_zero_of_column_eq_zero hAfg.choose hAfg.choose_spec]
        exact ⟨SignType.zero, rfl⟩
      by_cases hAfg' : ∃ j k, (∀ i, i ≠ k ↔ (A.submatrix f g) i j = 0)
      · sorry
      by_cases hAfg'' : ∀ j, ∃ k l, (∀ i, (i ≠ k ∧ i ≠ l) ↔ (A.submatrix f g) i j = 0)
      · use SignType.zero
        simp only [SignType.zero_eq_zero, SignType.coe_zero]
        symm
        by_contra hA0
        have hl := Matrix.linearIndependent_rows_of_det_ne_zero hA0
        rw [Fintype.linearIndependent_iff] at hl
        have hl1 := hl (fun g => 1)
        simp_rw [one_smul, one_ne_zero, forall_const, imp_false] at hl1
        absurd hl1
        sorry -- follows by linearly dependent rows
      push_neg at hAfg''
      have := hA.col_zero_or_two_nonzeros
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
