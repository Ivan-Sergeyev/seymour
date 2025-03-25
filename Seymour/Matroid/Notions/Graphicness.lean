import Seymour.Matroid.Notions.Regularity


/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops

variable {α : Type}

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ (VectorMatroid.mk X Y A).toMatroid = M

/-- Matroid is cographic iff its dual is represented by an incidence matrix of a graph. -/
def Matroid.IsCographic (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Any element of a graphic matroid is 1, 0, or -1 -/
theorem Matrix.IsGraphic.isSign {m n : Type} {A : Matrix m n ℚ} (hA : A.IsGraphic) (x : m) (y : n) :
    A x y ∈ Set.range SignType.cast := by
  rw [IsGraphic] at hA
  rw [Set.mem_range]
  by_cases h₁ : x = (hA y).choose
  · rw [h₁, (hA y).choose_spec.choose_spec.1]
    use .pos
    simp
  by_cases h₂ : x = (hA y).choose_spec.choose
  · rw [h₂, (hA y).choose_spec.choose_spec.2.1]
    use .neg
    simp
  rw [(hA y).choose_spec.choose_spec.2.2 x h₁ h₂]
  use .zero
  simp

theorem Matrix.IsGraphic.twoCol_neZero {m n : Type} {A : Matrix m n ℚ} (hA : A.IsGraphic) (y : n) :
    ∃ k l, (∀ i, (i ≠ k ∧ i ≠ l) ↔ A i y = 0) := by
  rw [IsGraphic] at hA
  have := hA y
  refine ⟨(hA y).choose, (hA y).choose_spec.choose, fun i ↦ ⟨?_, ?_⟩⟩ <;> intro h
  · exact (hA y).choose_spec.choose_spec.2.2 i h.1 h.2
  · by_contra hi
    rw [← or_iff_not_and_not] at hi
    cases hi with
    | inl hi =>
      have := (hA y).choose_spec.choose_spec.1
      rw [← hi, h] at this
      contradiction
    | inr hi =>
      have := (hA y).choose_spec.choose_spec.2.1
      rw [← hi, h] at this
      contradiction

-- We follow the proof from https://math.stackexchange.com/a/4801275/1184658
/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matrix.IsGraphic.isTotallyUnimodular_of_represents {X Y : Set α} {A : Matrix X Y ℚ} {M : Matroid α}
    (hA : A.IsGraphic) (hAM : (VectorMatroid.mk X Y A).toMatroid = M) :
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
      have := Matrix.IsGraphic.twoCol_neZero hA
      sorry -- follows by contradiction

/-- Graphic matroid is regular. -/
lemma Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  peel hM with X Y A hM
  exact ⟨hM.left.isTotallyUnimodular_of_represents hM.right, hM.right⟩

/-- Cographic matroid is regular. -/
lemma Matroid.IsCographic.isRegular {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  sorry
