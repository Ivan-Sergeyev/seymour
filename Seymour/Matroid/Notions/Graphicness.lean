import Seymour.Matroid.Operations.Duality

open Function

/-- Column of a node-edge incidence matrix is either all `0`,
    or has exactly one `+1` entry, exactly one `-1` entry, and all other elements `0`. -/
def IsIncidenceMatrixColumn {m : Type} [DecidableEq m] (v : m → ℚ) : Prop :=
  (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ v x₁ = 1 ∧ v x₂ = -1 ∧ (∀ i : m, i ≠ x₁ → i ≠ x₂ → v i = 0))

-- under additional assumption that `m` is nonempty, `IsIncidenceMatrixColumn v` is equivalent to:
-- `∃ x₁ x₂ : m, v = Function.update (0 : m → ℚ) x₁ 1 + Function.update (0 : m → ℚ) x₂ (-1)`

/-- Matrix is called graphic iff it is a node-edge incidence matrix of a (directed) graph. -/
def Matrix.IsGraphic {m n : Type} [DecidableEq m] (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, IsIncidenceMatrixColumn (A · y)

/-- The column function can be defined as an if statement with membership. We write it in this form
to satisfy Fintype.sum_ite_mem. -/
lemma IsIncidenceMatrixColumn.eq_if_mem {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ v = (fun x ↦ if x ∈ [x₁, x₂].toFinset then (if x = x₁ then 1 else -1) else 0)) := by
  refine Or.imp_right (fun hv ↦ ?_) hv
  peel hv with x₁ x₂ h
  refine ⟨h.1, ?_⟩
  simp only [List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq, Finset.mem_insert,
    Finset.mem_singleton]
  ext x
  by_cases x = x₁
  · simp_all
  by_cases x = x₂
  · simp_all
  simp_all

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

/-- The sum of a column of an incidence matrix is 0. -/
lemma IsIncidenceMatrixColumn.sum_zero {m : Type} [Fintype m] [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    ∑ i : m, v i = 0 := by
  cases IsIncidenceMatrixColumn.eq_if_mem hv with
  | inl h => simp_all
  | inr h =>
    rw [h.choose_spec.choose_spec.2, Finset.sum_ite_mem, Finset.univ_inter,
      List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
      Finset.sum_insert (by simpa using h.choose_spec.choose_spec.1), Finset.sum_singleton]
    simp_rw [ne_eq, ite_true, h.choose_spec.choose_spec.1.symm, ite_false, add_neg_cancel]

/-- Every element of a graphic matrix is 1, 0, or -1 -/
lemma Matrix.IsGraphic.elem_in_signTypeCastRange {m n : Type} [DecidableEq m] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) (x : m) (y : n) :
    A x y ∈ SignType.cast.range :=
  (hA y).elem_in_signTypeCastRange x

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
-- future refactor: it's probably easier to unfold the definition in-place to get this result
lemma IsIncidenceMatrixColumn.zero_or_two_nonzeros {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    (v = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ ∀ i, i ≠ x₁ → i ≠ x₂ → v i = 0) :=
  Or.imp_right (fun ⟨x₁, x₂, hxx, _, _, hvnxx⟩ ↦ ⟨x₁, x₂, hxx, hvnxx⟩) hv

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
lemma Matrix.IsGraphic.col_zero_or_two_nonzeros {m n : Type} [DecidableEq m] {A : Matrix m n ℚ} (hA : A.IsGraphic) (y : n) :
    ((A · y) = 0) ∨ (∃ x₁ x₂ : m, x₁ ≠ x₂ ∧ ∀ i, i ≠ x₁ → i ≠ x₂ → (A · y) i = 0) :=
  (hA y).zero_or_two_nonzeros

/-- The sum of the columns in a graphic matrix is 0 -/
lemma Matrix.IsGraphic.cols_sum_zero {m n : Type} [Fintype n] [Fintype m] [DecidableEq m] {A : Matrix m n ℚ} (hA : A.IsGraphic) :
    ∑ x, A x = 0 := by
  ext x
  rw [Pi.zero_apply, Fintype.sum_apply]
  exact IsIncidenceMatrixColumn.sum_zero <| hA x

/-- A nongraphic submatrix S of a graphic matrix is only nongraphic iff there exists a column in S that only has
one non-zero entry -/
lemma Matrix.IsGraphic.submatrix_one_if_not_graphic {l m o n : Type} [DecidableEq l] [DecidableEq m]
      {A : Matrix m n ℚ} (hA : A.IsGraphic)
      (f : l → m) (g : o → n) (hf : Injective f)
      (h : ¬(A.submatrix f g).IsGraphic) :
    ∃ y x, ((A.submatrix f g x y = 1 ∨ A.submatrix f g x y = -1)) ∧
      (∀ i : l, i ≠ x → (A.submatrix f g) i y = 0) := by
  simp_rw [IsGraphic, IsIncidenceMatrixColumn, submatrix_apply, ne_eq] at h
  push_neg at h
  obtain ⟨y, hy⟩ := h
  use y
  rcases hA (g y) with (h | ⟨x₁, x₂, hxx⟩)
  · absurd hy.1
    rw [funext_iff] at h
    ext x
    simp_all [h (f x)]
  · by_cases hxq : x₁ ∈ Set.range f ∨ x₂ ∈ Set.range f
    · simp_rw [submatrix_apply, ne_eq]
      rcases hxq with (⟨x, hx⟩ | ⟨x, hx⟩)
      all_goals
        use x
        simp_rw [ne_eq] at hxx
        simp_rw [hx]
        refine ⟨by simp_all [hxx.2.1, hxx.2.2.1], fun i hi ↦ ?_⟩
      · refine hxx.2.2.2 (f i) ((Function.Injective.ne_iff' hf hx).mpr hi) ?_
        by_contra!
        subst hx this
        obtain ⟨ei, hyei⟩ := hy.2 x i (by symm; exact hi) hxx.2.1 hxx.2.2.1
        exact absurd (hxx.2.2.2 (f ei) (hf.ne hyei.1) (hf.ne hyei.2.1)) hyei.2.2
      · refine hxx.2.2.2 (f i) ?_ ((Function.Injective.ne_iff' hf hx).mpr hi)
        by_contra!
        subst hx this
        obtain ⟨ei, hyei⟩ := hy.2 i x hi hxx.2.1 hxx.2.2.1
        exact absurd (hxx.2.2.2 (f ei) (hf.ne hyei.1) (hf.ne hyei.2.1)) hyei.2.2
    · rw [not_or] at hxq
      absurd hy.1
      ext i
      have := hxx.2.2.2 (f i) (by simp_all) (by simp_all)
      simp_all
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
      by_cases hAfg : (A.submatrix f g).IsGraphic
      · by_cases hAfg' : ∃ j, (∀ i, (A.submatrix f g) i j = 0)
        · rw [Matrix.det_eq_zero_of_column_eq_zero hAfg'.choose hAfg'.choose_spec]
          exact ⟨SignType.zero, rfl⟩
        · use SignType.zero
          simp only [SignType.zero_eq_zero, SignType.coe_zero]
          symm
          -- we enter contradiction since there is no eq (instead of ne) for linearIndependent_cols_of_det_ne_zero
          by_contra hA0
          have hl := Matrix.linearIndependent_rows_of_det_ne_zero hA0
          rw [Fintype.linearIndependent_iff] at hl
          have hl1 := hl (fun g => 1)
          simp_rw [one_smul, one_ne_zero, forall_const] at hl1
          exact hl1 (Matrix.IsGraphic.cols_sum_zero hAfg)
      · have ⟨y₁, x₁, hnAg⟩ := submatrix_one_if_not_graphic hA f g hf hAfg
        rw [Matrix.det_succ_column (A.submatrix f g) y₁]
        simp_rw [submatrix_apply]
        -- TODO: this `have` is horrifically repetitive and ugly. there a weird hack here
        -- (the extra 0 added to allow the future simp call to not delve into infinite recursion)
        -- i would have liked to use `conv` here
        have : ∀ (x : Fin (k + 1 + 1)),
          (-1 : ℚ) ^ ((x : ℕ) + (y₁ : ℕ)) * A (f x) (g y₁) *
            ((A.submatrix f g).submatrix x.succAbove y₁.succAbove).det =
            if x = x₁ then (-1 : ℚ) ^ ((x : ℕ) + (y₁ : ℕ) + 0) * A (f x) (g y₁) *
            ((A.submatrix f g).submatrix x.succAbove y₁.succAbove).det else 0 := by
          intro x
          simp_all only [Set.mem_range, submatrix_submatrix, add_zero, Even.add_self, Even.neg_pow,
            one_pow, one_mul]
          by_cases h : x = x₁ <;> simp_all
        simp_rw [this, Fintype.sum_ite_eq' x₁]
        repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
        · rw [in_signTypeCastRange_iff_abs, abs_neg_one_pow, range, Set.mem_range]
          use .pos
          simp only [SignType.pos_eq_one, SignType.coe_one]
        · exact Matrix.IsGraphic.elem_in_signTypeCastRange hA (f x₁) (g y₁)
        · simp only [range, submatrix_submatrix]
          refine ih _ _ (hf.comp ?_) (hg.comp ?_)
          all_goals exact Fin.succAbove_right_injective

/-- Graphic matroid is regular. -/
theorem Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  obtain ⟨X, Y, A, hA, hMA⟩ := hM
  exact ⟨X, Y, A, hA.isTotallyUnimodular, hMA⟩

/-- Cographic matroid is regular. -/
theorem Matroid.IsCographic.isRegular {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular := by
  unfold Matroid.IsCographic at hM
  exact hM.isRegular.of_dual
