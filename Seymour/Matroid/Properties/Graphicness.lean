import Seymour.Matroid.Operations.Duality


/-- Column of a node-edge incidence matrix is either all `0`,
    or has exactly one `+1` entry, exactly one `-1` entry, and all other elements `0`. -/
def IsIncidenceMatrixColumn {m : Type} [DecidableEq m] (v : m → ℚ) : Prop :=
  (v = 0) ∨ (∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ v i₁ = 1 ∧ v i₂ = -1 ∧ (∀ i : m, i ≠ i₁ → i ≠ i₂ → v i = 0))

-- Under additional assumption that `m` is nonempty, `IsIncidenceMatrixColumn v` is equivalent to:
-- `∃ i₁ i₂ : m, v = Function.update (0 : m → ℚ) i₁ 1 + Function.update (0 : m → ℚ) i₂ (-1)`

/-- Matrix is called graphic iff it is a node-edge incidence matrix of a (directed) graph. -/
def Matrix.IsGraphic {m n : Type} [DecidableEq m] (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, IsIncidenceMatrixColumn (A · y)

/-- The column function can be defined as an if statement with membership.
    We write it in this form to satisfy `Fintype.sum_ite_mem`. -/
lemma IsIncidenceMatrixColumn.eq_if_mem {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    v = 0 ∨ ∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ v = (fun i : m => if i ∈ [i₁, i₂].toFinset then (if i = i₁ then 1 else -1) else 0) := by
  refine Or.imp_right (fun hv => ?_) hv
  peel hv with i₁ i₂ hii
  refine ⟨hii.left, ?_⟩
  simp only [List.toFinset_cons, List.toFinset_nil, LawfulSingleton.insert_emptyc_eq, Finset.mem_insert, Finset.mem_singleton]
  ext i
  by_cases i = i₁
  · simp_all
  by_cases i = i₂
  · simp_all
  simp_all

/-- Every element of a column of a node-edge incidence matrix is `1`, `0`, or `-1`. -/
lemma IsIncidenceMatrixColumn.elem_in_signTypeCastRange {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    ∀ i : m, v i ∈ SignType.cast.range := by
  intro i
  cases hv with
  | inl hv => simp [hv]
  | inr hv =>
    obtain ⟨i₁, i₂, hii, hvi₁, hvi₂, hvnii⟩ := hv
    by_cases hii₁ : i = i₁
    · simp [hii₁, hvi₁]
    by_cases hii₂ : i = i₂
    · simp [hii₂, hvi₂]
    simp [hvnii i hii₁ hii₂]

/-- The sum of a column of an incidence matrix is `0`. -/
lemma IsIncidenceMatrixColumn.sum_zero {m : Type} [Fintype m] [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    ∑ i : m, v i = 0 := by
  cases IsIncidenceMatrixColumn.eq_if_mem hv with
  | inl => simp_all
  | inr hv =>
    rw [hv.choose_spec.choose_spec.right, Finset.sum_ite_mem, Finset.univ_inter,
      List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, LawfulSingleton.insert_emptyc_eq,
      Finset.sum_insert (by simpa using hv.choose_spec.choose_spec.left), Finset.sum_singleton]
    simp_rw [ne_eq, ite_true, hv.choose_spec.choose_spec.left.symm, ite_false, add_neg_cancel]

/-- Every element of a graphic matrix is `1`, `0`, or `-1`. -/
lemma Matrix.IsGraphic.elem_in_signTypeCastRange {m n : Type} [DecidableEq m] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) (i : m) (j : n) :
    A i j ∈ SignType.cast.range :=
  (hA j).elem_in_signTypeCastRange i

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
-- future refactor: it's probably easier to unfold the definition in-place to get this result
lemma IsIncidenceMatrixColumn.zero_or_two_nonzeros {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixColumn v) :
    (v = 0) ∨ (∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ ∀ i, i ≠ i₁ → i ≠ i₂ → v i = 0) :=
  Or.imp_right (fun ⟨i₁, i₂, hii, _, _, hvnii⟩ => ⟨i₁, i₂, hii, hvnii⟩) hv

/-- Column of a node-edge incidence matrix has either zero or two non-zero entries. -/
lemma Matrix.IsGraphic.col_zero_or_two_nonzeros {m n : Type} [DecidableEq m] {A : Matrix m n ℚ} (hA : A.IsGraphic) (y : n) :
    ((A · y) = 0) ∨ (∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ ∀ i : m, i ≠ i₁ → i ≠ i₂ → (A · y) i = 0) :=
  (hA y).zero_or_two_nonzeros

/-- The sum of the columns in a graphic matrix is `0`. -/
lemma Matrix.IsGraphic.cols_sum_zero {m n : Type} [Fintype n] [Fintype m] [DecidableEq m] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) :
    ∑ x, A x = 0 := by
  ext x
  rw [Pi.zero_apply, Fintype.sum_apply]
  exact IsIncidenceMatrixColumn.sum_zero (hA x)

/-- A nongraphic submatrix of a graphic matrix is only nongraphic iff there exists a column in it that only has
one non-zero entry -/
lemma Matrix.IsGraphic.submatrix_one_if_not_graphic {l m o n : Type} [DecidableEq l] [DecidableEq m]
    {A : Matrix m n ℚ} (hA : A.IsGraphic) {f : l → m} {g : o → n} (hf : f.Injective) (hAfg : ¬(A.submatrix f g).IsGraphic) :
    ∃ y : o, ∃ x : l,
      ((A.submatrix f g x y = 1 ∨ A.submatrix f g x y = -1)) ∧ (∀ i : l, i ≠ x → (A.submatrix f g) i y = 0) := by
  simp_rw [Matrix.IsGraphic, IsIncidenceMatrixColumn, Matrix.submatrix_apply, ne_eq] at hAfg
  push_neg at hAfg
  obtain ⟨y, hy⟩ := hAfg
  use y
  rcases hA (g y) with (hAg | ⟨i₁, i₂, hii⟩)
  · absurd hy.left
    rw [funext_iff] at hAg
    ext x
    simp_all [hAg (f x)]
  · by_cases hxq : i₁ ∈ Set.range f ∨ i₂ ∈ Set.range f
    · simp_rw [Matrix.submatrix_apply, ne_eq]
      rcases hxq with (⟨x, hx⟩ | ⟨x, hx⟩)
      all_goals
        use x
        simp_rw [ne_eq] at hii
        simp_rw [hx]
        refine ⟨by simp [hii.right.left, hii.right.right.left], fun i hi => ?_⟩
      · refine hii.right.right.right (f i) ((hf.ne_iff' hx).← hi) ?_
        by_contra! hfi
        subst hx hfi
        obtain ⟨i', hyi'⟩ := hy.right x i (Ne.symm hi) hii.right.left hii.right.right.left
        exact absurd (hii.right.right.right (f i') (hf.ne hyi'.left) (hf.ne hyi'.right.left)) hyi'.right.right
      · refine hii.right.right.right (f i) ?_ ((hf.ne_iff' hx).← hi)
        by_contra! hfi
        subst hx hfi
        obtain ⟨i', hyi'⟩ := hy.right i x hi hii.right.left hii.right.right.left
        exact absurd (hii.right.right.right (f i') (hf.ne hyi'.left) (hf.ne hyi'.right.left)) hyi'.right.right
    · rw [not_or] at hxq
      absurd hy.left
      ext j
      have := hii.right.right.right (f j)
      simp_all

variable {α : Type} [DecidableEq α]

/-- Matroid is graphic iff it can be represented by a graphic matrix. -/
def Matroid.IsGraphic (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ (VectorMatroid.mk X Y A).toMatroid = M

/-- Matroid is cographic iff its dual is graphic. -/
def Matroid.IsCographic (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Node-edge incidence matrix is totally unimodular. -/
lemma Matrix.IsGraphic.isTotallyUnimodular {X Y : Set α} {A : Matrix X Y ℚ} (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  -- We follow the proof from https://math.stackexchange.com/a/4801275/1184658
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro f g hf hg
    by_cases hAfg : (A.submatrix f g).IsGraphic
    · by_cases hAfg' : ∃ j, (∀ i, (A.submatrix f g) i j = 0)
      · simp [Matrix.det_eq_zero_of_column_eq_zero hAfg'.choose hAfg'.choose_spec]
      · use SignType.zero
        simp only [SignType.zero_eq_zero, SignType.coe_zero]
        symm
        -- we enter contradiction since there is no `eq` (instead of `ne`) for `linearIndependent_cols_of_det_ne_zero`
        by_contra hA0
        have hl := Matrix.linearIndependent_rows_of_det_ne_zero hA0
        rw [Fintype.linearIndependent_iff] at hl
        have hl1 := hl ↓1
        simp_rw [one_smul, one_ne_zero, forall_const] at hl1
        exact hl1 (Matrix.IsGraphic.cols_sum_zero hAfg)
    · have ⟨j₁, i₁, hnAg⟩ := hA.submatrix_one_if_not_graphic hf hAfg
      rw [(A.submatrix f g).det_succ_column j₁]
      simp_rw [Matrix.submatrix_apply]
      have hAxj₁ : ∀ (x : Fin (k + 1)),
          (-1 : ℚ) ^ (x.val + j₁.val) * A (f x) (g j₁) * ((A.submatrix f g).submatrix x.succAbove j₁.succAbove).det =
          if x = i₁ then
            (-1 : ℤ) ^ (x.val + j₁.val + 0) * A (f x) (g j₁) * ((A.submatrix f g).submatrix x.succAbove j₁.succAbove).det
          else 0
      · intro i
        by_cases i = i₁ <;> simp_all
      simp_rw [hAxj₁, Fintype.sum_ite_eq' i₁]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      · apply neg_one_pow_in_signTypeCastRange
      · exact Matrix.IsGraphic.elem_in_signTypeCastRange hA (f i₁) (g j₁)
      · rw [Matrix.submatrix_submatrix]
        exact ih _ _ (hf.comp Fin.succAbove_right_injective) (hg.comp Fin.succAbove_right_injective)

/-- Graphic matroid is regular. -/
theorem Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  obtain ⟨X, Y, A, hA, hMA⟩ := hM
  exact ⟨X, Y, A, hA.isTotallyUnimodular, hMA⟩
