import Seymour.Matroid.Regular


-- ## Incidence matrix

/-- Row of a node-edge incidence matrix is either all `0`,
    or has exactly one `+1` entry, exactly one `-1` entry, and all other elements `0`. -/
def IsIncidenceMatrixRow {m : Type} [DecidableEq m] (v : m → ℚ) : Prop :=
  (v = 0) ∨ (∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ v i₁ = 1 ∧ v i₂ = -1 ∧ (∀ i : m, i ≠ i₁ → i ≠ i₂ → v i = 0))

-- Under additional assumption that `m` is nonempty, `IsIncidenceMatrixRow v` is equivalent to:
-- `∃ i₁ i₂ : m, v = Function.update (0 : m → ℚ) i₁ 1 + Function.update (0 : m → ℚ) i₂ (-1)`

/-- The Row function can be defined as an if statement with membership.
    We write it in this form to satisfy `Fintype.sum_ite_mem`. -/
lemma IsIncidenceMatrixRow.eq_if_mem {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixRow v) :
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

/-- Every element of a row of a node-edge incidence matrix is `1`, `0`, or `-1`. -/
lemma IsIncidenceMatrixRow.elem_in_signTypeCastRange {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixRow v) :
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

/-- The sum of a row of an incidence matrix is `0`. -/
lemma IsIncidenceMatrixRow.sum_zero {m : Type} [Fintype m] [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixRow v) :
    ∑ i : m, v i = 0 := by
  cases IsIncidenceMatrixRow.eq_if_mem hv with
  | inl => simp_all
  | inr hv =>
    rw [hv.choose_spec.choose_spec.right, Finset.sum_ite_mem, Finset.univ_inter,
      List.toFinset_cons, List.toFinset_cons, List.toFinset_nil, LawfulSingleton.insert_emptyc_eq,
      Finset.sum_insert (by simpa using hv.choose_spec.choose_spec.left), Finset.sum_singleton]
    simp_rw [ne_eq, ite_true, hv.choose_spec.choose_spec.left.symm, ite_false, add_neg_cancel]

/-- Row of a node-edge incidence matrix has either zero or two non-zero entries. -/
-- future refactor: it's probably easier to unfold the definition in-place to get this result
lemma IsIncidenceMatrixRow.zero_or_two_nonzeros {m : Type} [DecidableEq m] {v : m → ℚ} (hv : IsIncidenceMatrixRow v) :
    (v = 0) ∨ (∃ i₁ i₂ : m, i₁ ≠ i₂ ∧ ∀ i, i ≠ i₁ → i ≠ i₂ → v i = 0) :=
  Or.imp_right (fun ⟨i₁, i₂, hii, _, _, hvnii⟩ => ⟨i₁, i₂, hii, hvnii⟩) hv


-- ## Graphic matrix

/-- Matrix is called graphic iff it is a node-edge incidence matrix of a (directed) graph. -/
def Matrix.IsGraphic {m n : Type} [DecidableEq n] (A : Matrix m n ℚ) : Prop :=
  ∀ x : m, IsIncidenceMatrixRow (A x)

/-- Every element of a graphic matrix is `1`, `0`, or `-1`. -/
lemma Matrix.IsGraphic.elem_in_signTypeCastRange {m n : Type} [DecidableEq n] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) (i : m) (j : n) :
    A i j ∈ SignType.cast.range :=
  (hA i).elem_in_signTypeCastRange j

/-- Row of a graphic matrix has either zero or two non-zero entries. -/
lemma Matrix.IsGraphic.row_zero_or_two_nonzeros {m n : Type} [DecidableEq n] {A : Matrix m n ℚ} (hA : A.IsGraphic) (x : m) :
    ((A x) = 0) ∨ (∃ j₁ j₂ : n, j₁ ≠ j₂ ∧ ∀ j : n, j ≠ j₁ → j ≠ j₂ → A x j = 0) :=
  (hA x).zero_or_two_nonzeros

/-- The sum of the rows in a graphic matrix is `0`. -/
lemma Matrix.IsGraphic.rows_sum_zero {m n : Type} [Fintype n] [Fintype m] [DecidableEq n] {A : Matrix m n ℚ}
    (hA : A.IsGraphic) :
    ∑ y, (A · y) = 0 := by
  ext x
  rw [Pi.zero_apply, Fintype.sum_apply]
  exact IsIncidenceMatrixRow.sum_zero (hA x)

/-- A nongraphic submatrix of a graphic matrix is only nongraphic iff there exists a row in it that only has
one non-zero entry -/
lemma Matrix.IsGraphic.submatrix_one_if_not_graphic {l m o n : Type} [DecidableEq n] [DecidableEq o]
    {A : Matrix m n ℚ} (hA : A.IsGraphic) {f : l → m} {g : o → n} (hg : g.Injective) (hAfg : ¬(A.submatrix f g).IsGraphic) :
    ∃ x : l, ∃ y : o,
      ((A.submatrix f g x y = 1 ∨ A.submatrix f g x y = -1)) ∧ (∀ j : o, j ≠ y → (A.submatrix f g) x j = 0) := by
  simp_rw [Matrix.IsGraphic, IsIncidenceMatrixRow, Matrix.submatrix_apply, ne_eq] at hAfg
  push_neg at hAfg
  obtain ⟨x, hx⟩ := hAfg
  use x
  rcases hA (f x) with (hAg | ⟨j₁, j₂, hjj⟩)
  · absurd hx.left
    rw [funext_iff] at hAg
    ext y
    simp_all [hAg (g y)]
  · by_cases hyq : j₁ ∈ Set.range g ∨ j₂ ∈ Set.range g
    · simp_rw [Matrix.submatrix_apply, ne_eq]
      rcases hyq with (⟨y, hy⟩ | ⟨y, hy⟩)
      all_goals
        use y
        simp_rw [ne_eq] at hjj
        simp_rw [hy]
        refine ⟨by simp [hjj.right.left, hjj.right.right.left], fun j hj => ?_⟩
      · refine hjj.right.right.right (g j) ((hg.ne_iff' hy).← hj) ?_
        by_contra! hgj
        subst hy hgj
        obtain ⟨j', hxj'⟩ := hx.right y j (Ne.symm hj) hjj.right.left hjj.right.right.left
        exact absurd (hjj.right.right.right (g j') (hg.ne hxj'.left) (hg.ne hxj'.right.left)) hxj'.right.right
      · refine hjj.right.right.right (g j) ?_ ((hg.ne_iff' hy).← hj)
        by_contra! hgj
        subst hy hgj
        obtain ⟨j', hxj'⟩ := hx.right j y hj hjj.right.left hjj.right.right.left
        exact absurd (hjj.right.right.right (g j') (hg.ne hxj'.left) (hg.ne hxj'.right.left)) hxj'.right.right
    · rw [not_or] at hyq
      absurd hx.left
      ext j
      have := hjj.right.right.right (g j)
      simp_all

/-- Matroid is graphic iff it can be represented by a graphic matrix. -/
def Matroid.IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ _ : DecidableEq Y, ∃ A : Matrix X Y ℚ, M = A.toMatroid ∧ A.IsGraphic

/-- Matroid is cographic iff its dual is graphic. -/
def Matroid.IsCographic {α : Type} (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Node-edge incidence matrix is totally unimodular. -/
lemma Matrix.IsGraphic.isTotallyUnimodular {α : Type} {X Y : Set α} [DecidableEq Y] {A : Matrix X Y ℚ} (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  -- We follow the proof from https://math.stackexchange.com/a/4801275/1184658
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro f g hf hg
    by_cases hAfg : (A.submatrix f g).IsGraphic
    · by_cases hAfg' : ∃ i, (∀ j, (A.submatrix f g) i j = 0)
      · simp [Matrix.det_eq_zero_of_row_eq_zero hAfg'.choose hAfg'.choose_spec]
      · use SignType.zero
        simp only [SignType.zero_eq_zero, SignType.coe_zero]
        symm
        -- we enter contradiction since there is no `eq` (instead of `ne`) for `linearIndependent_cols_of_det_ne_zero`
        by_contra hA0
        have hl := Matrix.linearIndependent_cols_of_det_ne_zero hA0
        rw [Fintype.linearIndependent_iff] at hl
        have hl1 := hl ↓1
        simp_rw [one_smul, one_ne_zero, forall_const] at hl1
        exact hl1 (Matrix.IsGraphic.rows_sum_zero hAfg)
    · have ⟨i₁, j₁, hnAg⟩ := hA.submatrix_one_if_not_graphic hg hAfg
      rw [(A.submatrix f g).det_succ_row i₁]
      simp_rw [Matrix.submatrix_apply]
      have hAi₁y : ∀ (y : Fin (k + 1)),
          (-1 : ℚ) ^ (i₁.val + y.val) * A (f i₁) (g y) * ((A.submatrix f g).submatrix i₁.succAbove y.succAbove).det =
          if y = j₁ then
            (-1 : ℤ) ^ (i₁.val + y.val) * A (f i₁) (g y) * ((A.submatrix f g).submatrix i₁.succAbove y.succAbove).det
          else 0
      · intro j
        by_cases j = j₁ <;> simp_all
      simp_rw [hAi₁y, Fintype.sum_ite_eq' j₁]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      · apply neg_one_pow_in_signTypeCastRange
      · exact Matrix.IsGraphic.elem_in_signTypeCastRange hA (f i₁) (g j₁)
      · rw [Matrix.submatrix_submatrix]
        exact ih _ _ (hf.comp Fin.succAbove_right_injective) (hg.comp Fin.succAbove_right_injective)

/-- Graphic matroid is regular. -/
theorem Matroid.IsGraphic.isRegular {α : Type} {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  obtain ⟨X, Y, _, A, hMA, hA⟩ := hM
  exact ⟨X, Y, A, hMA, hA.isTotallyUnimodular⟩

/-- Cographic matroid is regular. -/
theorem Matroid.IsCographic.isRegular {α : Type} {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular := by
  unfold Matroid.IsCographic at hM
  exact hM.isRegular.of_dual
