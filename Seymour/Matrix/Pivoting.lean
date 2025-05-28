import Seymour.Basic.Fin
import Seymour.Basic.SignTypeCast
import Seymour.Matrix.TotalUnimodularity
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped Matrix


variable {X Y F : Type}

-- ## Elementary row operations

/-- Multiply column `y` of `A` by factor `q` and keep the rest of `A` unchanged. -/
private def Matrix.mulCol [DecidableEq Y] [Mul F] (A : Matrix X Y F) (y : Y) (q : F) :
    Matrix X Y F :=
  A.updateCol y (q • Aᵀ y)

/-- If column `x` of `A` is multiplied by factor `q` then the determinant is multiplied by factor `q`. -/
private lemma Matrix.mulCol_det [DecidableEq X] [Fintype X] [CommRing F] (A : Matrix X X F) (x : X) (q : F) :
    (A.mulCol x q).det = q * A.det := by
  rw [Matrix.mulCol, Matrix.det_updateCol_smul]
  show q * (A.updateCol x (A · x)).det = q * A.det
  rw [Matrix.updateCol_eq_self]

/-- Multiplying column `y` by a non-zero factor preserves linear (in)dependence. -/
private lemma Matrix.mulCol_linearIndepOn [DecidableEq Y] [Field F] (A : Matrix X Y F) (y : Y) {q : F}
    (hq : q ≠ 0) (S : Set X) :
    LinearIndepOn F (A.mulCol y q) S ↔ LinearIndepOn F A S := by
  rw [Matrix.mulCol, linearIndepOn_iffₛ, linearIndepOn_iffₛ]
  constructor
  all_goals
    intro hFFS
    peel hFFS with f hf g hg hfg
    refine fun hfgl => hfg ?_
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum] at hfgl ⊢
    ext x'
    rw [funext_iff] at hfgl
    specialize hfgl x'
    simp_rw [Finset.sum_apply, Pi.smul_apply, Matrix.updateCol_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
      Finset.sum_ite_irrel] at hfgl ⊢
  · split_ifs with hx'
    · subst hx'
      conv => enter [1, 2, x]; rw [←mul_assoc, mul_comm (f x), mul_assoc]
      conv => enter [2, 2, x]; rw [←mul_assoc, mul_comm (g x), mul_assoc]
      rw [←Finset.mul_sum, ←Finset.mul_sum]
      exact congr_arg (q * ·) hfgl
    · exact hfgl
  · split_ifs at hfgl with hx'
    · subst hx'
      conv at hfgl => enter [1, 2, x]; rw [←mul_assoc, mul_comm (f x), mul_assoc]
      conv at hfgl => enter [2, 2, x]; rw [←mul_assoc, mul_comm (g x), mul_assoc]
      rw [←Finset.mul_sum, ←Finset.mul_sum] at hfgl
      exact mul_left_cancel₀ hq hfgl
    · exact hfgl

/-- Multiply row `x` of `A` by factor `q` and keep the rest of `A` unchanged. -/
private def Matrix.mulRow [DecidableEq X] [Mul F] (A : Matrix X Y F) (x : X) (q : F) :
    Matrix X Y F :=
  A.updateRow x (q • A x)

/-- If row `x` of `A` is multiplied by factor `q` then the determinant is multiplied by factor `q`. -/
private lemma Matrix.mulRow_det [DecidableEq X] [Fintype X] [CommRing F] (A : Matrix X X F) (x : X) (q : F) :
    (A.mulRow x q).det = q * A.det := by
  rw [Matrix.mulRow, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- Multiplying row `x` by a non-zero factor preserves linear (in)dependence on the transpose. -/
private lemma Matrix.mulRow_linearIndepOn [DecidableEq X] [Field F] (A : Matrix X Y F) (x : X) {q : F}
    (hq : q ≠ 0) (S : Set Y) :
    LinearIndepOn F (A.mulRow x q)ᵀ S ↔ LinearIndepOn F Aᵀ S := by
  rw [Matrix.mulRow, ←Matrix.updateCol_transpose]
  let B := Aᵀ
  rw [show Aᵀ = B by rfl, show A = Bᵀ by rfl, ←Matrix.mulCol]
  exact B.mulCol_linearIndepOn x hq S

/-- Multiplying a row by a `0, ±1` factor preserves total unimodularity. -/
private lemma Matrix.IsTotallyUnimodular.mulRow [DecidableEq X] [CommRing F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) {q : F} (hq : q ∈ SignType.cast.range) :
    (A.mulRow x q).IsTotallyUnimodular := by
  intro k f g hf hg
  if hi : ∃ i : Fin k, f i = x then
    obtain ⟨i, rfl⟩ := hi
    convert_to ((A.submatrix f g).updateRow i (q • (A.submatrix id g) (f i))).det ∈ SignType.cast.range
    · congr
      ext i' j'
      if hii : i' = i then
        simp [Matrix.mulRow, hii]
      else
        have hfii : f i' ≠ f i := (hii <| hf ·)
        simp [Matrix.mulRow, hii, hfii]
    rw [Matrix.det_updateRow_smul]
    apply in_signTypeCastRange_mul_in_signTypeCastRange hq
    have hAf := hA.submatrix f id
    convert hAf.det id g
    rw [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
    exact (A.submatrix f g).updateRow_eq_self i
  else
    convert hA k f g hf hg using 2
    simp_all [Matrix.submatrix, Matrix.mulRow]

/-- Add column `y` of `A` multiplied by `q` (where `q` is different for each column) to every column of `A` except `y`. -/
private def Matrix.addColMultiples [DecidableEq Y] [Add F] [SMul F F] (A : Matrix X Y F) (y : Y) (q : Y → F) :
    Matrix X Y F :=
  fun i : X => fun j : Y => if j = y then A i y else A i j + q j • A i y

/-- `Matrix.addColMultiples` preserves linear (in)dependence on the transpose. -/
private lemma Matrix.addColMultiples_linearIndepOn [DecidableEq Y] [Field F] (A : Matrix X Y F) (y : Y) {q : Y → F}
    (S : Set X) :
    LinearIndepOn F (A.addColMultiples y q) S ↔ LinearIndepOn F A S := by
  -- TODO there is a lot of shared code (mainly the setup) between `Matrix.mulCol_linearIndepOn` and here.
  -- Can we have an aux lemma to show it suffices to show `LinearIndepOn .. ↔ LinearIndepOn ..` for this?
  rw [linearIndepOn_iffₛ, linearIndepOn_iffₛ]
  constructor
  all_goals
    intro hFFS
    peel hFFS with f hf g hg hfg
    refine fun hfgl => hfg ?_
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum] at hfgl ⊢
    ext x'
    rw [funext_iff] at hfgl
    have hfgl' := hfgl x'
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.addColMultiples] at hfgl hfgl' ⊢
  · split_ifs with hx'
    · subst hx'; exact hfgl'
    · conv => enter [1, 2, x]; rw [left_distrib, smul_eq_mul, mul_comm (q x'), ←mul_assoc]
      conv => enter [2, 2, x]; rw [left_distrib, smul_eq_mul, mul_comm (q x'), ←mul_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.sum_mul, hfgl', hfgl y]
  · split_ifs at hfgl' with hx'
    · subst hx'; exact hfgl'
    · conv at hfgl' => enter [1, 2, x]; rw [left_distrib, smul_eq_mul, mul_comm (q x'), ←mul_assoc]
      conv at hfgl' => enter [2, 2, x]; rw [left_distrib, smul_eq_mul, mul_comm (q x'), ←mul_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.sum_mul] at hfgl'
      have hfgly := hfgl y
      simp only [↓reduceIte] at hfgly
      rwa [hfgly, add_left_inj] at hfgl'

/-- Add row `x` of `A` multiplied by factor `q` (where `q` is different for each row) to every row of `A` except `x`. -/
private def Matrix.addRowMultiples [DecidableEq X] [Add F] [SMul F F] (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i : X => if i = x then A x else A i + q i • A x

private lemma Matrix.addRowMultiples_tranpose_eq [DecidableEq X] [Add F] [SMul F F] (A : Matrix X Y F) (x : X) (q : X → F) :
    (A.addRowMultiples x q)ᵀ = Aᵀ.addColMultiples x q := by
  ext
  dsimp only [Matrix.addRowMultiples, Matrix.addColMultiples, Matrix.transpose_apply]
  split_ifs <;> rfl

/-- `Matrix.addRowMultiples` preserves linear (in)dependence on the transpose. -/
private lemma Matrix.addRowMultiples_linearIndepOn [DecidableEq X] [Field F] (A : Matrix X Y F) (x : X)
    {q : X → F} (S : Set Y) :
    LinearIndepOn F (A.addRowMultiples x q)ᵀ S ↔ LinearIndepOn F Aᵀ S := by
  rw [Matrix.addRowMultiples_tranpose_eq]
  exact Matrix.addColMultiples_linearIndepOn Aᵀ x S

/-- Adding multiples of a row to all other rows of a matrix does not change the determinant of the matrix. -/
private lemma Matrix.addRowMultiples_det [DecidableEq X] [Fintype X] [CommRing F] (A : Matrix X X F) (x : X) (q : X → F) :
    (A.addRowMultiples x q).det = A.det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i : X => if i = x then 0 else q i) x (if_pos rfl)
  unfold Matrix.addRowMultiples
  aesop

/-- Adding multiples of a row to all other rows of a matrix preserves total unimodularity. -/
private lemma Matrix.IsTotallyUnimodular.addPivotMultiples [DecidableEq X] [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) {x : X} {y : Y} (hAxy : A x y ≠ 0) :
    (A.addRowMultiples x (- A · y / A x y)).IsTotallyUnimodular := by
  intro k f g hf hg
  -- If `x` is in the selected rows, the determinant won't change.
  if hx : ∃ x' : Fin k, f x' = x then
    obtain ⟨x', hx'⟩ := hx
    convert_to ((A.submatrix f g).addRowMultiples x' (fun i : Fin k => (- A (f i) y / A x y))).det ∈ SignType.cast.range using 2
    · ext i j
      if hix' : i = x' then
        simp [Matrix.addRowMultiples, hix', hx']
      else
        have hfi : f i ≠ x := (hix' <| hf <| ·.trans hx'.symm)
        simp [Matrix.addRowMultiples, hix', hx', hfi]
    rw [Matrix.addRowMultiples_det]
    exact hA k f g hf hg
  -- Else if `y` is in the selected columns, its column is all zeros, so the determinant is zero.
  else if hy : ∃ y' : Fin k, g y' = y then
    convert zero_in_signTypeCastRange
    obtain ⟨y', hy'⟩ := hy
    apply Matrix.det_eq_zero_of_column_eq_zero y'
    intro i
    rw [Matrix.submatrix_apply, hy']
    have hi : f i ≠ x := (hx ⟨i, ·⟩)
    simp_all [Matrix.addRowMultiples]
  -- Else perform the expansion on the `y` column, the smaller determinant is equal to ± the bigger determinant.
  else
    let f' : Fin k.succ → X := Fin.cons x f
    let g' : Fin k.succ → Y := Fin.cons y g
    have hf0 : f' 0 = x := rfl
    have hg0 : g' 0 = y := rfl
    have hf' : f'.Injective
    · intro a b hab
      by_cases ha : a = 0
      · by_cases hb : b = 0
        · rw [ha, hb]
        · exfalso
          let b' := b.pred hb
          simp [f', ha] at hab
          have hab' : f b' = x
          · convert hab.symm
            have hb' : b'.succ = b := Fin.succ_pred b hb
            rw [←hb']
            simp
          exact hx ⟨b', hab'⟩
      · by_cases hb : b = 0
        · exfalso
          let a' := a.pred ha
          simp [f', hb] at hab
          have hab' : f a' = x
          · convert hab
            have ha' : a'.succ = a := Fin.succ_pred a ha
            rw [←ha']
            simp
          exact hx ⟨a', hab'⟩
        · let a' := a.pred ha
          let b' := b.pred hb
          have ha' : a'.succ = a := Fin.succ_pred a ha
          have hb' : b'.succ = b := Fin.succ_pred b hb
          rw [←ha', ←hb'] at hab ⊢
          simp [f'] at hab
          rw [hf hab]
    have similar : ((A.addRowMultiples x (- A · y / A x y)).submatrix f' g').det ∈ SignType.cast.range
    · convert_to
        ((A.submatrix f' g').addRowMultiples 0 (fun i : Fin k.succ => (- A (f' i) y / A x y))).det ∈ SignType.cast.range
          using 2
      · ext i j
        if hi0 : i = 0 then
          simp [Matrix.addRowMultiples, hi0, hf0]
        else
          have hfi : f' i ≠ x := (hi0 <| hf' <| ·.trans hf0.symm)
          simp [Matrix.addRowMultiples, hi0, hf0, hfi]
      rw [Matrix.addRowMultiples_det]
      exact hA.det f' g'
    have laplaced : ((A.addRowMultiples x (- A · y / A x y)).submatrix f' g').det =
        (A.addRowMultiples x (- A · y / A x y)) x y * ((A.addRowMultiples x (- A · y / A x y)).submatrix f g).det
    · rw [Matrix.det_succ_column_zero, sum_over_fin_succ_of_only_zeroth_nonzero]
      have my_pow_zero : (-1 : F) ^ (0 : Fin k.succ).val = 1 := pow_eq_one_iff_modEq.← rfl
      rw [my_pow_zero, one_mul]
      have hff : Fin.cons x f ∘ Fin.succ = f := rfl
      have hgg : Fin.cons y g ∘ Fin.succ = g := rfl
      simp [Matrix.submatrix_apply, f', g', hff, hgg]
      · intro i hi
        rw [Matrix.submatrix_apply]
        have hfi : f' i ≠ x := hf0 ▸ (hi <| hf' <| ·)
        simp_all [Matrix.addRowMultiples]
    have eq_Axy : (A.addRowMultiples x (- A · y / A x y)) x y = A x y
    · simp [Matrix.addRowMultiples]
    rw [laplaced, eq_Axy] at similar
    if hAxy1 : A x y = 1 then
      simpa [hAxy1] using similar
    else if hAxy9 : A x y = -1 then
      exact in_signTypeCastRange_of_neg_one_mul (hAxy9 ▸ similar)
    else
      exfalso
      obtain ⟨s, hs⟩ := hA.apply x y
      cases s with
      | zero => exact hAxy hs.symm
      | pos => exact hAxy1 hs.symm
      | neg => exact hAxy9 hs.symm


-- ## Long-tableau pivoting

/-- The result of pivoting in a long tableau. This definition makes sense only if `A x y` is non-zero.
    The recommending spelling when calling the function is `(A.longTableauPivot x y) i j` when pivoting in `A` on `[x,y]` and
    indexing at `[i,j]` even tho the `( )` is redundant. -/
def Matrix.longTableauPivot [One F] [SMul F F] [Div F] [Sub F] [DecidableEq X] (A : Matrix X Y F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of <| fun i : X =>
    if i = x then
      (1 / A x y) • A i
    else
      A i - (A i y / A x y) • A x

/-- Long-tableau pivoting changes the nonzero pivot to one. -/
lemma Matrix.longTableauPivot_elem_pivot_eq_one [DecidableEq X] [DivisionSemiring F] [Sub F] (A : Matrix X Y F) {x : X} {y : Y}
    (hAxy : A x y ≠ 0) :
    (A.longTableauPivot x y) x y = 1 := by
  simp [hAxy, Matrix.longTableauPivot]

/-- Long-tableau pivoting changes all nonpivot elements in the pivot column to zeros. -/
lemma Matrix.longTableauPivot_elem_in_pivot_col_eq_zero [DecidableEq X] [DivisionRing F] (A : Matrix X Y F) {x i : X} {y : Y}
    (hix : i ≠ x) (hAxy : A x y ≠ 0) :
    (A.longTableauPivot x y) i y = 0 := by
  simp [hix, hAxy, Matrix.longTableauPivot]

/-- Long-tableau pivoting preserves zeros of all nonpivot elements in the pivot row. -/
lemma Matrix.longTableauPivot_elem_in_pivot_row_eq_zero [DecidableEq X] [NonAssocSemiring F] [Sub F] [Div F] (A : Matrix X Y F)
    {x : X} {j : Y} (hAxj : A x j = 0) (y : Y) :
    (A.longTableauPivot x y) x j = 0 := by
  simp [hAxj, Matrix.longTableauPivot]

/-- Long-tableau pivoting preserves the original values in the nonpivot row whereëver the pivot row has zeros. -/
lemma Matrix.longTableauPivot_elem_of_zero_in_pivot_row [DecidableEq X] [NonAssocRing F] [Div F] (A : Matrix X Y F)
    {x i : X} {j : Y} (hix : i ≠ x) (hAxj : A x j = 0) (y : Y) :
    (A.longTableauPivot x y) i j = A i j := by
  simp [hix, hAxj, Matrix.longTableauPivot]

/-- Long-tableau pivoting expressed via elementary row operations. -/
private lemma Matrix.longTableauPivot_eq [DecidableEq X] [DivisionRing F] (A : Matrix X Y F) (x : X) (y : Y) :
    A.longTableauPivot x y = (A.addRowMultiples x (- A · y / A x y)).mulRow x (1 / A x y) := by
  ext i j
  if hi : i = x then
    simp [Matrix.longTableauPivot, Matrix.addRowMultiples, Matrix.mulRow, hi]
  else
    simp [Matrix.longTableauPivot, Matrix.addRowMultiples, Matrix.mulRow, hi, sub_eq_add_neg, neg_mul, neg_div]

/-- Long-tableau pivoting preserves total unimodularity. -/
lemma Matrix.IsTotallyUnimodular.longTableauPivot [DecidableEq X] [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (y : Y) (hAxy : A x y ≠ 0) :
    (A.longTableauPivot x y).IsTotallyUnimodular := by
  rw [A.longTableauPivot_eq x y]
  have h1Axy : 1 / A x y ∈ SignType.cast.range
  · rw [inv_eq_self_of_in_signTypeCastRange] <;> exact hA.apply x y
  exact (hA.addPivotMultiples hAxy).mulRow x h1Axy

/-- Long-tableau pivoting preserves linear independence on transpose. -/
lemma Matrix.longTableauPivot_linearIndepenOn [DecidableEq X] [Field F] (A : Matrix X Y F) {x : X} {y : Y}
    (hAxy : A x y ≠ 0) (S : Set Y) :
    LinearIndepOn F (A.longTableauPivot x y)ᵀ S ↔ LinearIndepOn F Aᵀ S := by
  rw [A.longTableauPivot_eq, Matrix.mulRow_linearIndepOn _ _ (one_div_ne_zero hAxy), A.addRowMultiples_linearIndepOn]

-- ## Short-tableau pivoting

/-- The result of pivoting in a short tableau. This definition makes sense only if `A x y` is non-zero.
    The recommending spelling when calling the function is `(A.shortTableauPivot x y) i j` when pivoting in `A` on `[x,y]` and
    indexing at `[i,j]` even tho the `( )` is redundant. -/
def Matrix.shortTableauPivot [One F] [SMul F F] [Div F] [Zero F] [Sub F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) :
    Matrix X Y F :=
  ((1 ◫ A).longTableauPivot x ◪y).submatrix id (fun j : Y => if j = y then ◩x else ◪j)

/-- Explicit formula for the short-tableau pivoting. -/
@[simp]
lemma Matrix.shortTableauPivot_eq [DivisionRing F] [DecidableEq X] [DecidableEq Y] (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y =
    Matrix.of (fun i : X => fun j : Y =>
      if i = x then
        if j = y then
          1 / A x y
        else
          (1 / A x y) * A x j
      else
        if j = y then
          - A i y / A x y
        else
          A i j - A i y / A x y * A x j
    ) := by
  ext i j
  by_cases hi : i = x <;> by_cases hj : j = y
  <;> simp [hi, hj, Matrix.shortTableauPivot, Matrix.longTableauPivot, mul_one, neg_div']

/-- Short-tableau pivoting preserves total unimodularity. -/
lemma Matrix.IsTotallyUnimodular.shortTableauPivot [DecidableEq X] [DecidableEq Y] [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) {x : X} {y : Y} (hAxy : A x y ≠ 0) :
    (A.shortTableauPivot x y).IsTotallyUnimodular :=
  ((hA.one_fromCols).longTableauPivot x ◪y hAxy).submatrix id (fun j : Y => if j = y then ◩x else ◪j)

lemma Matrix.shortTableauPivot_zero {X' Y' : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DivisionRing F]
    (A : Matrix X Y F) (x : X') (y : Y) (f : X' → X) (g : Y' → Y) (hg : y ∉ g.range) (hAfg : ∀ i j, A (f i) (g j) = 0) :
    ∀ i : X', ∀ j : Y', (A.shortTableauPivot (f x) y) (f i) (g j) = 0 := by
  unfold Matrix.shortTableauPivot Matrix.longTableauPivot
  aesop

lemma Matrix.shortTableauPivot_submatrix_zero_external_row [DivisionRing F] [DecidableEq X] [DecidableEq Y] (A : Matrix X Y F)
    (x : X) (y : Y) {X' Y' : Type} (f : X' → X) (g : Y' → Y) (hf : x ∉ f.range) (hg : y ∉ g.range) (hAg : ∀ j, A x (g j) = 0) :
    (A.shortTableauPivot x y).submatrix f g = A.submatrix f g := by
  unfold Matrix.shortTableauPivot Matrix.longTableauPivot
  aesop

lemma Matrix.submatrix_shortTableauPivot [DecidableEq X] [DecidableEq Y] {X' Y' : Type} [DecidableEq X'] [DecidableEq Y']
    [DivisionRing F] {f : X' → X} {g : Y' → Y}
    (A : Matrix X Y F) (hf : f.Injective) (hg : g.Injective) (x : X') (y : Y') :
    (A.submatrix f g).shortTableauPivot x y = (A.shortTableauPivot (f x) (g y)).submatrix f g := by
  ext i j
  have hfix : f i = f x → i = x := (hf ·)
  have hgjy : g j = g y → j = y := (hg ·)
  unfold Matrix.shortTableauPivot Matrix.longTableauPivot
  aesop


-- ## Lemma 1 of Proof of Regularity of 2-Sum and 3-Sum of Matroids

private lemma Matrix.shortTableauPivot_submatrix_succAbove_pivot_apply [Field F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F)
    {x y : Fin k.succ} (i j : Fin k) :
    (A.shortTableauPivot x y).submatrix x.succAbove y.succAbove i j =
    A (x.succAbove i) (y.succAbove j) - A (x.succAbove i) y * A x (y.succAbove j) / A x y := by
  simp [Matrix.shortTableauPivot, Matrix.longTableauPivot, y.succAbove_ne j, x.succAbove_ne i, div_mul_eq_mul_div]

private lemma Matrix.shortTableauPivot_submatrix_eq [Field F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F)
    {x y : Fin k.succ} :
    (A.shortTableauPivot x y).submatrix x.succAbove y.succAbove =
    Matrix.of (fun i j : Fin k => A (x.succAbove i) (y.succAbove j) - A (x.succAbove i) y * A x (y.succAbove j) / A x y) := by
  ext i j
  exact A.shortTableauPivot_submatrix_succAbove_pivot_apply i j

private abbrev Fin.reindexFun {n : ℕ} (i : Fin n.succ) : Fin 1 ⊕ Fin n → Fin n.succ :=
  (·.casesOn i i.succAbove)

private lemma Fin.reindexFun_bijective {n : ℕ} (i : Fin n.succ) : i.reindexFun.Bijective :=
  ⟨fun a b hab => by
    cases a with
    | inl a₁ =>
      cases b with
      | inl b₁ =>
        congr
        apply fin1_eq_fin1
      | inr bₙ =>
        symm at hab
        absurd i.succAbove_ne bₙ
        simpa using hab
    | inr aₙ =>
      cases b with
      | inl b₁ =>
        absurd i.succAbove_ne aₙ
        simpa using hab
      | inr bₙ =>
        simpa using hab,
    (by
      if hic : i = · then
        use ◩0
        simpa using hic
      else
        aesop)⟩

private noncomputable def Fin.reindexing {n : ℕ} (i : Fin n.succ) : Fin 1 ⊕ Fin n ≃ Fin n.succ :=
  Equiv.ofBijective i.reindexFun i.reindexFun_bijective

private lemma reindexing_symm_eq_left {n : ℕ} (i k : Fin n.succ) (j : Fin 1) :
    i.reindexing.symm k = ◩j ↔ i = k := by
  unfold Fin.reindexing
  constructor <;> intro hk
  on_goal 1 =>
    apply_fun i.reindexFun at hk
    rw [Equiv.ofBijective_apply_symm_apply i.reindexFun i.reindexFun_bijective k] at hk
  on_goal 2 =>
    apply_fun i.reindexFun using i.reindexFun_bijective.left
    rw [Equiv.ofBijective_apply_symm_apply i.reindexFun i.reindexFun_bijective k]
  all_goals
    simp [hk]

private lemma reindexing_symm_eq_right {n : ℕ} (i k : Fin n.succ) (j : Fin n) :
    i.reindexing.symm k = ◪j ↔ k = (i.succAbove j) := by
  unfold Fin.reindexing
  constructor <;> intro hkj
  on_goal 1 =>
    apply_fun i.reindexFun at hkj
    rw [Equiv.ofBijective_apply_symm_apply i.reindexFun i.reindexFun_bijective k] at hkj
  on_goal 2 =>
    apply_fun i.reindexFun using i.reindexFun_bijective.1
    rw [Equiv.ofBijective_apply_symm_apply i.reindexFun i.reindexFun_bijective k]
  all_goals
    simp [hkj]

private abbrev Matrix.block₁₁ {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) : Matrix (Fin 1) (Fin 1) F :=
  !![A x y]

private abbrev Matrix.block₁₂ {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) : Matrix (Fin 1) (Fin k) F :=
  Matrix.of (fun _ j => A x (y.succAbove j))

private abbrev Matrix.block₂₁ {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) : Matrix (Fin k) (Fin 1) F :=
  Matrix.of (fun i _ => A (x.succAbove i) y)

private abbrev Matrix.block₂₂ {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) : Matrix (Fin k) (Fin k) F :=
  Matrix.of (fun i j => A (x.succAbove i) (y.succAbove j))

private lemma Matrix.succAboveAt_block [DivisionRing F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) :
    A = (⊞ (A.block₁₁ x y) (A.block₁₂ x y) (A.block₂₁ x y) (A.block₂₂ x y)
      ).submatrix x.reindexing.symm y.reindexing.symm := by
  ext i j
  rw [Matrix.submatrix_apply]
  cases hx : x.reindexing.symm i <;> cases hy : y.reindexing.symm j
  on_goal 1 => rw [Matrix.fromBlocks_apply₁₁]
  on_goal 2 => rw [Matrix.fromBlocks_apply₁₂]
  on_goal 3 => rw [Matrix.fromBlocks_apply₂₁]
  on_goal 4 => rw [Matrix.fromBlocks_apply₂₂]
  all_goals
    try rw [reindexing_symm_eq_left] at hx
    try rw [reindexing_symm_eq_left] at hy
    try rw [reindexing_symm_eq_right] at hx
    try rw [reindexing_symm_eq_right] at hy
    subst hx hy
    simp

private lemma Matrix.shortTableauPivot_submatrix_eq_blockish [Field F] {k : ℕ}
    (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) :
    (A.shortTableauPivot x y).submatrix x.succAbove y.succAbove =
    (A.block₂₂ x y) - (A.block₂₁ x y) * (A.block₁₁ x y)⁻¹ * (A.block₁₂ x y) := by
  rw [Matrix.shortTableauPivot_submatrix_eq]
  conv in _ / _ => rw [div_eq_mul_inv _ (A x y)]
  rw [show (A.block₁₁ x y)⁻¹ = !![(A x y)⁻¹] from Matrix.ext (by simp [·.eq_zero, ·.eq_zero])]
  ext i j
  simp [Matrix.mul_apply, mul_right_comm]

private noncomputable instance invertible_matrix_fin1_of_ne_zero [Field F] {A : Matrix (Fin 1) (Fin 1) F}
    [hA0 : NeZero (A 0 0)] :
    Invertible A :=
  A.invertibleOfLeftInverse A⁻¹ (by
    ext i j
    rw [i.eq_zero, j.eq_zero]
    simp [IsUnit.inv_mul_cancel (IsUnit.mk0 _ hA0.out)])

private lemma shortTableauPivot_submatrix_succAbove_succAbove_det_abs_eq_div [LinearOrderedField F] {k : ℕ}
    {A : Matrix (Fin k.succ) (Fin k.succ) F} {x y : Fin k.succ} (hAxy : A x y ≠ 0) :
    |((A.shortTableauPivot x y).submatrix x.succAbove y.succAbove).det| = |A.det| / |A x y| := by
  have : NeZero (A.block₁₁ x y 0 0) := ⟨by simpa⟩
  rw [
    Matrix.shortTableauPivot_submatrix_eq_blockish, eq_div_iff_mul_eq (abs_ne_zero.← hAxy), mul_comm,
    ←show (A.block₁₁ x y).det = A x y from Matrix.det_fin_one_of _,
    ←abs_mul, ←(A.block₁₁ x y).invOf_eq_nonsing_inv, ←Matrix.det_fromBlocks₁₁]
  nth_rw 5 [A.succAboveAt_block x y]
  exact (Matrix.abs_det_submatrix_equiv_equiv ..).symm

/-- Lemma 1. -/
lemma shortTableauPivot_submatrix_det_abs_eq_div [LinearOrderedField F] {k : ℕ}
    {A : Matrix (Fin k.succ) (Fin k.succ) F} {x y : Fin k.succ} (hAxy : A x y ≠ 0) :
    ∃ f : Fin k → Fin k.succ, ∃ g : Fin k → Fin k.succ, f.Injective ∧ g.Injective ∧
      |((A.shortTableauPivot x y).submatrix f g).det| = |A.det| / |A x y| :=
  ⟨x.succAbove, y.succAbove, Fin.succAbove_right_injective, Fin.succAbove_right_injective,
    shortTableauPivot_submatrix_succAbove_succAbove_det_abs_eq_div hAxy⟩

/-- Corollary 1. -/
lemma shortTableauPivot_submatrix_det_ni_signTypeCastRange [LinearOrderedField F] {k : ℕ}
    {A : Matrix (Fin k.succ) (Fin k.succ) F}
    (hA : A.det ∉ SignType.cast.range) (x y : Fin k.succ) (hAxy : A x y = 1 ∨ A x y = -1) :
    ∃ f : Fin k → Fin k.succ, ∃ g : Fin k → Fin k.succ, f.Injective ∧ g.Injective ∧
      ((A.shortTableauPivot x y).submatrix f g).det ∉ SignType.cast.range := by
  have hAxy0 : A x y ≠ 0
  · cases hAxy with
    | inl h1 =>
      rw [h1]
      norm_num
    | inr h9 =>
      rw [h9]
      norm_num
  obtain ⟨f, g, hf, hg, hAfg⟩ := shortTableauPivot_submatrix_det_abs_eq_div hAxy0
  use f, g, hf, hg
  rw [in_signTypeCastRange_iff_abs, hAfg]
  cases hAxy with
  | inl h1 => rwa [h1, abs_one, div_one, ←in_signTypeCastRange_iff_abs]
  | inr h9 => rwa [h9, abs_neg, abs_one, div_one, ←in_signTypeCastRange_iff_abs]
