import Seymour.Basic.Fin
import Seymour.Basic.SignTypeCast
import Seymour.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Permutation


variable {X Y F : Type}

-- ## Definition and basic API

/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot).
    This definition makes sense only if `A x y` is nonzero. -/
def Matrix.shortTableauPivot [One F] [Mul F] [Div F] [Sub F] [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of <| fun i j =>
    if j = y then
      if i = x then
        1 / A x y
      else
        - A i y / A x y
    else
      if i = x then
        A x j / A x y
      else
        A i j - A i y * A x j / A x y

lemma Matrix.shortTableauPivot_elem_of_eq_eq [One F] [Mul F] [Div F] [Sub F] [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) {x : X} {y : Y} {i : X} {j : Y} (hix : i = x) (hjx : j = y) :
    A.shortTableauPivot x y i j = 1 / A x y := by
  simp [Matrix.shortTableauPivot, hix, hjx]

lemma Matrix.shortTableauPivot_elem_of_ne_ne [One F] [Mul F] [Div F] [Sub F] [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) {x : X} {y : Y} {i : X} {j : Y} (hix : i ≠ x) (hjx : j ≠ y) :
    A.shortTableauPivot x y i j = A i j - A i y * A x j / A x y := by
  simp [Matrix.shortTableauPivot, hix, hjx]

lemma Matrix.shortTableauPivot_row_pivot [One F] [Mul F] [Div F] [Sub F] [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y x =
    (fun j : Y => if j = y then 1 / A x y else A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot]

lemma Matrix.shortTableauPivot_row_other [One F] [Mul F] [Div F] [Sub F] [Neg F] [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (i : X) (hix : i ≠ x) :
    A.shortTableauPivot x y i =
    (fun j : Y => if j = y then - A i y / A x y else A i j - A i y * A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot, hix]

-- ## Short-tableau pivoting preserves total unimodularity

/-- Multiply the `x`th row of `A` by `c` and keep the rest of `A` unchanged. -/
private def Matrix.mulRow [DecidableEq X] [Mul F] (A : Matrix X Y F) (x : X) (c : F) :
    Matrix X Y F :=
  A.updateRow x (c • A x)

private lemma Matrix.mulRow_det [DecidableEq X] [Fintype X] [CommRing F] (A : Matrix X X F) (x : X) (c : F) :
    (A.mulRow x c).det = c * A.det := by
  rw [Matrix.mulRow, det_updateRow_smul, updateRow_eq_self]

private lemma Matrix.IsTotallyUnimodular.mulRow [DecidableEq X] [CommRing F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) {c : F} (hc : c ∈ SignType.cast.range) :
    (A.mulRow x c).IsTotallyUnimodular := by
  intro k f g hf hg
  if hi : ∃ i : Fin k, f i = x then
    obtain ⟨i, rfl⟩ := hi
    convert_to ((A.submatrix f g).updateRow i (c • (A.submatrix id g) (f i))).det ∈ SignType.cast.range
    · congr
      ext i' j'
      if hii : i' = i then
        simp [Matrix.mulRow, hii]
      else
        have hfii : f i' ≠ f i := (hii <| hf ·)
        simp [Matrix.mulRow, hii, hfii]
    rw [Matrix.det_updateRow_smul]
    apply in_signTypeCastRange_mul_in_signTypeCastRange hc
    have hAf := hA.submatrix f id
    rw [Matrix.isTotallyUnimodular_iff] at hAf
    convert hAf k id g
    rw [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
    exact (A.submatrix f g).updateRow_eq_self i
  else
    convert hA k f g hf hg using 2
    simp_all [Matrix.submatrix, Matrix.mulRow]

/-- Add `q` times the `x`th row of `A` to all rows of `A` except the `x`th row (where `q` is different for each row). -/
private def Matrix.addMultiples [DecidableEq X] [NonUnitalNonAssocSemiring F] (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i : X => if i = x then A x else A i + q i • A x

private lemma Matrix.addMultiples_det [DecidableEq X] [Fintype X] [CommRing F] (A : Matrix X X F) (x : X) (q : X → F) :
    (A.addMultiples x q).det = A.det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i : X => if i = x then 0 else q i) x (by simp)
  unfold Matrix.addMultiples
  aesop

private lemma Matrix.IsTotallyUnimodular.addMultiples [DecidableEq X] [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (y : Y) (hxy : A x y ≠ 0) :
    (A.addMultiples x (- A · y / A x y)).IsTotallyUnimodular := by
  intro k f g hf hg
  -- If `x` is in the selected rows, the determinant won't change.
  if hx : ∃ x' : Fin k, f x' = x then
    obtain ⟨x', hx'⟩ := hx
    convert_to ((A.submatrix f g).addMultiples x' (fun i : Fin k => (- A (f i) y / A x y))).det ∈ SignType.cast.range using 2
    · ext i j
      if hix' : i = x' then
        simp [Matrix.addMultiples, hix', hx']
      else
        have hfi : f i ≠ x := (hix' <| hf <| ·.trans hx'.symm)
        simp [Matrix.addMultiples, hix', hx', hfi]
    rw [Matrix.addMultiples_det]
    exact hA k f g hf hg
  -- Else if `y` is in the selected columns, its column is all zeros, so the determinant is zero.
  else if hy : ∃ y' : Fin k, g y' = y then
    convert zero_in_signTypeCastRange
    obtain ⟨y', hy'⟩ := hy
    apply Matrix.det_eq_zero_of_column_eq_zero y'
    intro i
    rw [Matrix.submatrix_apply, hy']
    have hi : f i ≠ x := (hx ⟨i, ·⟩)
    simp_all [Matrix.addMultiples]
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
    have similar : ((A.addMultiples x (- A · y / A x y)).submatrix f' g').det ∈ SignType.cast.range
    · convert_to
        ((A.submatrix f' g').addMultiples 0 (fun i : Fin k.succ => (- A (f' i) y / A x y))).det ∈ SignType.cast.range
          using 2
      · ext i j
        if hi0 : i = 0 then
          simp [Matrix.addMultiples, hi0, hf0]
        else
          have hfi : f' i ≠ x := (hi0 <| hf' <| ·.trans hf0.symm)
          simp [Matrix.addMultiples, hi0, hf0, hfi]
      rw [Matrix.addMultiples_det]
      rw [Matrix.isTotallyUnimodular_iff] at hA
      exact hA k.succ f' g'
    have laplaced : ((A.addMultiples x (- A · y / A x y)).submatrix f' g').det =
        (A.addMultiples x (- A · y / A x y)) x y * ((A.addMultiples x (- A · y / A x y)).submatrix f g).det
    · rw [Matrix.det_succ_column_zero, sum_over_fin_succ_of_only_zeroth_nonzero]
      have my_pow_zero : (-1 : F) ^ (0 : Fin k.succ).val = 1 := pow_eq_one_iff_modEq.← rfl
      rw [my_pow_zero, one_mul]
      have hff : Fin.cons x f ∘ Fin.succ = f := rfl
      have hgg : Fin.cons y g ∘ Fin.succ = g := rfl
      simp [Matrix.submatrix_apply, f', g', hff, hgg]
      · intro i hi
        rw [Matrix.submatrix_apply]
        have hfi : f' i ≠ x := hf0 ▸ (hi <| hf' <| ·)
        simp_all [Matrix.addMultiples]
    have eq_Axy : (A.addMultiples x (- A · y / A x y)) x y = A x y
    · simp [Matrix.addMultiples]
    rw [laplaced, eq_Axy] at similar
    if hAxy : A x y = 1 then
      simpa [hAxy] using similar
    else if hAyx : A x y = -1 then
      exact in_signTypeCastRange_of_neg_one_mul (hAyx ▸ similar)
    else
      exfalso
      obtain ⟨s, hs⟩ := hA.apply x y
      cases s with
      | zero => exact hxy hs.symm
      | pos => exact hAxy hs.symm
      | neg => exact hAyx hs.symm

/-- The small tableau consists of all columns but `x`th from the original matrix and the `y`th column of the square matrix. -/
private def Matrix.getShortTableau [DecidableEq Y] (A : Matrix X (X ⊕ Y) F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of (fun i : X => fun j : Y => if j = y then A i ◩x else A i ◪j)

private lemma Matrix.IsTotallyUnimodular.getShortTableau [DecidableEq Y] [CommRing F]
    {A : Matrix X (X ⊕ Y) F} (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.getShortTableau x y).IsTotallyUnimodular := by
  convert
    hA.submatrix id (fun j : Y => if j = y then ◩x else ◪j)
  unfold Matrix.getShortTableau
  aesop

private lemma Matrix.shortTableauPivot_eq [DecidableEq X] [DecidableEq Y] [Field F] (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y =
    ((A.prependId.addMultiples x (- A · y / A x y)).getShortTableau x y).mulRow x (1 / A x y) := by
  ext i j
  if hj : j = y then
    by_cases hi : i = x <;>
      simp [Matrix.shortTableauPivot, Matrix.addMultiples, Matrix.getShortTableau, Matrix.mulRow, hj, hi]
  else
    if hi : i = x then
      simp [Matrix.shortTableauPivot, Matrix.addMultiples, Matrix.getShortTableau, Matrix.mulRow, hj, hi]
      exact div_eq_inv_mul (A x j) (A x y)
    else
      simp [Matrix.shortTableauPivot, Matrix.addMultiples, Matrix.getShortTableau, Matrix.mulRow, hj, hi]
      ring

/-- Pivoting preserves total unimodularity. -/
lemma Matrix.IsTotallyUnimodular.shortTableauPivot [DecidableEq X] [DecidableEq Y] [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) {x : X} {y : Y} (hxy : A x y ≠ 0) :
    (A.shortTableauPivot x y).IsTotallyUnimodular := by
  rw [Matrix.shortTableauPivot_eq]
  have hAxy : 1 / A x y ∈ SignType.cast.range
  · rw [inv_eq_self_of_in_signTypeCastRange] <;> exact hA.apply x y
  exact (((hA.one_fromCols).addMultiples x ◪y hxy).getShortTableau x y).mulRow x hAxy

-- ## Specialized API

lemma Matrix.shortTableauPivot_zero {X' Y' : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq X'] [DivisionRing F]
    (A : Matrix X Y F) (x : X') (y : Y) (f : X' → X) (g : Y' → Y) (hg : y ∉ g.range) (hAfg : ∀ i j, A (f i) (g j) = 0) :
    ∀ i : X', ∀ j : Y', (A.shortTableauPivot (f x) y) (f i) (g j) = 0 := by
  unfold Matrix.shortTableauPivot
  aesop

lemma Matrix.shortTableauPivot_submatrix_zero_external_row [DivisionRing F] [DecidableEq X] [DecidableEq Y] (A : Matrix X Y F)
    (x : X) (y : Y) {X' Y' : Type} (f : X' → X) (g : Y' → Y) (hf : x ∉ f.range) (hg : y ∉ g.range) (hAg : ∀ j, A x (g j) = 0) :
    (A.shortTableauPivot x y).submatrix f g = A.submatrix f g := by
  unfold shortTableauPivot
  aesop

lemma Matrix.submatrix_shortTableauPivot [DecidableEq X] [DecidableEq Y] {X' Y' : Type} [DecidableEq X'] [DecidableEq Y']
    [DivisionRing F] {f : X' → X} {g : Y' → Y}
    (A : Matrix X Y F) (hf : f.Injective) (hg : g.Injective) (x : X') (y : Y') :
    (A.submatrix f g).shortTableauPivot x y = (A.shortTableauPivot (f x) (g y)).submatrix f g := by
  ext i j
  have hfix : f i = f x → i = x := (hf ·)
  have hgjy : g j = g y → j = y := (hg ·)
  unfold Matrix.shortTableauPivot
  aesop

lemma Matrix.shortTableauPivot_submatrix_succAbove_pivot_apply [DivisionRing F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F)
    {x y : Fin k.succ} (i j : Fin k) :
    (A.shortTableauPivot x y).submatrix x.succAbove y.succAbove i j =
    A (x.succAbove i) (y.succAbove j) - A (x.succAbove i) y * A x (y.succAbove j) / A x y := by
  simp [shortTableauPivot, y.succAbove_ne j, x.succAbove_ne i]

lemma Matrix.shortTableauPivot_submatrix_eq [DivisionRing F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F)
    {x y : Fin k.succ} :
    (A.shortTableauPivot x y).submatrix x.succAbove y.succAbove =
    Matrix.of (fun i j : Fin k => A (x.succAbove i) (y.succAbove j) - A (x.succAbove i) y * A x (y.succAbove j) / A x y) := by
  ext i j
  exact A.shortTableauPivot_submatrix_succAbove_pivot_apply i j

-- ## Lemma 1 of Proof of Regularity of 2-Sum and 3-Sum of Matroids

private abbrev Fin.reindexingAux {n : ℕ} (i : Fin n.succ) : Fin 1 ⊕ Fin n → Fin n.succ :=
  (·.casesOn i i.succAbove)

private lemma Fin.reindexingAux_bijective {n : ℕ} (i : Fin n.succ) : i.reindexingAux.Bijective :=
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
  Equiv.ofBijective i.reindexingAux i.reindexingAux_bijective

private lemma reindexing_symm_eq_left {n : ℕ} (i k : Fin n.succ) (j : Fin 1) :
    i.reindexing.symm k = ◩j ↔ i = k := by
  unfold Fin.reindexing
  constructor <;> intro hk
  on_goal 1 =>
    apply_fun i.reindexingAux at hk
    rw [Equiv.ofBijective_apply_symm_apply i.reindexingAux i.reindexingAux_bijective k] at hk
  on_goal 2 =>
    apply_fun i.reindexingAux using i.reindexingAux_bijective.left
    rw [Equiv.ofBijective_apply_symm_apply i.reindexingAux i.reindexingAux_bijective k]
  all_goals
    simp [hk]

private lemma reindexing_symm_eq_right {n : ℕ} (i k : Fin n.succ) (j : Fin n) :
    i.reindexing.symm k = ◪j ↔ k = (i.succAbove j) := by
  unfold Fin.reindexing
  constructor <;> intro hkj
  on_goal 1 =>
    apply_fun i.reindexingAux at hkj
    rw [Equiv.ofBijective_apply_symm_apply i.reindexingAux i.reindexingAux_bijective k] at hkj
  on_goal 2 =>
    apply_fun i.reindexingAux using i.reindexingAux_bijective.1
    rw [Equiv.ofBijective_apply_symm_apply i.reindexingAux i.reindexingAux_bijective k]
  all_goals
    simp [hkj]

private abbrev Matrix.block₁₁ (k : ℕ) (x y : Fin k.succ) (A : Matrix (Fin k.succ) (Fin k.succ) F) : Matrix (Fin 1) (Fin 1) F :=
  !![A x y]

private abbrev Matrix.block₁₂ (k : ℕ) (x y : Fin k.succ) (A : Matrix (Fin k.succ) (Fin k.succ) F) : Matrix (Fin 1) (Fin k) F :=
  Matrix.of (fun _ j => A x (y.succAbove j))

private abbrev Matrix.block₂₁ (k : ℕ) (x y : Fin k.succ) (A : Matrix (Fin k.succ) (Fin k.succ) F) : Matrix (Fin k) (Fin 1) F :=
  Matrix.of (fun i _ => A (x.succAbove i) y)

private abbrev Matrix.block₂₂ (k : ℕ) (x y : Fin k.succ) (A : Matrix (Fin k.succ) (Fin k.succ) F) : Matrix (Fin k) (Fin k) F :=
  Matrix.of (fun i j => A (x.succAbove i) (y.succAbove j))

private lemma Matrix.succAboveAt_block [DivisionRing F] {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) (x y : Fin k.succ) :
    A = (Matrix.fromBlocks (A.block₁₁ k x y) (A.block₁₂ k x y) (A.block₂₁ k x y) (A.block₂₂ k x y)
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
    (A.block₂₂ k x y) - (A.block₂₁ k x y) * (A.block₁₁ k x y)⁻¹ * (A.block₁₂ k x y) := by
  rw [Matrix.shortTableauPivot_submatrix_eq]
  conv in _ / _ => rw [div_eq_mul_inv _ (A x y)]
  rw [show (A.block₁₁ k x y)⁻¹ = !![(A x y)⁻¹] from Matrix.ext (by simp [·.eq_zero, ·.eq_zero])]
  ext i j
  simp [Matrix.mul_apply, mul_right_comm]

private noncomputable instance invertible_matrix_fin1_of_ne_zero [Field F] {A : Matrix (Fin 1) (Fin 1) F}
    [hAxy : NeZero (A 0 0)] :
    Invertible A :=
  A.invertibleOfLeftInverse A⁻¹ (by
    ext i j
    rw [i.eq_zero, j.eq_zero]
    simp [IsUnit.inv_mul_cancel (IsUnit.mk0 _ hAxy.out)])

private lemma shortTableauPivot_submatrix_succAbove_succAbove_det_abs_eq_div [LinearOrderedField F] {k : ℕ}
    {A : Matrix (Fin k.succ) (Fin k.succ) F} {x y : Fin k.succ} (hAxy : A x y ≠ 0) :
    |((A.shortTableauPivot x y).submatrix x.succAbove y.succAbove).det| = |A.det| / |A x y| := by
  have : NeZero (A.block₁₁ k x y 0 0) := ⟨by simpa⟩
  rw [
    Matrix.shortTableauPivot_submatrix_eq_blockish, eq_div_iff_mul_eq (abs_ne_zero.← hAxy), mul_comm,
    ←show (A.block₁₁ k x y).det = A x y from Matrix.det_fin_one_of _,
    ←abs_mul, ←(A.block₁₁ k x y).invOf_eq_nonsing_inv, ←Matrix.det_fromBlocks₁₁]
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
    (hA : A.det ∉ SignType.cast.range) (i j : Fin k.succ) (hAij : A i j = 1 ∨ A i j = -1) :
    ∃ f : Fin k → Fin k.succ, ∃ g : Fin k → Fin k.succ, f.Injective ∧ g.Injective ∧
      ((A.shortTableauPivot i j).submatrix f g).det ∉ SignType.cast.range := by
  have hAij0 : A i j ≠ 0
  · cases hAij with
    | inl h1 =>
      rw [h1]
      norm_num
    | inr h9 =>
      rw [h9]
      norm_num
  obtain ⟨f, g, hf, hg, hAfg⟩ := shortTableauPivot_submatrix_det_abs_eq_div hAij0
  use f, g, hf, hg
  rw [in_signTypeCastRange_iff_abs, hAfg]
  cases hAij with
  | inl h1 => rwa [h1, abs_one, div_one, ←in_signTypeCastRange_iff_abs]
  | inr h9 => rwa [h9, abs_neg, abs_one, div_one, ←in_signTypeCastRange_iff_abs]

/-
TODOs refactor arguments in (no urgency):
Matrix.block₁₁
Matrix.block₁₂
Matrix.block₂₁
Matrix.block₂₂
-/
