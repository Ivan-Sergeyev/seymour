import Seymour.Basic
import Seymour.Computable.MatrixTU


variable {X Y F : Type} [DecidableEq X] [DecidableEq Y]

/-- The result of the pivot operation in a short tableau (without exchanging the indices that define the pivot).
This definition makes sense only if `A x y` is nonzero. -/
def Matrix.shortTableauPivot [Field F] (A : Matrix X Y F) (x : X) (y : Y) :
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

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M 0 0 == 0  ∨  M.testTotallyUnimodular == (M.shortTableauPivot 0 0).testTotallyUnimodular
-- tested for matrices up to 2 × 4

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M 0 0 == 0  ∨  M.testTotallyUnimodularFaster == (M.shortTableauPivot 0 0).testTotallyUnimodularFaster
-- tested for matrices up to 3 × 3

lemma Matrix.shortTableauPivot_row_pivot [Field F] (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y x =
    (fun j : Y => if j = y then 1 / A x y else A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot]

lemma Matrix.shortTableauPivot_row_other [Field F] (A : Matrix X Y F) (x : X) (y : Y) (i : X) (hix : i ≠ x) :
    A.shortTableauPivot x y i =
    (fun j : Y => if j = y then - A i y / A x y else A i j - A i y * A x j / A x y) := by
  ext
  simp [Matrix.shortTableauPivot, hix]


omit [DecidableEq Y] in
/-- Multiply the `x`th row of `A` by `c` and keep the rest of `A` unchanged. -/
private def Matrix.mulRow [NonUnitalNonAssocSemiring F] (A : Matrix X Y F) (x : X) (c : F) :
    Matrix X Y F :=
  A.updateRow x (c • A x)

omit [DecidableEq Y] in
private lemma Matrix.IsTotallyUnimodular.mulRow [CommRing F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) {c : F} (hc : c ∈ Set.range SignType.cast) :
    (A.mulRow x c).IsTotallyUnimodular := by
  intro k f g hf hg
  if hi : ∃ i : Fin k, f i = x then
    obtain ⟨i, rfl⟩ := hi
    convert_to ((A.submatrix f g).updateRow i (c • (A.submatrix id g) (f i))).det ∈ Set.range SignType.cast
    · congr
      ext i' j'
      if hii : i' = i then
        simp [Matrix.mulRow, hii]
      else
        have hfii : f i' ≠ f i := (hii <| hf ·)
        simp [Matrix.mulRow, hii, hfii]
    rw [Matrix.det_updateRow_smul]
    apply in_set_range_singType_cast_mul_in_set_range_singType_cast hc
    have hAf := hA.submatrix f id
    rw [Matrix.isTotallyUnimodular_iff] at hAf
    convert hAf k id g
    rw [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
    exact (A.submatrix f g).updateRow_eq_self i
  else
    convert hA k f g hf hg using 2
    simp_all [Matrix.submatrix, Matrix.mulRow]

/-- Add `q` times the `x`th row of `A` to all rows of `A` except the `x`th row (where `q` is different for each row). -/
private def Matrix.addMultiples [Semifield F] (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i : X => if i = x then A x else A i + q i • A x

private lemma Matrix.IsTotallyUnimodular.addMultiples [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.addMultiples x (- A · y / A x y)).IsTotallyUnimodular := by
  intro k f g hf hg
  -- If `x` is in the selected rows, prove by induction that the determinant doesn't change.
  -- Else if `y` is in the selected columns, its column is all zeros so the determinant is zero.
  -- Else perform the expansion on the `y` column, the smaller determinant is equal to ± the bigger determinant,
  -- which did not change by the same argument as above.
  sorry

omit [DecidableEq X] in
/-- The small tableau consists of all columns but `x`th from the original matrix and the `y`th column of the square matrix. -/
private def Matrix.getSmallTableau (A : Matrix X (X ⊕ Y) F) (x : X) (y : Y) :
    Matrix X Y F :=
  Matrix.of (fun i : X => fun j : Y => if j = y then A i (Sum.inl x) else A i (Sum.inr j))

omit [DecidableEq X] in
private lemma Matrix.IsTotallyUnimodular.getSmallTableau [CommRing F]
    {A : Matrix X (X ⊕ Y) F} (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.getSmallTableau x y).IsTotallyUnimodular := by
  convert
    hA.submatrix id (fun j : Y => if j = y then Sum.inl x else Sum.inr j)
  unfold Matrix.getSmallTableau
  aesop

private lemma Matrix.shortTableauPivot_eq [Field F] (A : Matrix X Y F) (x : X) (y : Y) :
    A.shortTableauPivot x y =
    ((A.prependId.addMultiples x (- A · y / A x y)).getSmallTableau x y).mulRow x (1 / A x y) := by
  ext i j
  if hj : j = y then
    by_cases hi : i = x <;>
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiples, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
  else
    if hi : i = x then
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiples, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      exact div_eq_inv_mul (A x j) (A x y)
    else
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiples, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      ring

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster == (M.addMultiples 0 (- M · 0 / M 0 0)).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 3) → (Fin 2) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 3) (Fin 2) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ (M.addMultiples 0 (- M · 0 / M 0 0)).testTotallyUnimodularFaster
-- `→` seems to hold unconditionally

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster == ((M.prependId.addMultiples 0 (- M · 0 / M 0 0)).getSmallTableau 0 0).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 3) → (Fin 2) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 3) (Fin 2) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ ((M.prependId.addMultiples 0 (- M · 0 / M 0 0)).getSmallTableau 0 0).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ ((M.addMultiples 0 (- M · 0 / M 0 0)).mulRow 0 (1 / M 0 0)).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 3) → (Fin 2) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 3) (Fin 2) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ ((M.addMultiples 0 (- M · 0 / M 0 0)).mulRow 0 (1 / M 0 0)).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ (((M.prependId.addMultiples 0 (- M · 0 / M 0 0)).getSmallTableau 0 0).mulRow 0 (1 / M 0 0)).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 3) → (Fin 2) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 3) (Fin 2) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ (((M.prependId.addMultiples 0 (- M · 0 / M 0 0)).getSmallTableau 0 0).mulRow 0 (1 / M 0 0)).testTotallyUnimodularFaster


/-- Pivoting preserves total unimodularity. -/
lemma Matrix.IsTotallyUnimodular.shortTableauPivot [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.shortTableauPivot x y).IsTotallyUnimodular := by
  rw [Matrix.shortTableauPivot_eq]
  have hAxy : 1 / A x y ∈ Set.range SignType.cast
  · rw [inv_eq_self_of_in_set_range_singType_cast] <;> exact hA.apply x y
  exact (((hA.one_fromCols).addMultiples x (Sum.inr y)).getSmallTableau x y).mulRow x hAxy
