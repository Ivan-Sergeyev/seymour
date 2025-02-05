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

/-- Add `c` times the `x`th row of `A` to the `r`th row of `A` and keep the rest of `A` unchanged. -/
private def Matrix.addRowMul [Semiring F] (A : Matrix X Y F) (x r : X) (c : F) :
    Matrix X Y F :=
  A.updateRow r (A r + c • A x)

private lemma Matrix.IsTotallyUnimodular.addRowMul [CommRing F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) {x r : X} (hxr : x ≠ r) (c : F) :
    (A.addRowMul x r c).IsTotallyUnimodular := by
  intro k f g hf hg
  if hi : ∃ i : Fin k, f i = r then
    obtain ⟨i, rfl⟩ := hi
    convert_to ((A.submatrix f g).updateRow i ((A.submatrix f g) i + c • (A.submatrix id g) x)).det ∈ Set.range SignType.cast
    · congr
      ext i' j'
      if hii : i' = i then
        simp [Matrix.addRowMul, hii]
      else
        have hfii : f i' ≠ f i := (hii <| hf ·)
        simp [Matrix.addRowMul, hii, hfii]
    -- More assumption will be needed. The lemmas does not hold as is! Not even for `c = 1` does it universally hold.
    let i' : Fin k := sorry
    have hii : i ≠ i' := sorry
    have hAg : A.submatrix id g x = A.submatrix f g i'
    · sorry -- TODO what if `x` comes from the part of the matrix that `f` misses?
    rw [hAg, Matrix.det_updateRow_add_smul_self _ hii]
    exact hA k f g hf hg
  else
    convert hA k f g hf hg using 2
    simp_all [Matrix.submatrix, Matrix.addRowMul]

/-- Add `q` times the `x`th row of `A` to all rows of `A` except the `x`th row (where `q` is different for each row). -/
private def Matrix.addMultiple [Semifield F] (A : Matrix X Y F) (x : X) (q : X → F) :
    Matrix X Y F :=
  fun i : X => if i = x then A x else A i + q i • A x

private lemma Matrix.IsTotallyUnimodular.addMultiple [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (q : X → F) :
    (A.addMultiple x q).IsTotallyUnimodular := by
  sorry -- This lemma does not hold for the same reasons as the lemma above.

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
    (((Matrix.fromCols 1 A).addMultiple x (- A · y / A x y)).getSmallTableau x y).mulRow x (1 / A x y) := by
  ext i j
  if hj : j = y then
    by_cases hi : i = x <;>
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
  else
    if hi : i = x then
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      exact div_eq_inv_mul (A x j) (A x y)
    else
      simp [Matrix.shortTableauPivot, Matrix.fromCols, Matrix.addMultiple, Matrix.getSmallTableau, Matrix.mulRow, hj, hi]
      ring

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 2) → (Fin 3) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster == (M.addMultiple 0 (- M · 0 / M 0 0)).testTotallyUnimodularFaster

/-- info: true -/
#guard_msgs in
#eval ∀ m : (Fin 3) → (Fin 2) → ({0, 1, -1} : Finset ℚ),
  let M : Matrix (Fin 3) (Fin 2) ℚ := Matrix.of (fun i j => (m i j).val)
  M.testTotallyUnimodularFaster ≤ (M.addMultiple 0 (- M · 0 / M 0 0)).testTotallyUnimodularFaster
-- `→` seems to hold unconditionally

/-- Pivoting preserves total unimodularity. -/
lemma Matrix.IsTotallyUnimodular.shortTableauPivot [Field F] {A : Matrix X Y F}
    (hA : A.IsTotallyUnimodular) (x : X) (y : Y) :
    (A.shortTableauPivot x y).IsTotallyUnimodular := by
  rw [Matrix.shortTableauPivot_eq]
  have hAxy : 1 / A x y ∈ Set.range SignType.cast
  · rw [inv_eq_self_of_in_set_range_singType_cast] <;> exact hA.apply x y
  exact (((hA.one_fromCols).addMultiple x _).getSmallTableau x y).mulRow x hAxy
