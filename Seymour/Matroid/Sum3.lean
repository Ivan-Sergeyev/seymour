import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Conversions
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Regularity

/-!
# Matroid 3-sum

Here we study the 3-sum of matroids (starting with the 3-sum of matrices).
-/

/-! ## Matrix-level 3-sum -/

/-! ### Additional notation for convenience -/

/-!
  We define the unsigned and the signed version of the special cases of the 3×3 submatrix in the intersection of the summands.
-/

/-- Unsigned version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
private def matrix3x3unsigned₀ (R : Type*) [Zero R] [One R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 1; 0, 1, 1; 1, 1, 0]

/-- Unsigned version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
private def matrix3x3unsigned₁ (R : Type*) [Zero R] [One R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 1, 1; 0, 1, 1; 1, 1, 0]

/-- Signed version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
private def matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 1; 0, -1, 1; 1, 1, 0]

/-- Signed version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
private def matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ :=
  matrix3x3unsigned₁ ℚ


/-! ### Definition -/

/-- Structural data of 3-sum of matrices. -/
structure MatrixSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type*) (R : Type*) where
  Aₗ  : Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Fin 2) R
  Dₗ  : Matrix (Fin 2) Yₗ R
  D₀ₗ : Matrix (Fin 2) (Fin 2) R
  D₀ᵣ : Matrix (Fin 2) (Fin 2) R
  Dᵣ  : Matrix Xᵣ (Fin 2) R
  Aᵣ  : Matrix (Fin 2 ⊕ Xᵣ) (Unit ⊕ Yᵣ) R

/-- The bottom-left block of 3-sum. -/
noncomputable abbrev MatrixSum3.D {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [CommRing R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Fin 2 ⊕ Xᵣ) (Yₗ ⊕ Fin 2) R :=
  ⊞ S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ

/-- The resulting matrix of 3-sum. -/
noncomputable def MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [CommRing R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix ((Xₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ)) R :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ


/-! ### Conversion of summands -/

/-- Constructs 3-sum from summands in block form. -/
def blocksToMatrixSum3 {Xₗ Yₗ Xᵣ Yᵣ R : Type*}
    (Bₗ : Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) R)
    (Bᵣ : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) R) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R where
  Aₗ  := Bₗ.toBlocks₁₁
  Dₗ  := Bₗ.toBlocks₂₁.toCols₁
  D₀ₗ := Bₗ.toBlocks₂₁.toCols₂
  D₀ᵣ := Bᵣ.toBlocks₂₁.toRows₁
  Dᵣ  := Bᵣ.toBlocks₂₁.toRows₂
  Aᵣ  := Bᵣ.toBlocks₂₂

/-- Reconstructs the left summand from the matrix 3-sum structure. -/
private abbrev MatrixSum3.Bₗ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) R :=
  ⊞ S.Aₗ 0 (S.Dₗ ◫ S.D₀ₗ) (▮![S.Aᵣ ◩0 ◩0, S.Aᵣ ◩1 ◩0])

@[app_unexpander MatrixSum3.Bₗ]
private def MatrixSum3.Bₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Bₗ))
  | _ => throw ()

/-- Reconstructs the right summand from the matrix 3-sum structure. -/
private abbrev MatrixSum3.Bᵣ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) R :=
  ⊞ (▬![S.Aₗ ◪0 ◪0, S.Aₗ ◪0 ◪1]) 0 (S.D₀ᵣ ⊟ S.Dᵣ) S.Aᵣ

@[app_unexpander MatrixSum3.Bᵣ]
private def MatrixSum3.Bᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Bᵣ))
  | _ => throw ()

/-- If the 3-sum is constructed from summands in block form, reconstructing the left summand yields the original one. -/
private lemma blocksToMatrixSum3_Bₗ_eq {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R]
    (Bₗ : Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) R)
    (Bᵣ : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) R)
    (hBₗ : Bₗ ◪0 ◪0 = Bᵣ ◪◩0 ◪◩0 ∧ Bₗ ◪1 ◪0 = Bᵣ ◪◩1 ◪◩0 ∧ ∀ i, Bₗ ◩i ◪0 = 0) :
    (blocksToMatrixSum3 Bₗ Bᵣ).Bₗ = Bₗ := by
  ext i j
  cases j with
  | inl jₗ => cases jₗ <;> cases i <;> tauto
  | inr jᵣ =>
    fin_cases jᵣ
    cases i with
    | inl iₗ => have := hBₗ.right.right iₗ; tauto
    | inr iᵣ => fin_cases iᵣ <;> tauto

/-- If the 3-sum is constructed from summands in block form, reconstructing the right summand yields the original one. -/
private lemma blocksToMatrixSum3_Bᵣ_eq {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R]
    (Bₗ : Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) R)
    (Bᵣ : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) R)
    (hBᵣ : Bᵣ ◩0 ◩0 = Bₗ ◩◪0 ◩◪0 ∧ Bᵣ ◩0 ◩1 = Bₗ ◩◪0 ◩◪1 ∧ ∀ i, Bᵣ ◩0 ◪i = 0) :
    (blocksToMatrixSum3 Bₗ Bᵣ).Bᵣ = Bᵣ := by
  ext i j
  cases i with
  | inl iₗ =>
    fin_cases iₗ
    cases j with
    | inl jₗ => fin_cases jₗ <;> tauto
    | inr jᵣ => have := hBᵣ.right.right jᵣ; tauto
  | inr iᵣ => cases iᵣ <;> cases j <;> tauto

/-- The 3×3 submatrix of the reconstructed left summand in the intersection of the summands. -/
private abbrev MatrixSum3.Sₗ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Fin 3) (Fin 3) R :=
  S.Bₗ.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]

@[app_unexpander MatrixSum3.Sₗ]
private def MatrixSum3.Sₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Sₗ))
  | _ => throw ()

/-- The 3×3 submatrix of the reconstructed right summand in the intersection of the summands. -/
private abbrev MatrixSum3.Sᵣ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [Zero R] [One R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Fin 3) (Fin 3) R :=
  S.Bᵣ.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]

@[app_unexpander MatrixSum3.Sᵣ]
private def MatrixSum3.Sᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Sᵣ))
  | _ => throw ()


/-! ## Canonical signing of matrices -/

/-! ### Definition -/

/-! All declarations in this section are private. -/

/-- Canonical re-signing of a matrix. -/
private def Matrix.toCanonicalSigning {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix X Y ℚ :=
  let u : X → ℚ := (fun i : X =>
    if i = x₀ then Q x₀ y₀ * Q x₂ y₀ else
    if i = x₁ then Q x₀ y₀ * Q x₀ y₂ * Q x₁ y₂ * Q x₂ y₀ else
    if i = x₂ then 1 else
    1)
  let v : Y → ℚ := (fun j : Y =>
    if j = y₀ then Q x₂ y₀ else
    if j = y₁ then Q x₂ y₁ else
    if j = y₂ then Q x₀ y₀ * Q x₀ y₂ * Q x₂ y₀ else
    1)
  Q ⊡ u ⊗ v

@[app_unexpander Matrix.toCanonicalSigning]
private def Matrix.toCanonicalSigning_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `toCanonicalSigning))
  | _ => throw ()


/-! ### General results -/

/-! All declarations in this section are private. -/

/-- Canonical re-signing of a TU matrix is TU. -/
private lemma Matrix.IsTotallyUnimodular.toCanonicalSigning {X Y : Type*} [DecidableEq X] [DecidableEq Y] {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTotallyUnimodular := by
  have hu : ∀ i : X,
    (fun i : X =>
      if i = x₀ then Q x₀ y₀ * Q x₂ y₀ else
      if i = x₁ then Q x₀ y₀ * Q x₀ y₂ * Q x₁ y₂ * Q x₂ y₀ else
      if i = x₂ then 1 else
      1) i ∈ SignType.cast.range
  · intro i
    if hix₀ : i = x₀ then
      simp_rw [hix₀, ite_true]
      apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix₁ : i = x₁ then
      simp_rw [hix₀, ite_false, hix₁, ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix₂ : i = x₂ then
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix₂, ite_true]
      exact one_in_signTypeCastRange
    else
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix₂, ite_false]
      exact one_in_signTypeCastRange
  have hv : ∀ j : Y,
    (fun j : Y =>
      if j = y₀ then Q x₂ y₀ else
      if j = y₁ then Q x₂ y₁ else
      if j = y₂ then Q x₀ y₀ * Q x₀ y₂ * Q x₂ y₀ else
      1) j ∈ SignType.cast.range
  · intro j
    if hjy₀ : j = y₀ then
      simp_rw [hjy₀, ite_true]
      apply hQ.apply
    else if hjy₁ : j = y₁ then
      simp_rw [hjy₀, ite_false, hjy₁, ite_true]
      apply hQ.apply
    else if hjy₂ : j = y₂ then
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy₂, ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy₂, ite_false]
      exact one_in_signTypeCastRange
  unfold Matrix.toCanonicalSigning
  exact Q.entrywiseProduct_outerProduct_eq_mul_col_mul_row _ _ ▸ (hQ.mul_rows hu).mul_cols hv


/-! ### Definition of re-signing in two special cases -/

/-! All declarations in this section are private. -/

/-- Sufficient condition for existence of a TU canonical signing in the first special case. -/
private def Matrix.HasTuCanonicalSigning₀ {X Y : Type*} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₀ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₀]
private def Matrix.HasTuCanonicalSigning₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₀))
  | _ => throw ()

/-- Sufficient condition for existence of a TU canonical signing in the second spcial case. -/
private def Matrix.HasTuCanonicalSigning₁ {X Y : Type*} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₁ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₁]
private def Matrix.HasTuCanonicalSigning₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₁))
  | _ => throw ()


/-! ### Lemmas about distinctness of row and column indices -/

/-! All declarations in this section are private. -/

private lemma Matrix.HasTuCanonicalSigning₀.distinct_x₀_x₁_x₂ {X Y : Type*} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hxx
    rw [hxx] at hQ
    have hQ01 := congr_fun₂ hQ.right 0 0
    have hQ11 := congr_fun₂ hQ.right 1 0
    have hQ21 := congr_fun₂ hQ.right 2 0
    have hQ02 := congr_fun₂ hQ.right 0 2
    have hQ22 := congr_fun₂ hQ.right 2 2
    simp [Matrix.abs] at hQ01 hQ11 hQ21 hQ02 hQ22
    simp_all

private lemma Matrix.HasTuCanonicalSigning₀.distinct_y₀_y₁_y₂ {X Y : Type*} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hyy
    rw [hyy] at hQ
    have hQ10 := congr_fun₂ hQ.right 1 0
    have hQ11 := congr_fun₂ hQ.right 1 1
    have hQ12 := congr_fun₂ hQ.right 1 2
    have hQ21 := congr_fun₂ hQ.right 2 1
    have hQ22 := congr_fun₂ hQ.right 2 2
    simp [Matrix.abs] at hQ10 hQ11 hQ12 hQ21 hQ22
    simp_all

private lemma Matrix.HasTuCanonicalSigning₁.distinct_x₀_x₁_x₂ {X Y : Type*} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hxx
    rw [hxx] at hQ
    have hQ01 := congr_fun₂ hQ.right 0 0
    have hQ11 := congr_fun₂ hQ.right 1 0
    have hQ21 := congr_fun₂ hQ.right 2 0
    have hQ02 := congr_fun₂ hQ.right 0 2
    have hQ22 := congr_fun₂ hQ.right 2 2
    simp [Matrix.abs] at hQ01 hQ11 hQ21 hQ02 hQ22
    simp_all

private lemma Matrix.HasTuCanonicalSigning₁.distinct_y₀_y₁_y₂ {X Y : Type*} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hyy
    rw [hyy] at hQ
    have hQ10 := congr_fun₂ hQ.right 1 0
    have hQ11 := congr_fun₂ hQ.right 1 1
    have hQ12 := congr_fun₂ hQ.right 1 2
    have hQ21 := congr_fun₂ hQ.right 2 1
    have hQ22 := congr_fun₂ hQ.right 2 2
    simp [Matrix.abs] at hQ10 hQ11 hQ12 hQ21 hQ22
    simp_all

/-- Re-signing a TU matrix in the first special case transforms the 3×3 submatrix to its canonically signed version.
    Note: the proof takes a long time to compile due to the large number of case distinctions. -/
private lemma Matrix.HasTuCanonicalSigning₀.toCanonicalSigning_submatrix3x3 {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂] = matrix3x3signed₀ := by
  have hQ₀₀ := congr_fun₂ hQ.right 0 0
  have hQ₀₁ := congr_fun₂ hQ.right 0 1
  have hQ₀₂ := congr_fun₂ hQ.right 0 2
  have hQ₁₀ := congr_fun₂ hQ.right 1 0
  have hQ₁₁ := congr_fun₂ hQ.right 1 1
  have hQ₁₂ := congr_fun₂ hQ.right 1 2
  have hQ₂₀ := congr_fun₂ hQ.right 2 0
  have hQ₂₁ := congr_fun₂ hQ.right 2 1
  have hQ₂₂ := congr_fun₂ hQ.right 2 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  obtain ⟨d, hd⟩ := (hQ.left.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).det ![x₀, x₁, x₂] ![y₀, y₁, y₂]
  simp [Matrix.det_fin_three, Matrix.toCanonicalSigning, hQ₀₁, hQ₁₀, hQ₂₂, hQ.distinct_x₀_x₁_x₂, hQ.distinct_y₀_y₁_y₂] at hd ⊢
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.toCanonicalSigning, hQ.distinct_x₀_x₁_x₂, hQ.distinct_y₀_y₁_y₂, hQ₀₁, hQ₁₀, hQ₂₂]
  all_goals
    clear hQ₀₁ hQ₁₀ hQ₂₂
    cases hQ₀₀ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
    <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
    <;> simp [*] at hd

/-- Re-signing a TU matrix in the second special case transforms the 3×3 submatrix to its canonically signed version. -/
private lemma Matrix.HasTuCanonicalSigning₁.toCanonicalSigning_submatrix3x3 {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂] = matrix3x3signed₁ := by
  have hQ₀₀ := congr_fun₂ hQ.right 0 0
  have hQ₀₁ := congr_fun₂ hQ.right 0 1
  have hQ₀₂ := congr_fun₂ hQ.right 0 2
  have hQ₁₀ := congr_fun₂ hQ.right 1 0
  have hQ₁₁ := congr_fun₂ hQ.right 1 1
  have hQ₁₂ := congr_fun₂ hQ.right 1 2
  have hQ₂₀ := congr_fun₂ hQ.right 2 0
  have hQ₂₁ := congr_fun₂ hQ.right 2 1
  have hQ₂₂ := congr_fun₂ hQ.right 2 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  obtain ⟨d₁, hd₁⟩ := (hQ.left.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).det ![x₀, x₂] ![y₀, y₁]
  obtain ⟨d₂, hd₂⟩ := (hQ.left.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).det ![x₀, x₁] ![y₁, y₂]
  simp [Matrix.det_fin_two, Matrix.toCanonicalSigning, hQ₁₀, hQ₂₂, hQ.distinct_x₀_x₁_x₂, hQ.distinct_y₀_y₁_y₂] at hd₁ hd₂
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.toCanonicalSigning, hQ.distinct_x₀_x₁_x₂, hQ.distinct_y₀_y₁_y₂, hQ₁₀, hQ₂₂]
  all_goals
    clear hQ₁₀ hQ₂₂
    cases hQ₀₀ <;> cases hQ₀₁ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
    <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
    <;> simp [*] at hd₁ hd₂


/-! ## Canonical signing of 3-sum of matrices -/

/-! ### Additional notation for special rows and columns and their properties -/

/-- First special column of `S.Bᵣ` used to generate `S.D`. -/
@[simp]
private abbrev MatrixSum3.c₀ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Fin 2 ⊕ Xᵣ → R :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 0)

@[app_unexpander MatrixSum3.c₀]
private def MatrixSum3.c₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `c₀))
  | _ => throw ()

/-- Second special column of `S.Bᵣ` used to generate `S.D`. -/
@[simp]
private abbrev MatrixSum3.c₁ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Fin 2 ⊕ Xᵣ → R :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 1)

@[app_unexpander MatrixSum3.c₁]
private def MatrixSum3.c₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `c₁))
  | _ => throw ()

/-- First special row of `S.Bₗ` used to generate `S.D`. -/
@[simp]
private abbrev MatrixSum3.d₀ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Yₗ ⊕ Fin 2 → R :=
  (S.Dₗ ◫ S.D₀ₗ) 0

@[app_unexpander MatrixSum3.d₀]
private def MatrixSum3.d₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `d₀))
  | _ => throw ()

/-- Second special row of `S.Bₗ` used to generate `S.D`. -/
@[simp]
private abbrev MatrixSum3.d₁ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Yₗ ⊕ Fin 2 → R :=
  (S.Dₗ ◫ S.D₀ₗ) 1

@[app_unexpander MatrixSum3.d₁]
private def MatrixSum3.d₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `d₁))
  | _ => throw ()

/-- Property of a vector to be in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`. -/
abbrev Function.IsParallelTo₃ {X R : Type*} [Zero R] [Neg R] (v : X → R) (c₀ c₁ c₂ : X → R) : Prop :=
  v = 0 ∨ v = c₀ ∨ v = -c₀ ∨ v = c₁ ∨ v = -c₁ ∨ v = c₂ ∨ v = -c₂

/-- If a vector is in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`, then its opposite belongs to the same set. -/
private lemma Function.IsParallelTo₃.neg {X R : Type*} [CommRing R] {v : X → R} {c₀ c₁ c₂ : X → R}
    (hv : v.IsParallelTo₃ c₀ c₁ c₂) :
    (-v).IsParallelTo₃ c₀ c₁ c₂ := by
  rcases hv with (hv | hv | hv | hv | hv | hv | hv)
  all_goals
    rw [hv]
    ring_nf
    simp only [Function.IsParallelTo₃, true_or, or_true]

/-- If a vector is in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`, then scaling it by a `{0, ±1}` factor keeps it by the same set. -/
private lemma Function.IsParallelTo₃.mul_sign {X R : Type*} [CommRing R] {v : X → R} {c₀ c₁ c₂ : X → R}
    (hv : v.IsParallelTo₃ c₀ c₁ c₂) {q : R} (hq : q ∈ SignType.cast.range) :
    (fun i : X => v i * q).IsParallelTo₃ c₀ c₁ c₂ := by
  obtain ⟨s, hs⟩ := hq
  cases s with
  | zero =>
    simp only [SignType.zero_eq_zero, SignType.coe_zero] at hs
    simp only [←hs, mul_zero]
    left
    rfl
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one] at hs
    simp [←hs]
    exact hv
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
    simp only [←hs, mul_neg, mul_one]
    exact hv.neg


/-! ### Auxiliary definitions -/

/-! All declarations in this section are private. -/

/-- Sufficient condition for existence of a canonical signing of a 3-sum of matrices over `Z2`. -/
private def MatrixSum3.HasCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  (S.Bₗ.HasTuSigning ∧ S.Bᵣ.HasTuSigning)
  ∧ ((S.Sₗ = matrix3x3unsigned₀ Z2 ∧ S.Sᵣ = matrix3x3unsigned₀ Z2) ∨
     (S.Sₗ = matrix3x3unsigned₁ Z2 ∧ S.Sᵣ = matrix3x3unsigned₁ Z2))

/-- Proposition that `S` is a canonical signing of a 3-sum of matrices. -/
private def MatrixSum3.IsCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  (S.Bₗ.IsTotallyUnimodular ∧ S.Bᵣ.IsTotallyUnimodular)
  ∧ ((S.Sₗ = matrix3x3signed₀ ∧ S.Sᵣ = matrix3x3signed₀) ∨
     (S.Sₗ = matrix3x3signed₁ ∧ S.Sᵣ = matrix3x3signed₁))

/-- Canonically re-signs the left summand of a 3-sum. -/
private noncomputable abbrev Matrix.HasTuSigning.toCanonicalSummandₗ {Xₗ Yₗ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ]
    {Bₗ : Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) Z2} (hBₗ : Bₗ.HasTuSigning) :
    Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) ℚ :=
  hBₗ.choose.toCanonicalSigning ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0

/-- Canonically re-signs the right summand of a 3-sum. -/
private noncomputable abbrev Matrix.HasTuSigning.toCanonicalSummandᵣ {Xᵣ Yᵣ : Type*} [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Bᵣ : Matrix (Unit ⊕ Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ Unit ⊕ Yᵣ) Z2} (hBᵣ : Bᵣ.HasTuSigning) :
    Matrix (Unit ⊕ Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ Unit ⊕ Yᵣ) ℚ :=
  hBᵣ.choose.toCanonicalSigning ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0

/-- Canonical re-signing of a 3-sum of matrices over `Z2`. -/
private noncomputable def MatrixSum3.HasCanonicalSigning.toCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ :=
  blocksToMatrixSum3 hS.left.left.toCanonicalSummandₗ hS.left.right.toCanonicalSummandᵣ


/-! ### Soundness of definitions -/

/-!
  In this section we prove that `MatrixSum3.HasCanonicalSigning.toCanonicalSigning` satisfies `IsCanonicalSigning`.
-/

private lemma MatrixSum3.HasCanonicalSigning.summands_hasTuCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.left.left.choose.HasTuCanonicalSigning₀ ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0 ∧
    hS.left.right.choose.HasTuCanonicalSigning₀ ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0 ∨
    hS.left.left.choose.HasTuCanonicalSigning₁ ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0 ∧
    hS.left.right.choose.HasTuCanonicalSigning₁ ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0 := by
  rcases hS.right with hSr | hSr
  <;> [left; right]
  all_goals constructor
  <;> [have htu := hS.left.left.choose_spec.left; have htu := hS.left.right.choose_spec.left]
  <;> [have heq := hSr.left; have heq := hSr.right]
  <;> [have hsgn := hS.left.left.choose_spec.right; have hsgn := hS.left.right.choose_spec.right]
  all_goals
    refine ⟨htu, ?_⟩
    ext i j
    have hij := congr_fun₂ heq i j
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp [Matrix.abs, hij, hsgn _ _]

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bₗ = hS.left.left.toCanonicalSummandₗ := by
  unfold MatrixSum3.HasCanonicalSigning.toCanonicalSigning
  rw [blocksToMatrixSum3_Bₗ_eq]
  rcases hS.summands_hasTuCanonicalSigning with ⟨hBₗ, hBᵣ⟩ | ⟨hBₗ, hBᵣ⟩
  all_goals
    simp only [Matrix.HasTuSigning.toCanonicalSummandₗ, Matrix.HasTuSigning.toCanonicalSummandᵣ]
    refine ⟨?_, ?_, ?_⟩
    · have := congr_fun₂ hBₗ.toCanonicalSigning_submatrix3x3 0 2
      have := congr_fun₂ hBᵣ.toCanonicalSigning_submatrix3x3 0 2
      simp_all
    · have := congr_fun₂ hBₗ.toCanonicalSigning_submatrix3x3 1 2
      have := congr_fun₂ hBᵣ.toCanonicalSigning_submatrix3x3 1 2
      simp_all
    · intro i
      cases i with
      | inl iₗ =>
        simp [Matrix.toCanonicalSigning]
        left
        exact abs_eq_zero.→ (hS.left.left.choose_spec.right ◩◩iₗ ◪0)
      | inr iᵣ =>
        fin_cases iᵣ
        simpa using congr_fun₂ hBₗ.toCanonicalSigning_submatrix3x3 2 2

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bᵣ = hS.left.right.toCanonicalSummandᵣ := by
  unfold MatrixSum3.HasCanonicalSigning.toCanonicalSigning
  rw [blocksToMatrixSum3_Bᵣ_eq]
  rcases hS.summands_hasTuCanonicalSigning with ⟨hBₗ, hBᵣ⟩ | ⟨hBₗ, hBᵣ⟩
  all_goals
    simp only [Matrix.HasTuSigning.toCanonicalSummandₗ, Matrix.HasTuSigning.toCanonicalSummandᵣ]
    refine ⟨?_, ?_, ?_⟩
    · have := congr_fun₂ hBₗ.toCanonicalSigning_submatrix3x3 2 0
      have := congr_fun₂ hBᵣ.toCanonicalSigning_submatrix3x3 2 0
      simp_all
    · have := congr_fun₂ hBₗ.toCanonicalSigning_submatrix3x3 2 1
      have := congr_fun₂ hBᵣ.toCanonicalSigning_submatrix3x3 2 1
      simp_all
    · intro i
      cases i with
      | inl iₗ =>
        fin_cases iₗ
        simpa using congr_fun₂ hBᵣ.toCanonicalSigning_submatrix3x3 2 2
      | inr iᵣ =>
        simp [Matrix.toCanonicalSigning]
        exact abs_eq_zero.→ (hS.left.right.choose_spec.right ◩0 ◪◪iᵣ)

/-- Canonical re-signing transforms a 3-sum of matrices into its canonically signed version. -/
private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_isCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.IsCanonicalSigning := by
  constructor
  · rw [MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq, MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq]
    constructor
    · apply hS.left.left.choose_spec.left.toCanonicalSigning
    · apply hS.left.right.choose_spec.left.toCanonicalSigning
  · unfold MatrixSum3.Sₗ MatrixSum3.Sᵣ
    rw [MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq, MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq]
    rcases hS.summands_hasTuCanonicalSigning with hS' | hS' <;> [left; right]
    all_goals
      exact ⟨hS'.left.toCanonicalSigning_submatrix3x3, hS'.right.toCanonicalSigning_submatrix3x3⟩


/-! ### Lemmas about extending bottom-right block with special columns and top-left block with special rows -/

/-! All declarations in this section are private. -/

private lemma MatrixSum3.aux_d₀ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bₗ.IsTotallyUnimodular) (hSAᵣ : S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1) (i : Yₗ ⊕ Fin 2) :
    ![S.d₀ i, S.d₁ i] ≠ ![1, -1] ∧ ![S.d₀ i, S.d₁ i] ≠ ![-1, 1] := by
  have := hS.det ![◪0, ◪1] ![◩i, ◪0]
  constructor
  <;> intro contr
  <;> have := congr_fun contr 0
  <;> have := congr_fun contr 1
  <;> simp_all [Matrix.det_fin_two]

private lemma MatrixSum3.aux_c₀ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) (i : Fin 2 ⊕ Xᵣ) :
    ![S.c₀ i, S.c₁ i] ≠ ![1, -1] ∧ ![S.c₀ i, S.c₁ i] ≠ ![-1, 1] := by
  have := hS.det ![◪i, ◩0] ![◩0, ◩1]
  constructor
  <;> intro contr
  <;> have := congr_fun contr 0
  <;> have := congr_fun contr 1
  <;> simp_all [Matrix.det_fin_two]

private lemma MatrixSum3.c₀_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  let B : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) ℚ := S.Bᵣ.shortTableauPivot ◩0 ◩0
  let B' : Matrix (Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) ℚ := B.submatrix Sum.inr id
  have B'_eq : B' = (▮(-S.c₀) ◫ ▮(S.c₁ - S.c₀) ◫ S.Aᵣ).submatrix id equivUnitSumUnit.leftCongr.symm
  · ext _ (j₂ | _)
    · fin_cases j₂ <;> simp [Matrix.shortTableauPivot_eq, B, B', hSAₗ]
    · simp [Matrix.shortTableauPivot_eq, B, B']
  have hB : B.IsTotallyUnimodular
  · apply hS.shortTableauPivot
    simp [MatrixSum3.Bᵣ, hSAₗ]
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hScc : (▮(-S.c₀) ◫ ▮(S.c₁ - S.c₀) ◫ S.Aᵣ).IsTotallyUnimodular
  · simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, Matrix.submatrix_id_id] using
      hB'.submatrix id equivUnitSumUnit.leftCongr
  let q : (Unit ⊕ Unit) ⊕ (Unit ⊕ Yᵣ) → ℚ := (·.casesOn (-1) 1)
  have hq : ∀ i : (Unit ⊕ Unit) ⊕ (Unit ⊕ Yᵣ), q i ∈ SignType.cast.range
  · rintro (_|_) <;> simp [q]
  convert hScc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

private lemma MatrixSum3.c₂_c₁_Aᵣ_isTotallyUnimodular_of_Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮(S.c₀ - S.c₁) ◫ ▮S.c₁ ◫ S.Aᵣ).IsTotallyUnimodular := by
  let B : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) ℚ := S.Bᵣ.shortTableauPivot ◩0 ◩1
  let B' : Matrix (Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) ℚ := B.submatrix Sum.inr id
  have B'_eq : B' = (▮(S.c₀ - S.c₁) ◫ ▮(-S.c₁) ◫ S.Aᵣ).submatrix id equivUnitSumUnit.leftCongr.symm
  · ext _ (j₂ | _)
    · fin_cases j₂ <;> simp [Matrix.shortTableauPivot_eq, B, B', hSAₗ]
    · simp [Matrix.shortTableauPivot_eq, B, B']
  have hB : B.IsTotallyUnimodular
  · apply hS.shortTableauPivot
    simp [MatrixSum3.Bᵣ, hSAₗ]
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hScc : (▮(S.c₀ - S.c₁) ◫ ▮(-S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular
  · simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, Matrix.submatrix_id_id] using
      hB'.submatrix id equivUnitSumUnit.leftCongr
  let q : (Unit ⊕ Unit) ⊕ (Unit ⊕ Yᵣ) → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
  have hq : ∀ i : (Unit ⊕ Unit) ⊕ (Unit ⊕ Yᵣ), q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hScc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

private lemma MatrixSum3.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  intro k f g hf hg
  if hgc₂ : ∃ j, g j = ◩◪⟨⟩ then -- `c₂` is contained in the submatrix
    obtain ⟨j₂, hj₂⟩ := hgc₂
    if hgc₀ : ∃ j, g j = ◩◩◩⟨⟩ then -- `c₀` is contained in the submatrix
      obtain ⟨j₀, hj₀⟩ := hgc₀
      if hgc₁ : ∃ j, g j = ◩◩◪⟨⟩ then -- `c₁` is contained in the submatrix
        obtain ⟨j₁, hj₁⟩ := hgc₁
        use 0
        symm
        apply ((▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).submatrix f g).det_eq_zero_of_col_sub_col_eq_col j₀ j₁ j₂
        simp [hj₀, hj₁, hj₂]
        rfl
      else
        convert (S.c₀_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ hS hSAₗ).det f
          ((·.map (·.casesOn (·.casesOn Sum.inl Sum.inl) Sum.inr) id) ∘ g)
        ext i j
        cases hgj : g j with
        | inl z₃ => cases z₃ with
          | inl z₂ =>
            cases z₂ with
            | inl => simp [hgj]
            | inr => tauto
          | inr => simp [*]
        | inr z₁ => cases z₁ <;> simp [hgj]
    else
      convert (S.c₂_c₁_Aᵣ_isTotallyUnimodular_of_Bᵣ hS hSAₗ).det f
        ((·.map (·.casesOn (·.casesOn Sum.inr Sum.inr) Sum.inl) id) ∘ g)
      ext i j
      cases hgj : g j with
      | inl z₃ => cases z₃ with
        | inl z₂ =>
          cases z₂ with
          | inl => tauto
          | inr => simp [hgj]
        | inr => simp [*]
      | inr z₁ => cases z₁ <;> simp [hgj]
  else
    -- Here we have a submatrix of the original matrix.
    let f' : Fin k → Unit ⊕ (Fin 2 ⊕ Xᵣ) := Sum.inr ∘ f
    let g' : Fin k → Fin 2 ⊕ (Unit ⊕ Yᵣ) := (·.map (·.casesOn equivUnitSumUnit ↓0) id) ∘ g
    convert hS.det f' g'
    ext i j
    cases hgj : g j with
    | inl z₃ => cases z₃ with
      | inl z₂ => cases z₂ <;> simp [hgj, f', g']
      | inr => tauto
    | inr z₁ => cases z₁ <;> simp [hgj, f', g']

private lemma MatrixSum3.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮S.c₀ ◫ ▮S.c₁ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  convert (S.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ hS hSAₗ).comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ (Unit ⊕ Yᵣ)) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩⟨⟩) ↓◩◩◩⟨⟩) ↓◩◩◪⟨⟩) ↓◩◩◪⟨⟩) ↓◩◪⟨⟩) ↓◩◪⟨⟩) Sum.inr))
  aesop

private lemma MatrixSum3.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bᵣ.IsTotallyUnimodular) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮0 ◫ (▮S.c₀ ◫ ▮(-S.c₀) ◫ ▮S.c₁ ◫ ▮(-S.c₁) ◫ ▮(S.c₀ - S.c₁) ◫ ▮(S.c₁ - S.c₀) ◫ S.Aᵣ)).IsTotallyUnimodular := by
  convert ((S.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ hS hSAₗ).mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

private def MatrixSum3.transpose {Xₗ Yₗ Xᵣ Yᵣ R : Type*} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    MatrixSum3 Yᵣ Xᵣ Yₗ Xₗ R where
  Aₗ  := S.Aᵣ.transpose.submatrix Sum.swap Sum.swap
  Dₗ  := S.Dᵣ.transpose
  D₀ₗ := S.D₀ᵣ.transpose
  D₀ᵣ := S.D₀ₗ.transpose
  Dᵣ  := S.Dₗ.transpose
  Aᵣ  := S.Aₗ.transpose.submatrix Sum.swap Sum.swap

private lemma MatrixSum3.pmz_d₀_d₁_d₂_Aₗ_isTotallyUnimodular_of_Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) (hS : S.Bₗ.IsTotallyUnimodular) (hSAᵣ : S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1) :
    (▬0 ⊟ (▬S.d₀ ⊟ ▬(-S.d₀) ⊟ ▬S.d₁ ⊟ ▬(-S.d₁) ⊟ ▬(S.d₀ - S.d₁) ⊟ ▬(S.d₁ - S.d₀) ⊟ S.Aₗ)).IsTotallyUnimodular := by
  have hS' : S.transpose.Bᵣ.IsTotallyUnimodular
  · simp only [MatrixSum3.Bₗ] at hS
    simp only [MatrixSum3.Bᵣ, MatrixSum3.transpose]
    convert hS.transpose.submatrix (Sum.map Sum.swap id ∘ Sum.swap) (Sum.map Sum.swap id ∘ Sum.swap)
    ext (_|_|_) (j | _)
    · fin_cases j <;> simp
    all_goals simp
  rw [←Matrix.transpose_isTotallyUnimodular_iff]
  convert (S.transpose.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ hS' hSAᵣ).submatrix Sum.swap (Sum.map id (Sum.map id Sum.swap))
  aesop


/-! ### Properties of canonical signings of 3-sums -/

/-! All declarations in this section are private. -/

private lemma MatrixSum3.IsCanonicalSigning.Aₗ_elem {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1 := by
  rcases hS.right with hSS | hSS
  <;> exact ⟨congr_fun₂ hSS.left 2 0, congr_fun₂ hSS.left 2 1⟩

private lemma MatrixSum3.IsCanonicalSigning.Aᵣ_elem {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1 := by
  rcases hS.right with hSS | hSS
  <;> exact ⟨congr_fun₂ hSS.right 0 2, congr_fun₂ hSS.right 1 2⟩

/-- The bottom-left block of a canonical signing of a 3-sum of matrices in the first special case. -/
private lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₀ {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (hSₗ₀ : S.Sₗ = matrix3x3signed₀) :
    S.D = S.c₀ ⊗ S.d₀ - S.c₁ ⊗ S.d₁ := by
  have hSᵣ₀ : S.Sᵣ = matrix3x3signed₀
  · cases hS.right with
    | inl hSₗ => exact hSₗ.right
    | inr hSₗ =>
      exfalso
      have imposs := congr_fun₂ (hSₗ.left ▸ hSₗ₀) 1 1
      norm_num at imposs
  ext i j
  simp [MatrixSum3.D]
  cases i with
  | inl iₗ =>
    cases j
    all_goals
      have hv0 := congr_fun₂ hSᵣ₀ iₗ 0
      have hv1 := congr_fun₂ hSᵣ₀ iₗ 1
      fin_cases iₗ <;> simp_all
  | inr iᵣ =>
    cases j with
    | inl jₗ =>
      have hv00 := congr_fun₂ hSₗ₀ 0 0
      have hv01 := congr_fun₂ hSₗ₀ 0 1
      have hv10 := congr_fun₂ hSₗ₀ 1 0
      have hv11 := congr_fun₂ hSₗ₀ 1 1
      simp at hv00 hv01 hv10 hv11
      simp [Matrix.mul_apply, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two, hv00, hv01, hv10, hv11]
      ring
    | inr jᵣ =>
      have hv0 := congr_fun₂ hSₗ₀ 0 jᵣ
      have hv1 := congr_fun₂ hSₗ₀ 1 jᵣ
      fin_cases jᵣ <;> simp_all

/-- The bottom-left block of a canonical signing of a 3-sum of matrices in the second special case. -/
private lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₁ {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (hSₗ₁ : S.Sₗ = matrix3x3signed₁) :
    S.D = S.c₀ ⊗ S.d₀ - S.c₀ ⊗ S.d₁ + S.c₁ ⊗ S.d₁ := by
  have hSᵣ₀ : S.Sᵣ = matrix3x3signed₁
  · cases hS.right with
    | inl hS₀ =>
      exfalso
      have contr := congr_fun₂ (hS₀.left ▸ hSₗ₁) 1 1
      norm_num at contr
    | inr hS₁ => exact hS₁.right
  ext i j
  simp [MatrixSum3.D]
  cases i with
  | inl iₗ =>
    cases j
    all_goals
      have hv0 := congr_fun₂ hSᵣ₀ iₗ 0
      have hv1 := congr_fun₂ hSᵣ₀ iₗ 1
      fin_cases iₗ <;> simp at hv0 hv1 <;> simp [hv0, hv1]
  | inr iᵣ =>
    cases j with
    | inl jₗ =>
      have hv00 := congr_fun₂ hSₗ₁ 0 0
      have hv01 := congr_fun₂ hSₗ₁ 0 1
      have hv10 := congr_fun₂ hSₗ₁ 1 0
      have hv11 := congr_fun₂ hSₗ₁ 1 1
      simp at hv00 hv01 hv10 hv11
      simp [Matrix.mul_apply, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two, hv00, hv01, hv10, hv11]
      linarith
    | inr jᵣ =>
      have hv0 := congr_fun₂ hSₗ₁ 0 jᵣ
      have hv1 := congr_fun₂ hSₗ₁ 1 jᵣ
      fin_cases jᵣ <;> simp at hv0 hv1 <;> simp [hv0, hv1]

/-- Every col of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±c₀, ±c₁, ±c₂}`. -/
private lemma MatrixSum3.IsCanonicalSigning.D_eq_cols {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (j : Yₗ ⊕ Fin 2) :
    (S.D · j).IsParallelTo₃ S.c₀ S.c₁ (S.c₀ - S.c₁) := by
  have hj := S.aux_d₀ hS.left.left hS.Aᵣ_elem j
  rcases hS.right with ⟨hDₗ, hDᵣ⟩ | ⟨hDₗ, hDᵣ⟩
  on_goal 1 => have hD := hS.D_eq_sum_outer₀ hDₗ
  on_goal 2 => have hD := hS.D_eq_sum_outer₁ hDₗ
  all_goals
    rw [hD]
    obtain ⟨y, hy⟩ : S.d₀ j ∈ SignType.cast.range := hS.left.left.apply ◪0 ◩j
    obtain ⟨z, hz⟩ : S.d₁ j ∈ SignType.cast.range := hS.left.left.apply ◪1 ◩j
    eta_expand
    rcases y <;> rcases z
    <;> simp only [SignType.pos_eq_one, SignType.coe_one, SignType.zero_eq_zero,
      SignType.coe_zero, SignType.neg_eq_neg_one, SignType.coe_neg] at hy hz
    <;> simp [-MatrixSum3.c₀, -MatrixSum3.c₁, ←hy, ←hz, Function.IsParallelTo₃, Pi.zero_def, Pi.neg_def, sub_eq_add_neg] at hj ⊢
    repeat right
    ext
    abel

/-- Every row of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±d₀, ±d₁, ±d₂}`. -/
private lemma MatrixSum3.IsCanonicalSigning.D_eq_rows {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (i : Fin 2 ⊕ Xᵣ) :
    (S.D i).IsParallelTo₃ S.d₀ S.d₁ (S.d₀ - S.d₁) := by
  have hi := S.aux_c₀ hS.left.right hS.Aₗ_elem i
  rcases hS.right with ⟨hDₗ, hDᵣ⟩ | ⟨hDₗ, hDᵣ⟩
  on_goal 1 => have hD := hS.D_eq_sum_outer₀ hDₗ
  on_goal 2 => have hD := hS.D_eq_sum_outer₁ hDₗ
  all_goals
    rw [hD]
    obtain ⟨y, hy⟩ : S.c₀ i ∈ SignType.cast.range := hS.left.right.apply ◪i ◩0
    obtain ⟨z, hz⟩ : S.c₁ i ∈ SignType.cast.range := hS.left.right.apply ◪i ◩1
    eta_expand
    rcases y <;> rcases z
    <;> simp only [SignType.pos_eq_one, SignType.coe_one, SignType.zero_eq_zero,
      SignType.coe_zero, SignType.neg_eq_neg_one, SignType.coe_neg] at hy hz
    <;> simp [-MatrixSum3.c₀, -MatrixSum3.c₁, ←hy, ←hz, Function.IsParallelTo₃, Pi.zero_def, Pi.neg_def, sub_eq_add_neg] at hi ⊢
    repeat right
    ext
    abel

/-- The left block of a canonical signing of a 3-sum of matrices is totally unimodular. -/
private lemma MatrixSum3.IsCanonicalSigning.Aₗ_D_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (hS : S.IsCanonicalSigning) :
    (S.Aₗ ⊟ S.D).IsTotallyUnimodular := by
  classical
  let e : ((Xₗ ⊕ Unit) ⊕ Fin 2 ⊕ Xᵣ → (Unit ⊕ (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Xₗ ⊕ Unit)) :=
    (·.casesOn
      (Sum.inr ∘ Sum.inr)
      fun j : Fin 2 ⊕ Xᵣ =>
        if h0 : S.D j = 0 then ◩⟨⟩ else
        if hpc₀ : S.D j = S.d₀ then ◪◩◩◩◩◩◩⟨⟩ else
        if hmc₀ : S.D j = -S.d₀ then ◪◩◩◩◩◩◪⟨⟩ else
        if hpc₁ : S.D j = S.d₁ then ◪◩◩◩◩◪⟨⟩ else
        if hmc₁ : S.D j = -S.d₁ then ◪◩◩◩◪⟨⟩ else
        if hpc₂ : S.D j = S.d₀ - S.d₁ then ◪◩◩◪⟨⟩ else
        if hmc₂ : S.D j = S.d₁ - S.d₀ then ◪◩◪⟨⟩ else
        False.elim (have := hS.D_eq_rows j; by aesop))
  convert (S.pmz_d₀_d₁_d₂_Aₗ_isTotallyUnimodular_of_Bₗ hS.left.left hS.Aᵣ_elem).submatrix e id
  ext i j
  cases i with
  | inl => rfl
  | inr i =>
    simp only [Matrix.fromRows_apply_inr, Matrix.replicateRow_zero, Fin.isValue, Matrix.submatrix_apply, id_eq]
    wlog h0 : S.D i ≠ 0
    · rw [not_not] at h0
      simp [e, h0, congr_fun h0 j]
    wlog hpd₀ : S.D i ≠ S.d₀
    · rw [not_not] at hpd₀
      simp only [e, h0]
      simp [hpd₀, congr_fun hpd₀ j]
    wlog hmd₀ : S.D i ≠ -S.d₀
    · rw [not_not] at hmd₀
      simp only [e, h0, hpd₀]
      simp [hmd₀, congr_fun hmd₀ j]
    wlog hpd₁ : S.D i ≠ S.d₁
    · rw [not_not] at hpd₁
      simp only [e, h0, hpd₀, hmd₀]
      simp [hpd₁, congr_fun hpd₁ j]
    wlog hmd₁ : S.D i ≠ -S.d₁
    · rw [not_not] at hmd₁
      simp only [e, h0, hpd₀, hmd₀, hpd₁]
      simp [hmd₁, congr_fun hmd₁ j]
    wlog hpd₂ : S.D i ≠ S.d₀ - S.d₁
    · rw [not_not] at hpd₂
      simp only [e, h0, hpd₀, hmd₀, hpd₁, hmd₁]
      simp [hpd₂, congr_fun hpd₂ j]
    wlog hmd₂ : S.D i ≠ S.d₁ - S.d₀
    · rw [not_not] at hmd₂
      simp only [e, h0, hpd₀, hmd₀, hpd₁, hmd₁, hpd₂]
      simp [hmd₂, congr_fun hmd₂ j]
    exfalso
    have hSd := hS.D_eq_rows i
    rw [Function.IsParallelTo₃, neg_sub] at hSd
    tauto

/-- The extension of the bottom-right block of a canonical signing of a 3-sum of matrices with special columns is totally
    unimodular. -/
private lemma MatrixSum3.IsCanonicalSigning.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular :=
  S.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular_of_Bᵣ hS.left.right hS.Aₗ_elem


/-! ### Correctness -/

/-!
  In this section we prove that `MatrixSum3.HasCanonicalSigning.toCanonicalSigning` is indeed a signing of the original 3-sum.
-/

private lemma Matrix.toCanonicalSigning_apply_abs {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (Q : Matrix X Y ℚ) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₀ ℚ
        ∨ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₁ ℚ)
    (i : X) (j : Y) :
    |(Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂) i j| = |Q i j| := by
  rcases hQ with hQ | hQ
  all_goals
    have hQ00 := congr_fun₂ hQ 0 0
    have hQ02 := congr_fun₂ hQ 0 2
    have hQ12 := congr_fun₂ hQ 1 2
    have hQ20 := congr_fun₂ hQ 2 0
    have hQ21 := congr_fun₂ hQ 2 1
    simp [Matrix.abs, Matrix.toCanonicalSigning] at hQ00 hQ02 hQ12 hQ20 hQ21 ⊢
    split_ifs
  all_goals
    simp [abs_mul, hQ00, hQ02, hQ12, hQ20, hQ21]

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bₗ.IsSigningOf S.Bₗ := by
  intro i j
  rw [hS.toCanonicalSigning_Bₗ_eq]
  refine hS.left.left.choose_spec.right i j ▸ hS.left.left.choose.toCanonicalSigning_apply_abs ?_ i j
  rcases hS.right with ⟨hSS, _⟩ | ⟨hSS, _⟩ <;> [left; right]
  all_goals
    ext i j
    have hSij := hS.left.left.choose_spec.right (![◪0, ◪1, ◩◪0] i) (![◩◪0, ◩◪1, ◪0] j)
    have hSSij := congr_fun₂ hSS i j
    fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.abs] at hSij hSSij ⊢
    try rw [hSSij] at hSij
    try simp at hSij
    rw [hSij]

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bᵣ.IsSigningOf S.Bᵣ := by
  rw [hS.toCanonicalSigning_Bᵣ_eq]
  intro i j
  convert hS.left.right.choose.toCanonicalSigning_apply_abs ?_ i j
  · exact (hS.left.right.choose_spec.right i j).symm
  · rcases hS.right with ⟨_, hSS⟩ | ⟨_, hSS⟩ <;> [left; right]
    all_goals
      ext i j
      have hSij := hS.left.right.choose_spec.right (![◪◩0, ◪◩1, ◩0] i) (![◩0, ◩1, ◪◩0] j)
      have hSSij := congr_fun₂ hSS i j
      fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.abs] at hSij hSSij ⊢
      try rw [hSSij] at hSij
      try simp at hSij
      rw [hSij]

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Aₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Aₗ.IsSigningOf S.Aₗ :=
  (hS.toCanonicalSigning_Bₗ_isSigning ◩· ◩·)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Dₗ.IsSigningOf S.Dₗ :=
  (hS.toCanonicalSigning_Bₗ_isSigning ◪· ◩◩·)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ₗ.IsSigningOf S.D₀ₗ :=
  (hS.toCanonicalSigning_Bₗ_isSigning ◪· ◩◪·)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Aᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Aᵣ.IsSigningOf S.Aᵣ :=
 (hS.toCanonicalSigning_Bᵣ_isSigning ◪· ◪·)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Dᵣ.IsSigningOf S.Dᵣ :=
  (hS.toCanonicalSigning_Bᵣ_isSigning ◪◪· ◩·)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ᵣ.IsSigningOf S.D₀ᵣ :=
  (hS.toCanonicalSigning_Bᵣ_isSigning ◪◩· ◩·)

private lemma MatrixSum3.HasCanonicalSigning.summands_submatrix3x3 {Xₗ Yₗ Xᵣ Yᵣ : Type*} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2}
    (hS : S.HasCanonicalSigning) :
    |hS.left.left.choose.submatrix  ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]| = matrix3x3unsigned₀ ℚ ∧
    |hS.left.right.choose.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]| = matrix3x3unsigned₀ ℚ ∨
    |hS.left.left.choose.submatrix  ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]| = matrix3x3unsigned₁ ℚ ∧
    |hS.left.right.choose.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]| = matrix3x3unsigned₁ ℚ := by
  rcases hS.right with hSr | hSr
  <;> [left; right]
  all_goals constructor
  <;> [have heq := hSr.left; have heq := hSr.right]
  <;> [have hsgn := hS.left.left.choose_spec.right; have hsgn := hS.left.right.choose_spec.right]
  all_goals
    ext i j
    have hSij := congr_fun₂ heq i j
    fin_cases i <;> fin_cases j <;> simp at hSij <;> simp [Matrix.abs, hSij, hsgn _ _]

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_c₀_in_signTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Fin 2 ⊕ Xᵣ) :
    hS.toCanonicalSigning.c₀ iᵣ ∈ SignType.cast.range := by
  rw [MatrixSum3.c₀, in_signTypeCastRange_iff_abs]
  cases iᵣ with
  | inl i₀ =>
    rw [Matrix.fromRows_apply_inl, hS.toCanonicalSigning_D₀ᵣ_isSigning i₀ 0]
    exact (S.D₀ᵣ i₀ 0).valCast_in_signTypeCastRange
  | inr iᵣ =>
    rw [Matrix.fromRows_apply_inr, hS.toCanonicalSigning_Dᵣ_isSigning iᵣ 0]
    exact (S.Dᵣ iᵣ 0).valCast_in_signTypeCastRange

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_c₁_in_signTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Fin 2 ⊕ Xᵣ) :
    hS.toCanonicalSigning.c₁ iᵣ ∈ SignType.cast.range := by
  rw [MatrixSum3.c₁, in_signTypeCastRange_iff_abs]
  cases iᵣ with
  | inl i₀ =>
    rw [Matrix.fromRows_apply_inl, hS.toCanonicalSigning_D₀ᵣ_isSigning i₀ 1]
    exact (S.D₀ᵣ i₀ 1).valCast_in_signTypeCastRange
  | inr iᵣ =>
    rw [Matrix.fromRows_apply_inr, hS.toCanonicalSigning_Dᵣ_isSigning iᵣ 1]
    exact (S.Dᵣ iᵣ 1).valCast_in_signTypeCastRange

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_c₂_in_signTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Fin 2 ⊕ Xᵣ) :
    (hS.toCanonicalSigning.c₀ - hS.toCanonicalSigning.c₁) iᵣ ∈ SignType.cast.range := by
  rw [Pi.sub_apply]
  have hcc := hS.toCanonicalSigning.aux_c₀ hS.toCanonicalSigning_isCanonicalSigning.left.right hS.toCanonicalSigning_isCanonicalSigning.Aₗ_elem iᵣ
  obtain ⟨s₀, hs₀⟩ := hS.toCanonicalSigning_c₀_in_signTypeCastRange iᵣ
  obtain ⟨s₁, hs₁⟩ := hS.toCanonicalSigning_c₁_in_signTypeCastRange iᵣ
  cases s₀ <;> cases s₁ <;> simp [←hs₀, ←hs₁] at hcc ⊢

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dₗᵣ_in_signTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Xᵣ) (jₗ : Yₗ) :
    hS.toCanonicalSigning.D ◪iᵣ ◩jₗ ∈ SignType.cast.range := by
  rcases hS.toCanonicalSigning_isCanonicalSigning.D_eq_cols ◩jₗ with hc | hc | hc | hc | hc | hc | hc
  <;> rw [congr_fun hc ◪iᵣ]
  · exact zero_in_signTypeCastRange
  · exact hS.toCanonicalSigning_c₀_in_signTypeCastRange ◪iᵣ
  · exact neg_in_signTypeCastRange (hS.toCanonicalSigning_c₀_in_signTypeCastRange ◪iᵣ)
  · exact hS.toCanonicalSigning_c₁_in_signTypeCastRange ◪iᵣ
  · exact neg_in_signTypeCastRange (hS.toCanonicalSigning_c₁_in_signTypeCastRange ◪iᵣ)
  · exact hS.toCanonicalSigning_c₂_in_signTypeCastRange ◪iᵣ
  · exact neg_in_signTypeCastRange (hS.toCanonicalSigning_c₂_in_signTypeCastRange ◪iᵣ)

private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Xᵣ) (jₗ : Yₗ) (i₀ j₀ : Fin 2) :
    |hS.toCanonicalSigning.Dₗ i₀ jₗ * hS.toCanonicalSigning.Dᵣ iᵣ j₀| = ZMod.cast (S.Dᵣ iᵣ j₀ * S.Dₗ i₀ jₗ) := by
  rw [abs_mul, Z2_mul_cast_toRat, hS.toCanonicalSigning_Dₗ_isSigning i₀ jₗ, hS.toCanonicalSigning_Dᵣ_isSigning iᵣ j₀]
  exact Rat.mul_comm (S.Dₗ i₀ jₗ).val (S.Dᵣ iᵣ j₀).val

set_option maxHeartbeats 333333 in
private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D.IsSigningOf S.D := by
  intro i j
  cases i with
  | inl iₗ =>
    cases j with
    | inl jₗ => exact hS.toCanonicalSigning_Dₗ_isSigning iₗ jₗ
    | inr jᵣ => exact hS.toCanonicalSigning_D₀ₗ_isSigning iₗ jᵣ
  | inr iᵣ =>
    cases j with
    | inl jₗ =>
      obtain ⟨s, hs⟩ := hS.toCanonicalSigning_Dₗᵣ_in_signTypeCastRange iᵣ jₗ
      rw [←hs]
      simp [Matrix.mul_apply] at hs ⊢
      cases hS.toCanonicalSigning_isCanonicalSigning.right with
      | inl hSS =>
        obtain ⟨hSₗ', hSᵣ'⟩ := hSS
        have hD₀ₗ : S.D₀ₗ = !![1, 0; 0, 1]
        · ext i j
          have hijD₀ₗ := hS.toCanonicalSigning_D₀ₗ_isSigning i j
          have hijSₗ' := congr_fun₂ hSₗ' i j
          fin_cases i <;> fin_cases j
          <;> simp at hijD₀ₗ hijSₗ' ⊢
          <;> simp [hijSₗ'] at hijD₀ₗ
          <;> clear * - hijD₀ₗ
          · cases (S.D₀ₗ 0 0).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 0 1).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 1 0).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 1 1).eq_0_or_1 <;> simp_all
        have hD₀ₗ' : hS.toCanonicalSigning.D₀ₗ = !![1, 0; 0, -1]
        · ext i j
          have hijSₗ' := congr_fun₂ hSₗ' i j
          fin_cases i <;> fin_cases j <;> exact hijSₗ'
        rw [hD₀ₗ]
        rw [hD₀ₗ'] at hs
        rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two] at hs ⊢
        simp [inv_neg] at hs ⊢
        rw [hs]
        apply abs_add_eq_zmod_cast
        · rw [mul_comm]
          exact hS.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem iᵣ jₗ 0 0
        · rw [abs_neg, mul_comm]
          exact hS.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem iᵣ jₗ 1 1
        · exact hs ▸ Set.mem_range_self s
      | inr hSS =>
        obtain ⟨hSₗ', hSᵣ'⟩ := hSS
        have hD₀ₗ : S.D₀ₗ = !![1, 1; 0, 1]
        · ext i j
          have hijD₀ₗ := hS.toCanonicalSigning_D₀ₗ_isSigning i j
          have hijSₗ' := congr_fun₂ hSₗ' i j
          fin_cases i <;> fin_cases j
          <;> simp at hijD₀ₗ hijSₗ' ⊢
          <;> simp [hijSₗ'] at hijD₀ₗ
          <;> clear * - hijD₀ₗ
          · cases (S.D₀ₗ 0 0).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 0 1).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 1 0).eq_0_or_1 <;> simp_all
          · cases (S.D₀ₗ 1 1).eq_0_or_1 <;> simp_all
        rw [hD₀ₗ]
        have hD₀ₗ' : hS.toCanonicalSigning.D₀ₗ = !![1, 1; 0, 1]
        · ext i j
          have hij := congr_fun₂ hSₗ' i j
          fin_cases i <;> fin_cases j <;> exact hij
        rw [hD₀ₗ'] at hs
        rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two] at hs ⊢
        simp [inv_neg, add_mul, ←add_assoc] at hs ⊢
        rw [hs]
        have habc : (s.cast : ℚ) ∈ SignType.cast.range := Set.mem_range_self s
        rw [hs] at habc
        have hD00 := hS.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem iᵣ jₗ 0 0
        rw [mul_comm] at hD00
        have hD01 := hS.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem iᵣ jₗ 1 0
        rw [mul_comm, ←abs_neg] at hD01
        have hD11 := hS.toCanonicalSigning_Dₗ_elem_mul_Dᵣ_elem iᵣ jₗ 1 1
        rw [mul_comm] at hD11
        exact abs_add_add_eq_zmod_cast hD00 hD01 hD11 habc
    | inr => apply hS.toCanonicalSigning_Dᵣ_isSigning

/-- Canonical re-signing yields a signing of the original 3-sum of marices. -/
private lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.matrix.IsSigningOf S.matrix := by
  rintro (_|_) (_|_)
  · apply hS.toCanonicalSigning_Aₗ_isSigning
  · rfl
  · apply hS.toCanonicalSigning_D_isSigning
  · apply hS.toCanonicalSigning_Aᵣ_isSigning


/-! ## Family of 3-sum-like matrices -/

/-! ### Definition -/

/-- Structural data of 3-sum-like matrices. -/
structure MatrixLikeSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type*) (c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ) where
  Aₗ : Matrix Xₗ Yₗ ℚ
  D  : Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ
  Aᵣ : Matrix (Fin 2 ⊕ Xᵣ) Yᵣ ℚ
  LeftTU : (Aₗ ⊟ D).IsTotallyUnimodular
  Parallels : ∀ j : Yₗ, (D · j).IsParallelTo₃ c₀ c₁ (c₀ - c₁)
  BottomTU : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular
  AuxTU : (⊞ Aₗ 0 D.toRows₁ (▮![1, 1])).IsTotallyUnimodular
  Col₀ : c₀ ◩0 = 1 ∧ c₀ ◩1 = 0
  Col₁ : (c₁ ◩0 = 0 ∧ c₁ ◩1 = -1) ∨ (c₁ ◩0 = 1 ∧ c₁ ◩1 = 1)

/-- The resulting 3-sum-like matrix. -/
private abbrev MatrixLikeSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ (Fin 2 ⊕ Xᵣ)) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ

@[app_unexpander MatrixLikeSum3.matrix]
private def MatrixLikeSum3.matrix_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `matrix))
  | _ => throw ()


/-! ### Pivoting -/

/-- Effect on `Aₗ` after pivoting on an element in `Aₗ`. -/
private abbrev MatrixLikeSum3.shortTableauPivotAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.shortTableauPivot x y

@[app_unexpander MatrixLikeSum3.shortTableauPivotAₗ]
private def MatrixLikeSum3.shortTableauPivotAₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `shortTableauPivotAₗ))
  | _ => throw ()

/-- Equivalent expression for `Aₗ` after pivoting on an element in `Aₗ`. -/
private lemma MatrixLikeSum3.shortTableauPivotAₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotAₗ x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext
  simp

/-- Effect on `D` after pivoting on an element in `Aₗ`. -/
private abbrev MatrixLikeSum3.shortTableauPivotD {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  ((▬(M.Aₗ x) ⊟ M.D).shortTableauPivot ◩⟨⟩ y).toRows₂

@[app_unexpander MatrixLikeSum3.shortTableauPivotD]
private def MatrixLikeSum3.shortTableauPivotD_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `shortTableauPivotD))
  | _ => throw ()

/-- Equivalent expression for `D` after pivoting on an element in `Aₗ`. -/
private lemma MatrixLikeSum3.shortTableauPivotD_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotD x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext
  simp

/-- After pivoting on an element in `Aₗ`, adjoining `Aₗ` and `D` (row-wise) still gives a totally unimodular matrix. -/
private lemma MatrixLikeSum3.shortTableauPivot_leftTU {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.shortTableauPivotAₗ x y ⊟ M.shortTableauPivotD x y).IsTotallyUnimodular := by
  rw [M.shortTableauPivotD_eq x y, M.shortTableauPivotAₗ_eq x y, Matrix.fromRows_toRows]
  exact M.LeftTU.shortTableauPivot hxy

/-! Auxiliary results about multiplying columns of the left block by `0, ±1` factors . -/

private abbrev Matrix.mulCols {X Y R : Type*} [Mul R] (A : Matrix X Y R) (q : Y → R) :
    Matrix X Y R :=
  Matrix.of (fun i : X => fun j : Y => A i j * q j)

@[app_unexpander Matrix.mulCols]
private def Matrix.mulCols_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `mulCols))
  | _ => throw ()

private abbrev MatrixLikeSum3.mulColsAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.mulCols q

@[app_unexpander MatrixLikeSum3.mulColsAₗ]
private def MatrixLikeSum3.mulColsAₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `mulColsAₗ))
  | _ => throw ()

private lemma MatrixLikeSum3.mulColsAₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsAₗ q = ((M.Aₗ ⊟ M.D).mulCols q).toRows₁ := by
  ext
  simp only [Matrix.of_apply, Matrix.toRows₁_apply, Matrix.fromRows_apply_inl]

private abbrev MatrixLikeSum3.mulColsD {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  Matrix.of (fun i : Fin 2 ⊕ Xᵣ => fun j : Yₗ => M.D i j * q j)

@[app_unexpander MatrixLikeSum3.mulColsD]
private def MatrixLikeSum3.mulColsD_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `mulColsD))
  | _ => throw ()

private lemma MatrixLikeSum3.mulColsD_eq {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsD q = ((M.Aₗ ⊟ M.D).mulCols q).toRows₂ := by
  ext
  simp

private lemma MatrixLikeSum3.mulCols_leftTU {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Yₗ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (M.mulColsAₗ q ⊟ M.mulColsD q).IsTotallyUnimodular := by
  rw [M.mulColsAₗ_eq, M.mulColsD_eq, Matrix.fromRows_toRows]
  exact M.LeftTU.mul_cols hq

private lemma MatrixLikeSum3.mulCols_auxTU {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (⊞ (M.mulColsAₗ q) 0 (M.mulColsD q).toRows₁ (▮![1, 1])).IsTotallyUnimodular := by
  let q' : Yₗ ⊕ Unit → ℚ := (·.casesOn q 1)
  have hq' : ∀ j, q' j ∈ SignType.cast.range := (·.casesOn hq (by simp [q']))
  convert M.AuxTU.mul_cols hq'
  aesop

private abbrev MatrixLikeSum3.mulCols {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ := M.mulColsAₗ q
  D  := M.mulColsD q
  Aᵣ := M.Aᵣ
  LeftTU := M.mulCols_leftTU hq
  Parallels j := (M.Parallels j).mul_sign (hq j)
  BottomTU := M.BottomTU
  AuxTU := M.mulCols_auxTU hq
  Col₀ := M.Col₀
  Col₁ := M.Col₁

@[app_unexpander MatrixLikeSum3.mulCols]
private def MatrixLikeSum3.mulCols_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $M) => `($(M).$(Lean.mkIdent `mulCols))
  | _ => throw ()

set_option maxHeartbeats 333333 in
private lemma MatrixLikeSum3.isParallelTo₃ {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y j : Yₗ} (hAₗ : M.Aₗ x j / M.Aₗ x y = -1) :
    (fun i : Fin 2 ⊕ Xᵣ => M.D i j + M.D i y).IsParallelTo₃ c₀ c₁ (c₀ - c₁) := by
  cases M.Parallels y with
  | inl hu0 => simpa [congr_fun hu0] using M.Parallels j
  | inr huc =>
    cases M.Parallels j with
    | inl hv0 => simpa [congr_fun hv0] using M.Parallels y
    | inr hvc =>
      -- simplify goal by introducing notation for pivot column and non-pivot column in `D`
      set u := (M.D · y)
      set v := (M.D · j)
      rw [show (fun i : Fin 2 ⊕ Xᵣ => v i + u i) = v + u by rfl]
      -- apply TUness
      let S : Matrix (Fin 3) (Fin 3) ℚ := !![M.Aₗ x y, M.Aₗ x j, 0; u ◩0, v ◩0, 1; u ◩1, v ◩1, 1]
      have hS : S.IsTotallyUnimodular
      · convert M.AuxTU.submatrix ![◩x, ◪0, ◪1] ![◩y, ◩j, ◪0]
        symm
        apply Matrix.eta_fin_three
      have hS000 : S 0 0 ≠ 0 := ↓(by simp_all [S])
      have hS00 := hS.shortTableauPivot hS000
      have huv0 : ∃ s : SignType, s.cast = v ◩0 + u ◩0
      · simpa [hAₗ, S, ←div_mul_comm, one_mul] using hS00.apply 1 1
      have huv1 : ∃ s : SignType, s.cast = v ◩1 + u ◩1
      · simpa [hAₗ, S, ←div_mul_comm, one_mul] using hS00.apply 2 1
      have huv01 : ∃ s : SignType, s.cast = (v ◩0 + u ◩0) - (v ◩1 + u ◩1)
      · simpa [hAₗ, S, ←div_mul_comm, Matrix.det_fin_two, ←div_mul_comm, one_mul] using hS00.det ![1, 2] ![1, 2]
      clear hAₗ hS hS00 hS000
      -- go case bashing
      rcases huc with (huc | huc | huc | huc | huc | huc) <;> rcases hvc with (hvc | hvc | hvc | hvc | hvc | hvc)
      all_goals try
        rw [huc, hvc]
        unfold Function.IsParallelTo₃
        ring_nf
        simp only [true_or, or_true]
      all_goals rcases M.Col₁ with hc₁ | hc₁
      all_goals simp [huc, hvc, hc₁, M.Col₀] at huv0 huv1 huv01

/-- After pivoting on an element in `Aₗ`, columns of resulting `D` are still generated by `c₀` and `c₁`. -/
private lemma MatrixLikeSum3.shortTableauPivot_isParallelTo₃ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) (j : Yₗ) :
    ((M.shortTableauPivotD x y) · j).IsParallelTo₃ c₀ c₁ (c₀ - c₁) := by
  have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
  · obtain ⟨s, hs⟩ := M.LeftTU.apply ◩x y
    cases s <;> tauto
  if hjy : j = y then -- pivot column
    have hPC : (-M.D · y / M.Aₗ x y).IsParallelTo₃ c₀ c₁ (c₀ - c₁)
    · cases hAxy with
      | inl h1 =>
        simp only [h1, div_one]
        exact (M.Parallels y).neg
      | inr h9 =>
        simp only [h9, neg_div_neg_eq, div_one]
        exact M.Parallels y
    simpa [hjy] using hPC
  else -- non-pivot column
    obtain (h0 | h1 | h9) : M.Aₗ x j / M.Aₗ x y = 0 ∨ M.Aₗ x j / M.Aₗ x y = 1 ∨ M.Aₗ x j / M.Aₗ x y = -1
    · obtain ⟨sᵣ, hsᵣ⟩ := M.LeftTU.apply ◩x j
      cases sᵣ with
      | zero =>
        simp only [SignType.zero_eq_zero, SignType.coe_zero, Matrix.fromRows_apply_inl] at hsᵣ
        simp [←hsᵣ]
      | pos =>
        simp only [SignType.pos_eq_one, SignType.coe_one, Matrix.fromRows_apply_inl] at hsᵣ
        aesop
      | neg =>
        simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, Matrix.fromRows_apply_inl] at hsᵣ
        aesop
    · have hMDAₗ : ∀ i, M.D i y / M.Aₗ x y * M.Aₗ x j = 0 := by aesop
      have hMDj : (M.shortTableauPivotD x y · j) = (M.D · j) := by simp [hjy, hMDAₗ]
      exact hMDj ▸ M.Parallels j
    · have hMDAₗ : (M.D · y / M.Aₗ x y * M.Aₗ x j) = (M.D · y) := by simp_rw [←div_mul_comm, h1, one_mul]
      have hMDj : (M.shortTableauPivotD x y · j) = (fun i : Fin 2 ⊕ Xᵣ => M.D i j - M.D i y)
      · ext i
        simp [hjy, congr_fun hMDAₗ i]
      rw [hMDj]
      let q : Yₗ → ℚ := fun j' : Yₗ => if j' = y then -1 else 1
      have hq : ∀ j' : Yₗ, q j' ∈ SignType.cast.range
      · intro j'
        simp only [Set.mem_range, q]
        if hj' : j' = y then
          use SignType.neg
          simp [hj']
        else
          use SignType.pos
          simp [hj']
      let M' := M.mulCols hq
      let r := M'.Aₗ x j / M'.Aₗ x y
      have h9 : r = -1
      · simp [hjy, h1, r, M', q, div_neg]
      have hDj : (M.D · j) = (M'.D · j)
      · ext i
        simp [M', q, hjy]
      have hDy : (M.D · y) = -(M'.D · y)
      · ext i
        simp [M', q, hjy]
      have hM' : (fun i : Fin 2 ⊕ Xᵣ => M.D i j - M.D i y) = (fun i : Fin 2 ⊕ Xᵣ => M'.D i j + M'.D i y)
      · ext i
        simp [congr_fun hDj i, congr_fun hDy i]
      exact hM' ▸ M'.isParallelTo₃ h9
    · have hMDAₗ : (M.D · y / M.Aₗ x y * M.Aₗ x j) = (-M.D · y)
      · simp_rw [←div_mul_comm, h9, ←neg_eq_neg_one_mul]
      have hMDj : (M.shortTableauPivotD x y · j) = (fun i : Fin 2 ⊕ Xᵣ => M.D i j + M.D i y)
      · ext i
        simp [hjy, congr_fun hMDAₗ i]
      exact hMDj ▸ M.isParallelTo₃ h9

private lemma MatrixLikeSum3.shortTableauPivot_auxTU {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (⊞ (M.shortTableauPivotAₗ x y) 0 (M.shortTableauPivotD x y).toRows₁ (▮![1, 1])).IsTotallyUnimodular := by
  have hxy' : (⊞ M.Aₗ 0 M.D.toRows₁ (▮![1, 1])) ◩x ◩y ≠ 0 := hxy
  convert M.AuxTU.shortTableauPivot hxy'
  aesop

private def MatrixLikeSum3.shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ := M.shortTableauPivotAₗ x y
  D  := M.shortTableauPivotD x y
  Aᵣ := M.Aᵣ
  LeftTU := M.shortTableauPivot_leftTU hxy
  Parallels := M.shortTableauPivot_isParallelTo₃ hxy
  BottomTU := M.BottomTU
  AuxTU := M.shortTableauPivot_auxTU hxy
  Col₀ := M.Col₀
  Col₁ := M.Col₁

@[app_unexpander MatrixLikeSum3.shortTableauPivot]
private def MatrixLikeSum3.shortTableauPivot_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `shortTableauPivot))
  | _ => throw ()

/-! ### Total unimodularity -/

/-! All declarations in this section are private. -/

private lemma MatrixLikeSum3.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁) ◫ M.Aᵣ).IsTotallyUnimodular := by
  convert M.BottomTU.comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩⟨⟩) ↓◩◩◩⟨⟩) ↓◩◩◪⟨⟩) ↓◩◩◪⟨⟩) ↓◩◪⟨⟩) ↓◩◪⟨⟩) Sum.inr))
  aesop

private lemma MatrixLikeSum3.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} [DecidableEq Yᵣ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮0 ◫ (▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ M.Aᵣ)).IsTotallyUnimodular := by
  convert (M.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular.mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

/-- Adjoining `D` and `Aᵣ` gives a totally unimodular matrix. -/
private lemma MatrixLikeSum3.D_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (M.D ◫ M.Aᵣ).IsTotallyUnimodular := by
  classical
  let e : (Yₗ ⊕ Yᵣ → (Unit ⊕ (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ)) :=
    (·.casesOn
      (fun j : Yₗ =>
        if h0 : (M.D · j) = 0 then ◩⟨⟩ else
        if hpc₀ : (M.D · j) = c₀ then ◪◩◩◩◩◩◩⟨⟩ else
        if hmc₀ : (M.D · j) = -c₀ then ◪◩◩◩◩◩◪⟨⟩ else
        if hpc₁ : (M.D · j) = c₁ then ◪◩◩◩◩◪⟨⟩ else
        if hmc₁ : (M.D · j) = -c₁ then ◪◩◩◩◪⟨⟩ else
        if hpc₂ : (M.D · j) = c₀ - c₁ then ◪◩◩◪⟨⟩ else
        if hmc₂ : (M.D · j) = c₁ - c₀ then ◪◩◪⟨⟩ else
        (False.elim (by have := M.Parallels j; aesop)))
      (Sum.inr ∘ Sum.inr))
  convert M.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular.submatrix id e
  ext i j
  cases j with
  | inl jₗ =>
    simp only [Matrix.fromCols_apply_inl, Matrix.replicateCol_zero, Matrix.submatrix_apply, id_eq]
    wlog h0 : ¬(M.D · jₗ) = 0
    · rw [not_not] at h0
      simp [e, h0, congr_fun h0 i]
    wlog hpc₀ : ¬(M.D · jₗ) = c₀
    · rw [not_not] at hpc₀
      simp only [e, h0]
      simp [hpc₀, congr_fun hpc₀ i]
    wlog hmc₀ : ¬(M.D · jₗ) = -c₀
    · rw [not_not] at hmc₀
      simp only [e, h0, hpc₀]
      simp [hmc₀, congr_fun hmc₀ i]
    wlog hpc₁ : ¬(M.D · jₗ) = c₁
    · rw [not_not] at hpc₁
      simp only [e, h0, hpc₀, hmc₀]
      simp [hpc₁, congr_fun hpc₁ i]
    wlog hmc₁ : ¬(M.D · jₗ) = -c₁
    · rw [not_not] at hmc₁
      simp only [e, h0, hpc₀, hmc₀, hpc₁]
      simp [hmc₁, congr_fun hmc₁ i]
    wlog hpc₂ : ¬(M.D · jₗ) = c₀ - c₁
    · rw [not_not] at hpc₂
      simp only [e, h0, hpc₀, hmc₀, hpc₁, hmc₁]
      simp [hpc₂, congr_fun hpc₂ i]
    wlog hmc₂ : ¬(M.D · jₗ) = c₁ - c₀
    · rw [not_not] at hmc₂
      simp only [e, h0, hpc₀, hmc₀, hpc₁, hmc₁, hpc₂]
      simp [hmc₂, congr_fun hmc₂ i]
    exfalso
    have hMD := M.Parallels jₗ
    simp only [Function.IsParallelTo₃, neg_sub] at hMD
    tauto
  | inr => rfl

/-- Every 3-sum-like matrix is totally unimodular. -/
private lemma MatrixLikeSum3.isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    M.matrix.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular]
  intro k
  induction k generalizing M with
  | zero => simp [Matrix.IsPartiallyUnimodular]
  | succ n ih =>
    intro f g
    wlog hf : f.Injective
    · exact M.matrix.submatrix_det_zero_of_not_injective_rows g hf ▸ zero_in_signTypeCastRange
    wlog hg : g.Injective
    · exact M.matrix.submatrix_det_zero_of_not_injective_cols f hg ▸ zero_in_signTypeCastRange
    wlog hfₗ : ∃ iₗ : Fin (n + 1), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
    · push_neg at hfₗ
      convert M.D_Aᵣ_isTotallyUnimodular.det (fn_of_sum_ne_inl hfₗ) g using 2
      ext
      rewrite [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ]
      rfl
    obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
    wlog hgₗ : ∃ j₀ : Fin (n + 1), ∃ yₗ : Yₗ, (g j₀ = ◩yₗ ∧ M.Aₗ xₗ yₗ ≠ 0)
    · push_neg at hgₗ
      convert zero_in_signTypeCastRange
      apply ((MatrixLikeSum3.matrix M).submatrix f g).det_eq_zero_of_row_eq_zero  iₗ
      intro j
      cases hgj : g j with
      | inl => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ hgₗ j _ hgj
      | inr => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ rfl
    obtain ⟨j₀, y₀, hgj₀, hAxy0⟩ := hgₗ
    have hAxy1 : M.Aₗ xₗ y₀ = 1 ∨ M.Aₗ xₗ y₀ = -1
    · obtain ⟨s, hs⟩ := (M.LeftTU.comp_rows Sum.inl).apply xₗ y₀
      cases s with
      | zero => exact (hAxy0 hs.symm).elim
      | pos => exact Or.inl hs.symm
      | neg => exact Or.inr hs.symm
    have hMfg19 : (M.matrix.submatrix f g) iₗ j₀ = 1 ∨ (M.matrix.submatrix f g) iₗ j₀ = -1 := by
      rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
      exact hAxy1
    rw [in_signTypeCastRange_iff_abs]
    obtain ⟨f', g', hMffgg⟩ := (M.matrix.submatrix f g).abs_det_eq_shortTableauPivot_submatrix_abs_det hMfg19
    rw [hMffgg, M.matrix.submatrix_shortTableauPivot hf hg iₗ j₀, hfiₗ, hgj₀,
      Matrix.submatrix_submatrix, ←in_signTypeCastRange_iff_abs]
    convert ih (M.shortTableauPivot hAxy0) (f ∘ f') (g ∘ g')
    ext (_|_) (_|_) <;> simp [MatrixLikeSum3.shortTableauPivot]


/-! ### Implications for canonical signing of 3-sum of matrices -/

/-!
  In this section we prove that 3-sums of matrices belong to the family of 3-sum-like matrices.
-/

private lemma MatrixSum3.IsCanonicalSigning.col₀ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.c₀ ◩0 = 1 ∧ S.c₀ ◩1 = 0 := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> exact ⟨congr_fun₂ hSᵣ.right 0 0, congr_fun₂ hSᵣ.right 1 0⟩

private lemma MatrixSum3.IsCanonicalSigning.col₁ {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    (S.c₁ ◩0 = 0 ∧ S.c₁ ◩1 = -1) ∨ (S.c₁ ◩0 = 1 ∧ S.c₁ ◩1 = 1) := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> [left; right]
  <;> exact ⟨congr_fun₂ hSᵣ.right 0 1, congr_fun₂ hSᵣ.right 1 1⟩

/-- Convert a canonical signing of 3-sum of matrices to a 3-sum-like matrix. -/
private noncomputable def MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3 {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    MatrixLikeSum3 (Xₗ ⊕ Unit) (Yₗ ⊕ Fin 2) Xᵣ (Unit ⊕ Yᵣ) S.c₀ S.c₁ where
  Aₗ := S.Aₗ
  D  := S.D
  Aᵣ := S.Aᵣ
  LeftTU := hS.Aₗ_D_isTotallyUnimodular
  Parallels := hS.D_eq_cols
  BottomTU := hS.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular
  AuxTU := congr_arg (▮![1, ·]) hS.Aᵣ_elem.right ▸ hS.Aᵣ_elem.left ▸ hS.left.left
  Col₀ := hS.col₀
  Col₁ := hS.col₁

/-- The canonical signing of a 3-sum of matrices is totally unimodular. -/
private lemma MatrixSum3.IsCanonicalSigning.isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.matrix.IsTotallyUnimodular :=
  hS.toMatrixLikeSum3.isTotallyUnimodular

/-- If the reconstructed summands of a 3-sum have TU signings, then the canonical signing of the 3-sum has a TU signing. -/
private lemma MatrixSum3.HasCanonicalSigning.HasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    S.matrix.HasTuSigning :=
  ⟨hS.toCanonicalSigning.matrix, hS.toCanonicalSigning_isCanonicalSigning.isTotallyUnimodular, hS.toCanonicalSigning_isSigning⟩


/-! ## Matroid-level 3-sum -/

/-! ### Additional notation for convenience -/

/-! All declarations in this section are private. -/

private lemma And.rrrr {P₁ P₂ P₃ P₄ P₅} (hP : P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅) : P₅ :=
  hP.right.right.right.right

/-! #### Removing bundled elements from sets -/

variable {α : Type*}

/-- Remove one bundled element from a set. -/
abbrev Set.drop1 (Z : Set α) (z₀ : Z) : Set α := Z \ {z₀.val}

/-- Remove two bundled elements from a set. -/
abbrev Set.drop2 (Z : Set α) (z₀ z₁ : Z) : Set α := Z \ {z₀.val, z₁.val}

/-- Remove three bundled elements from a set. -/
abbrev Set.drop3 (Z : Set α) (z₀ z₁ z₂ : Z) : Set α := Z \ {z₀.val, z₁.val, z₂.val}

private lemma drop2_comm {Z : Set α} (z₀ z₁ : Z) : Z.drop2 z₀ z₁ = Z.drop2 z₁ z₀ := by
  unfold Set.drop2
  aesop

private lemma drop3_comm {Z : Set α} (z₀ z₁ z₂ : Z) : Z.drop3 z₀ z₁ z₂ = Z.drop3 z₁ z₀ z₂ := by
  unfold Set.drop3
  aesop

private lemma drop3_comm' {Z : Set α} (z₀ z₁ z₂ : Z) : Z.drop3 z₀ z₁ z₂ = Z.drop3 z₀ z₂ z₁ := by
  unfold Set.drop3
  aesop

private lemma drop3_ne₀ {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : i.val ≠ z₀.val := by
  have hi := i.property.right
  simp at hi
  exact hi.left

private lemma drop3_ne₁ {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : i.val ≠ z₁.val := by
  have hi := i.property.right
  simp at hi
  exact hi.right.left

private lemma drop3_ne₂ {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : i.val ≠ z₂.val := by
  have hi := i.property.right
  simp at hi
  exact hi.right.right

private lemma Set.drop3_disjoint₀₁ (Z : Set α) (z₀ z₁ z₂ : Z) : Z.drop3 z₀ z₁ z₂ ⫗ {z₀.val, z₁.val} := by
  simp_all

private lemma Set.drop3_disjoint₂ (Z : Set α) (z₀ z₁ z₂ : Z) : Z.drop3 z₀ z₁ z₂ ⫗ {z₂.val} := by
  simp_all

private lemma ni_of_in_drop3_of_inter {Z Z' : Set α} {z₀ z₁ z₂ : α} (hZZ' : Z ∩ Z' = {z₀, z₁, z₂}) {a : α}
    {hz₀ : z₀ ∈ Z'} {hz₁ : z₁ ∈ Z'} {hz₂ : z₂ ∈ Z'} (haZ' : a ∈ Z'.drop3 ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩) :
    a ∉ Z := by
  have haZZ' := congr_arg (a ∈ ·) hZZ'
  simp at haZZ'
  simp [Set.drop3] at haZ'
  tauto

private lemma drop3_union_pair {Z : Set α} {z₀ z₁ z₂ : Z} (hz₀ : z₀ ≠ z₂) (hz₁ : z₁ ≠ z₂) :
    Z.drop3 z₀ z₁ z₂ ∪ {z₀.val, z₁.val} = Z.drop1 z₂ := by
  ext a
  rw [←Subtype.coe_ne_coe] at hz₀ hz₁
  by_cases a = z₀ <;> by_cases a = z₁ <;> simp [*]

private lemma pair_union_drop3 {Z : Set α} {z₀ z₁ z₂ : Z} (hz₀ : z₀ ≠ z₂) (hz₁ : z₁ ≠ z₂) :
    {z₀.val, z₁.val} ∪ Z.drop3 z₀ z₁ z₂ = Z.drop1 z₂ := by
  rw [Set.union_comm]
  exact drop3_union_pair hz₀ hz₁

private lemma drop3_union_mem {Z : Set α} {z₀ z₁ z₂ : Z} (hz₀ : z₀ ≠ z₂) (hz₁ : z₁ ≠ z₂) :
    Z.drop3 z₀ z₁ z₂ ∪ {z₂.val} = Z.drop2 z₀ z₁ := by
  ext a
  rw [←Subtype.coe_ne_coe] at hz₀ hz₁
  have := hz₀.symm
  have := hz₁.symm
  by_cases a = z₂ <;> simp [*]

private lemma mem_union_drop3 {Z : Set α} {z₀ z₁ z₂ : Z} (hz₀ : z₀ ≠ z₂) (hz₁ : z₁ ≠ z₂) :
    {z₂.val} ∪ Z.drop3 z₀ z₁ z₂ = Z.drop2 z₀ z₁ := by
  rw [Set.union_comm]
  exact drop3_union_mem hz₀ hz₁

def undrop3 {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : Z :=
  ⟨i.val, i.property.left⟩


/-! #### Membership in drop-sets -/

/-! All declarations in this section are private. -/

private lemma Set.mem_drop1' {Z : Set α} {z₀ : Z} {v : α} (hv : v ∈ Z) (hz₀ : v ≠ z₀) :
    v ∈ Z.drop1 z₀ := by
  rw [Set.mem_diff, Set.mem_singleton_iff]
  exact ⟨hv, hz₀⟩

private lemma Set.mem_drop1 (Z : Set α) {z₀ z : Z} (hz₀ : z ≠ z₀) :
    z.val ∈ Z.drop1 z₀ :=
  Set.mem_drop1' z.property (Subtype.coe_ne_coe.← hz₀)

private lemma mem_drop1_mem_ground {Z : Set α} {z₀ : Z} {v : α} (hv : v ∈ Z.drop1 z₀) :
    v ∈ Z :=
  Set.mem_of_mem_diff hv

private lemma Set.mem_drop2 (Z : Set α) {z₀ z₁ z : Z} (hz₀ : z ≠ z₀) (hz₁ : z ≠ z₁) :
    z.val ∈ Z.drop2 z₀ z₁ := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_singleton_iff]
  exact ⟨Subtype.coe_prop z, ⟨Subtype.coe_ne_coe.← hz₀, Subtype.coe_ne_coe.← hz₁⟩⟩

private lemma mem_drop2_ne₀ {Z : Set α} {z₀ z₁ : Z} {v : α} (hv : v ∈ Z.drop2 z₀ z₁) : v ≠ z₀.val := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or] at hv
  exact hv.right.left

private lemma mem_drop2_ne₁ {Z : Set α} {z₀ z₁ : Z} {v : α} (hv : v ∈ Z.drop2 z₀ z₁) : v ≠ z₁.val := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_singleton_iff] at hv
  exact hv.right.right

private lemma mem_drop2_mem_drop1 {Z : Set α} {z₀ z₁ : Z} {v : α} (hv : v ∈ Z.drop2 z₀ z₁) :
    v ∈ Z.drop1 z₀ := by
  rw [Set.mem_diff, Set.mem_singleton_iff]
  exact ⟨Set.mem_of_mem_diff hv, mem_drop2_ne₀ hv⟩

private lemma mem_drop3_ne₀ {Z : Set α} {z₀ z₁ z₂ : Z} {v : α} (hv: v ∈ Z.drop3 z₀ z₁ z₂) : v ≠ z₀.val := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or] at hv
  exact hv.right.left

private lemma mem_drop3_ne₁ {Z : Set α} {z₀ z₁ z₂ : Z} {v : α} (hv: v ∈ Z.drop3 z₀ z₁ z₂) : v ≠ z₁.val := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_insert_iff, not_or] at hv
  exact hv.right.right.left

private lemma mem_drop3_ne₂ {Z : Set α} {z₀ z₁ z₂ : Z} {v : α} (hv: v ∈ Z.drop3 z₀ z₁ z₂) : v ≠ z₂.val := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_insert_iff, not_or, Set.mem_singleton_iff] at hv
  exact hv.right.right.right

private lemma Set.mem_drop3 (Z : Set α) {z₀ z₁ z₂ z : Z} (hz₀ : z ≠ z₀) (hz₁ : z ≠ z₁) (hz₂ : z ≠ z₂) :
    z.val ∈ Z.drop3 z₀ z₁ z₂ := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_insert_iff, not_or, Set.mem_singleton_iff]
  exact ⟨Subtype.coe_prop z, ⟨Subtype.coe_ne_coe.← hz₀, ⟨Subtype.coe_ne_coe.← hz₁, Subtype.coe_ne_coe.← hz₂⟩⟩⟩

private lemma mem_drop3_mem_drop2 {Z : Set α} {z₀ z₁ z₂ : Z} {v : α} (hv : v ∈ Z.drop3 z₀ z₁ z₂) :
    v ∈ Z.drop2 z₀ z₁ := by
  rw [Set.mem_diff, Set.mem_insert_iff, not_or, Set.mem_singleton_iff]
  exact ⟨Set.mem_of_mem_diff hv, ⟨mem_drop3_ne₀ hv, mem_drop3_ne₁ hv⟩⟩

private lemma mem_drop2_mem_drop3_or_eq₂ {Z : Set α} {z₀ z₁ z₂ : Z} {v : α}
    (hv : v ∈ Z.drop2 z₀ z₁) (hz₀ : z₀ ≠ z₂) (hz₁ : z₁ ≠ z₂) :
    v ∈ Z.drop3 z₀ z₁ z₂ ∨ v = z₂ := by
  rw [←Set.mem_singleton_iff, ←Set.mem_union, drop3_union_mem hz₀ hz₁]
  exact hv


/-! #### Re-typing elements of the triplet intersection -/

/-! All declarations in this section are private. -/

section triplets
variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

private lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ₗ]
private def Eq.mem3₀ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ₗ))
  | _ => throw ()

private lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ₗ]
private def Eq.mem3₁ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ₗ))
  | _ => throw ()

private lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

@[app_unexpander Eq.mem3₂ₗ]
private def Eq.mem3₂ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ₗ))
  | _ => throw ()

private lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ᵣ]
private def Eq.mem3₀ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ᵣ))
  | _ => throw ()

private lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ᵣ]
private def Eq.mem3₁ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ᵣ))
  | _ => throw ()

private lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

@[app_unexpander Eq.mem3₂ᵣ]
private def Eq.mem3₂ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ᵣ))
  | _ => throw ()

@[simp]
private def Eq.interAll3 (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : (Zₗ × Zₗ × Zₗ) × (Zᵣ × Zᵣ × Zᵣ) :=
  ⟨⟨⟨a₀, hZZ.mem3₀ₗ⟩, ⟨a₁, hZZ.mem3₁ₗ⟩, ⟨a₂, hZZ.mem3₂ₗ⟩⟩, ⟨⟨a₀, hZZ.mem3₀ᵣ⟩, ⟨a₁, hZZ.mem3₁ᵣ⟩, ⟨a₂, hZZ.mem3₂ᵣ⟩⟩⟩

@[app_unexpander Eq.interAll3]
private def Eq.interAll3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `interAll3))
  | _ => throw ()

end triplets


/-! ### Conversion from union form to block form and vice versa -/

def Matrix.toBlockSummandₗ {Xₗ Yₗ : Set α} {R : Type*} (Bₗ : Matrix Xₗ Yₗ R) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
    Matrix ((Xₗ.drop3 x₀ x₁ x₂ ⊕ Unit) ⊕ Fin 2) ((Yₗ.drop3 y₀ y₁ y₂ ⊕ Fin 2) ⊕ Unit) R :=
  Bₗ.submatrix (·.casesOn (·.casesOn undrop3 ↓x₂) ![x₀, x₁]) (·.casesOn (·.casesOn undrop3 ![y₀, y₁]) ↓y₂)

def Matrix.toBlockSummandᵣ {Xᵣ Yᵣ : Set α} {R : Type*} (Bᵣ : Matrix Xᵣ Yᵣ R) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
    Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ x₁ x₂)) (Fin 2 ⊕ (Unit ⊕ Yᵣ.drop3 y₀ y₁ y₂)) R :=
  Bᵣ.submatrix (·.casesOn ↓x₂ (·.casesOn ![x₀, x₁] undrop3)) (·.casesOn ![y₀, y₁] (·.casesOn ↓y₂ undrop3))

private lemma Matrix.IsSigningOf.toBlockSummandₗ {Xₗ Yₗ : Set α} {R : Type*} [LinearOrderedRing R]
    {Bₗ : Matrix Xₗ Yₗ R} {n : ℕ} {Aₗ : Matrix Xₗ Yₗ (ZMod n)}
    (hBAₗ : Bₗ.IsSigningOf Aₗ) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
    (Bₗ.toBlockSummandₗ x₀ x₁ x₂ y₀ y₁ y₂).IsSigningOf (Aₗ.toBlockSummandₗ x₀ x₁ x₂ y₀ y₁ y₂) :=
  hBAₗ.submatrix _ _

private lemma Matrix.IsSigningOf.toBlockSummandᵣ {Xᵣ Yᵣ : Set α} {R : Type*} [LinearOrderedRing R]
    {Bᵣ : Matrix Xᵣ Yᵣ R} {n : ℕ} {Aᵣ : Matrix Xᵣ Yᵣ (ZMod n)}
    (hBAᵣ : Bᵣ.IsSigningOf Aᵣ) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
    (Bᵣ.toBlockSummandᵣ x₀ x₁ x₂ y₀ y₁ y₂).IsSigningOf (Aᵣ.toBlockSummandᵣ x₀ x₁ x₂ y₀ y₁ y₂) :=
  hBAᵣ.submatrix _ _

private def equivFin1 {Z : Set α} (z : Z) : Unit ≃ Set.Elem {z.val} :=
  Equiv.ofUnique Unit (Set.Elem {z.val})

variable [DecidableEq α]

private def equivFin2 {Z : Set α} {z₀ z₁ : Z} (hzz : z₀ ≠ z₁) : Fin 2 ≃ Set.Elem {z₀.val, z₁.val} :=
⟨
  ![⟨z₀.val, Set.mem_insert z₀.val {z₁.val}⟩, ⟨z₁.val, Set.mem_insert_of_mem z₀.val rfl⟩],
  (if ·.val = z₀.val then 0 else 1),
  (if h0 : · = 0 then by simp [h0] else have := fin2_eq_1_of_ne_0 h0; by aesop),
  ↓(by aesop)
⟩

private def equiv₃X {Xₗ Xᵣ : Set α} [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Xᵣ)] {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ}
    (hx₀ₗ : x₁ₗ ≠ x₂ₗ) (hx₁ₗ : x₀ₗ ≠ x₂ₗ) (hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ) (hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ) (hx₂ᵣ : x₀ᵣ ≠ x₁ᵣ) :
    (Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) ≃ (Xₗ.drop2 x₀ₗ x₁ₗ).Elem ⊕ (Xᵣ.drop1 x₂ᵣ).Elem :=
  Equiv.sumCongr
    (((equivFin1 x₂ₗ).rightCongr.trans (Xₗ.drop3_disjoint₂ x₀ₗ x₁ₗ x₂ₗ).equivSumUnion).trans
      (drop3_union_mem hx₁ₗ hx₀ₗ).≃)
    (((equivFin2 hx₂ᵣ).leftCongr.trans (Xᵣ.drop3_disjoint₀₁ x₀ᵣ x₁ᵣ x₂ᵣ).symm.equivSumUnion).trans
      (pair_union_drop3 hx₁ᵣ hx₀ᵣ).≃)

private def equiv₃Y {Yₗ Yᵣ : Set α} [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Yᵣ)] {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (hy₀ₗ : y₁ₗ ≠ y₂ₗ) (hy₁ₗ : y₀ₗ ≠ y₂ₗ) (hy₂ₗ : y₀ₗ ≠ y₁ₗ) (hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ) (hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ) :
    (Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) ≃ (Yₗ.drop1 y₂ₗ).Elem ⊕ (Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem :=
  Equiv.sumCongr
    (((equivFin2 hy₂ₗ).rightCongr.trans (Yₗ.drop3_disjoint₀₁ y₀ₗ y₁ₗ y₂ₗ).equivSumUnion).trans
      (drop3_union_pair hy₁ₗ hy₀ₗ).≃)
    (((equivFin1 y₂ᵣ).leftCongr.trans ((Yᵣ.drop3_disjoint₂ y₀ᵣ y₁ᵣ y₂ᵣ).symm).equivSumUnion).trans
      (mem_union_drop3 hy₁ᵣ hy₀ᵣ).≃)

private def Matrix.toIntermediate {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type*}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A : Matrix
      ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
      ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
      R)
    (hx₀ₗ : x₁ₗ ≠ x₂ₗ) (hx₁ₗ : x₀ₗ ≠ x₂ₗ) (hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ) (hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ) (hx₂ᵣ : x₀ᵣ ≠ x₁ᵣ)
    (hy₀ₗ : y₁ₗ ≠ y₂ₗ) (hy₁ₗ : y₀ₗ ≠ y₂ₗ) (hy₂ₗ : y₀ₗ ≠ y₁ₗ) (hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ) (hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ) :
    Matrix ((Xₗ.drop2 x₀ₗ x₁ₗ).Elem ⊕ (Xᵣ.drop1 x₂ᵣ).Elem) ((Yₗ.drop1 y₂ₗ).Elem ⊕ (Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem) R :=
  A.reindex
    (equiv₃X hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ)
    (equiv₃Y hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ)

@[app_unexpander Matrix.toIntermediate]
private def Matrix.toIntermediate_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `toIntermediate))
  | _ => throw ()

private def Matrix.toMatrixDropUnionDropInternal {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type*}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A : Matrix
      ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
      ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
      R)
    (hx₀ₗ : x₁ₗ ≠ x₂ₗ) (hx₁ₗ : x₀ₗ ≠ x₂ₗ) (hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ) (hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ) (hx₂ᵣ : x₀ᵣ ≠ x₁ᵣ)
    (hy₀ₗ : y₁ₗ ≠ y₂ₗ) (hy₁ₗ : y₀ₗ ≠ y₂ₗ) (hy₂ₗ : y₀ₗ ≠ y₁ₗ) (hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ) (hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem R :=
  (A.toIntermediate hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ).toMatrixUnionUnion

@[app_unexpander Matrix.toMatrixDropUnionDropInternal]
private def Matrix.toMatrixDropUnionDropInternal_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `toMatrixDropUnionDropInternal))
  | _ => throw ()

@[simp]
def Matrix.toMatrixDropUnionDrop {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type*}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A : Matrix
      ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
      ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
      R) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem R :=
  A.submatrix
    (fun i : (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem =>
      if hi₂ₗ : i.val = x₂ₗ then ◩◪0 else
      if hiXₗ : i.val ∈ Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ then ◩◩⟨i, hiXₗ⟩ else
      if hi₀ᵣ : i.val = x₀ᵣ then ◪◩0 else
      if hi₁ᵣ : i.val = x₁ᵣ then ◪◩1 else
      if hiXᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then ◪◪⟨i, hiXᵣ⟩ else
      False.elim (i.property.elim ↓(by simp_all) ↓(by simp_all)))
    (fun j : (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem =>
      if hj₀ₗ : j.val = y₀ₗ then ◩◪0 else
      if hj₁ₗ : j.val = y₁ₗ then ◩◪1 else
      if hjYₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then ◩◩⟨j, hjYₗ⟩ else
      if hj₂ᵣ : j.val = y₂ᵣ then ◪◩0 else
      if hjYᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then ◪◪⟨j, hjYᵣ⟩ else
      False.elim (j.property.elim ↓(by simp_all) ↓(by simp_all)))

private lemma Matrix.toMatrixDropUnionDrop_eq_toMatrixDropUnionDropInternal {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type*}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (hx₀ₗ : x₁ₗ ≠ x₂ₗ) (hx₁ₗ : x₀ₗ ≠ x₂ₗ) (hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ) (hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ) (hx₂ᵣ : x₀ᵣ ≠ x₁ᵣ)
    (hy₀ₗ : y₁ₗ ≠ y₂ₗ) (hy₁ₗ : y₀ₗ ≠ y₂ₗ) (hy₂ₗ : y₀ₗ ≠ y₁ₗ) (hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ) (hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ)
    (A : Matrix
      ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
      ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
      R) :
    A.toMatrixDropUnionDrop = A.toMatrixDropUnionDropInternal hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ := by
  apply congr_arg₂
  · ext i
    unfold equiv₃X
    if hi₂ₗ : i.val = x₂ₗ then
      have hx₂ₗXₗ := Xₗ.mem_drop2 hx₁ₗ.symm hx₀ₗ.symm
      have hi : i.toSum = ◩⟨x₂ₗ.val, hx₂ₗXₗ⟩
      · simp [hi₂ₗ, hx₂ₗXₗ]
      simp_rw [hi₂ₗ, hi]
      simp
    else if hiXₗ : i.val ∈ Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ then
      have hiXₗ' := mem_drop3_mem_drop2 hiXₗ
      have hi : i.toSum = ◩⟨i.val, hiXₗ'⟩
      · simp [hiXₗ']
      simp_rw [hi₂ₗ, hiXₗ, hi]
      simp [hiXₗ]
    else if hi₀ᵣ : i.val = x₀ᵣ then
      have hx₀ᵣXₗ : x₀ᵣ.val ∉ Xₗ.drop2 x₀ₗ x₁ₗ
      · intro contr
        rw [←drop3_union_mem hx₁ₗ hx₀ₗ, Set.union_singleton, ←hi₀ᵣ] at contr
        exact contr.elim (hi₂ₗ ·) (hiXₗ ·)
      have hx₀ᵣXᵣ : x₀ᵣ.val ∈ Xᵣ.drop1 x₂ᵣ := Xᵣ.mem_drop1 hx₁ᵣ
      have hi : i.toSum = ◪⟨x₀ᵣ.val, hx₀ᵣXᵣ⟩
      · simp [hi₀ᵣ, hx₀ᵣXₗ, hx₀ᵣXᵣ]
      simp_rw [hi₂ₗ, hiXₗ, hi₀ᵣ, hi]
      simp [equivFin2]
    else if hi₁ᵣ : i.val = x₁ᵣ then
      have hx₁ᵣXₗ : x₁ᵣ.val ∉ Xₗ.drop2 x₀ₗ x₁ₗ
      · intro contr
        rw [←drop3_union_mem hx₁ₗ hx₀ₗ, Set.union_singleton, ←hi₁ᵣ] at contr
        exact contr.elim (hi₂ₗ ·) (hiXₗ ·)
      have hx₁ᵣXᵣ : x₁ᵣ.val ∈ Xᵣ.drop1 x₂ᵣ := Xᵣ.mem_drop1 hx₀ᵣ
      have hi : i.toSum = ◪⟨x₁ᵣ.val, hx₁ᵣXᵣ⟩
      · simp [hi₁ᵣ, hx₁ᵣXₗ, hx₁ᵣXᵣ]
      simp_rw [hi₂ₗ, hiXₗ, hi₀ᵣ, hi₁ᵣ, hi]
      simp [equivFin2, Subtype.coe_ne_coe.← hx₂ᵣ.symm]
    else if hiXᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then
      have hiXₗ' : i.val ∉ Xₗ.drop2 x₀ₗ x₁ₗ
      · intro contr
        simp_rw [←drop3_union_mem hx₁ₗ hx₀ₗ, Set.union_singleton] at contr
        exact contr.elim (hi₂ₗ ·) (hiXₗ ·)
      have hiXᵣ' := mem_drop3_mem_drop2 (drop3_comm' x₀ᵣ x₁ᵣ x₂ᵣ ▸ hiXᵣ)
      have hiXᵣ'' := mem_drop2_mem_drop1 (drop2_comm x₀ᵣ x₂ᵣ ▸ hiXᵣ')
      have hi : i.toSum = ◪⟨i.val, hiXᵣ''⟩
      · simp [hiXₗ', hiXᵣ'']
      simp_rw [hi₂ₗ, hiXₗ, hi₀ᵣ, hi₁ᵣ, hiXᵣ, hi]
      simp [hi₀ᵣ, hi₁ᵣ, hiXᵣ]
    else
      exfalso
      exact i.property.elim ↓(by simp_all) ↓(by simp_all)
  · ext j
    unfold equiv₃Y
    if hj₀ₗ : j.val = y₀ₗ then
      have hy₀ₗYₗ : y₀ₗ.val ∈ Yₗ.drop1 y₂ₗ := Yₗ.mem_drop1 hy₁ₗ
      have hj : j.toSum = ◩⟨y₀ₗ.val, hy₀ₗYₗ⟩
      · simp [hj₀ₗ, hy₀ₗYₗ]
      simp_rw [hj₀ₗ, hj]
      simp [equivFin2]
    else if hj₁ₗ : j.val = y₁ₗ then
      have hy₁ₗYₗ : y₁ₗ.val ∈ Yₗ.drop1 y₂ₗ := Yₗ.mem_drop1 hy₀ₗ
      have hj : j.toSum = ◩⟨y₁ₗ.val, hy₁ₗYₗ⟩
      · simp [hj₁ₗ, hy₁ₗYₗ]
      simp_rw [hj₀ₗ, hj₁ₗ, hj]
      simp [equivFin2, Subtype.coe_ne_coe.← hy₂ₗ.symm]
    else if hjYₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then
      have hjYₗ' := mem_drop3_mem_drop2 (drop3_comm' y₀ₗ y₁ₗ y₂ₗ ▸ hjYₗ)
      have hjYₗ'' := mem_drop2_mem_drop1 (drop2_comm y₀ₗ y₂ₗ ▸ hjYₗ')
      have hj : j.toSum = ◩⟨j.val, hjYₗ''⟩
      · simp [hjYₗ'']
      simp_rw [hj₀ₗ, hj₁ₗ, hjYₗ, hj]
      simp [equivFin2, hjYₗ]
    else if hj₂ᵣ : j.val = y₂ᵣ then
      have hy₂ᵣYₗ : y₂ᵣ.val ∉ Yₗ.drop1 y₂ₗ
      · intro contr
        rw [←drop3_union_pair hy₁ₗ hy₀ₗ, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, ←hj₂ᵣ] at contr
        exact contr.elim (hjYₗ ·) (·.elim (hj₀ₗ ·) (hj₁ₗ ·))
      have hy₂ᵣYᵣ : y₂ᵣ.val ∈ Yᵣ.drop2 y₀ᵣ y₁ᵣ := Yᵣ.mem_drop2 hy₁ᵣ.symm hy₀ᵣ.symm
      have hj : j.toSum = ◪⟨y₂ᵣ.val, hy₂ᵣYᵣ⟩
      · simp [hj₂ᵣ, hy₂ᵣYₗ, hy₂ᵣYᵣ]
      simp_rw [hj₀ₗ, hj₁ₗ, hjYₗ, hj₂ᵣ, hj]
      simp [Disjoint.equivSumUnion]
    else if hjYᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then
      have hjYₗ' : j.val ∉ Yₗ.drop1 y₂ₗ
      · intro contr
        simp_rw [←drop3_union_pair hy₁ₗ hy₀ₗ, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at contr
        exact contr.elim (hjYₗ ·) (·.elim (hj₀ₗ ·) (hj₁ₗ ·))
      have hjYᵣ' : j.val ∈ Yᵣ.drop2 y₀ᵣ y₁ᵣ := mem_drop3_mem_drop2 hjYᵣ
      have hj : j.toSum = ◪⟨j.val, hjYᵣ'⟩
      · simp [hjYₗ', hjYᵣ']
      simp_rw [hj₀ₗ, hj₁ₗ, hjYₗ, hj₂ᵣ, hjYᵣ, hj]
      simp [Disjoint.equivSumUnion, hj₂ᵣ, hjYᵣ]
    else
      exfalso
      exact j.property.elim ↓(by simp_all) ↓(by simp_all)


/-! ### The 3-sum of standard representations -/

/-- `StandardRepr`-level 3-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum3 {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  -- Elements of the intersection as elements of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.interAll3
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.interAll3
  -- Construction
  open scoped Classical in if
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ Sₗ.B.submatrix ![x₀ₗ, x₁ₗ] ![y₀ₗ, y₁ₗ] = Sᵣ.B.submatrix ![x₀ᵣ, x₁ᵣ] ![y₀ᵣ, y₁ᵣ]
    -- `D₀` is invertible
    ∧ IsUnit (Sₗ.B.submatrix ![x₀ₗ, x₁ₗ] ![y₀ₗ, y₁ₗ])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Sₗ.B x₀ₗ y₂ₗ = 1
    ∧ Sₗ.B x₁ₗ y₂ₗ = 1
    ∧ Sₗ.B x₂ₗ y₀ₗ = 1
    ∧ Sₗ.B x₂ₗ y₁ₗ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ y₂ₗ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Sᵣ.B x₀ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₁ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₀ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₁ᵣ = 1
    ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B x₂ᵣ ⟨y, hy⟩ = 0)
  then
    some ⟨
      -- row indices
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      -- col indices
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      -- row and col indices are disjoint
      union_disjoint_union
        Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right
        Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right
        hXY.disjoint_sdiff_left.disjoint_sdiff_right
        hYX.disjoint_sdiff_left.disjoint_sdiff_right,
      -- standard representation matrix
      (blocksToMatrixSum3
          (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ)
          (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)
        ).matrix.toMatrixDropUnionDrop,
      -- decidability of row indices
      inferInstance,
      -- decidability of col indices
      inferInstance⟩
  else
    none

private lemma standardReprSum3_X_xxx {Sₗ Sᵣ S : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum3 hXX hYY hXY hYX = some S) :
    S.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x₂}) := by
  simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm

lemma standardReprSum3_X_eq {Sₗ Sᵣ S : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum3 hXX hYY hXY hYX = some S) :
    S.X = Sₗ.X ∪ Sᵣ.X := by
  have hx₀ : x₁ ≠ x₂
  · simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact hS.left.left.left.right.right
  have hx₁ : x₀ ≠ x₂
  · simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact hS.left.left.left.right.left
  rw [standardReprSum3_X_xxx hS]
  ext a
  if hax₂ : a = x₂ then
    simp [*, hXX.mem3₂ₗ, hx₀.symm, hx₁.symm]
  else if hax₀ : a = x₀ then
    simp [*, hXX.mem3₀ᵣ]
  else if hax₁ : a = x₁ then
    simp [*, hXX.mem3₁ᵣ]
  else
    simp [*]

private lemma standardReprSum3_Y_yyy {Sₗ Sᵣ S : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum3 hXX hYY hXY hYX = some S) :
    S.Y = (Sₗ.Y \ {y₂}) ∪ (Sᵣ.Y \ {y₀, y₁}) := by
  simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm

lemma standardReprSum3_Y_eq {Sₗ Sᵣ S : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum3 hXX hYY hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ Sᵣ.Y := by
  have hy₀ : y₁ ≠ y₂
  · simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact hS.left.left.right.right.right
  have hy₁ : y₀ ≠ y₂
  · simp_rw [standardReprSum3, Option.ite_none_right_eq_some, Option.some.injEq] at hS
    exact hS.left.left.right.right.left
  rw [standardReprSum3_Y_yyy hS]
  ext a
  if hay₂ : a = y₂ then
    simp [*, hYY.mem3₂ᵣ, hy₀.symm, hy₁.symm]
  else if hax₀ : a = y₀ then
    simp [*, hYY.mem3₀ₗ]
  else if hax₁ : a = y₁ then
    simp [*, hYY.mem3₁ₗ]
  else
    simp [*]

private lemma HEq.standardRepr_matrix_apply {R : Type*} {S₁ : StandardRepr α R} {X₂ Y₂ : Set α} {B₂ : Matrix X₂ Y₂ R}
    (hSB : HEq S₁.B B₂) (i : S₁.X) (j : S₁.Y) (hXX : S₁.X = X₂) (hYY : S₁.Y = Y₂) :
    S₁.B i j = B₂ (hXX ▸ i) (hYY ▸ j) := by
  obtain ⟨X₁, Y₁, B₁⟩ := S₁
  dsimp only at hXX hYY hSB ⊢
  subst hXX hYY
  rw [heq_eq_eq] at hSB
  exact congr_fun₂ hSB i j

private abbrev matrixSum3aux (Sₗ Sᵣ : StandardRepr α Z2)
    (x₀ₗ x₁ₗ x₂ₗ : Sₗ.X) (y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y) (x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X) (y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y) :
    MatrixSum3 (Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ) (Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) Z2 :=
  blocksToMatrixSum3 (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)

set_option maxHeartbeats 3000000 in
lemma standardReprSum3_hasTuSigning {Sₗ Sᵣ S : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) (hS : standardReprSum3 hXX hYY hXY hYX = some S) :
    S.B.HasTuSigning := by
  -- row membership
  let x₀ₗ : Sₗ.X := ⟨x₀, hXX.mem3₀ₗ⟩
  let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.mem3₀ᵣ⟩
  let x₁ₗ : Sₗ.X := ⟨x₁, hXX.mem3₁ₗ⟩
  let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.mem3₁ᵣ⟩
  let x₂ₗ : Sₗ.X := ⟨x₂, hXX.mem3₂ₗ⟩
  let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.mem3₂ᵣ⟩
  -- col membership
  let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.mem3₀ₗ⟩
  let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.mem3₀ᵣ⟩
  let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.mem3₁ₗ⟩
  let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.mem3₁ᵣ⟩
  let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.mem3₂ₗ⟩
  let y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.mem3₂ᵣ⟩
  -- signings of summands
  obtain ⟨Bₗ, hBₗ, hSBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hSBᵣ⟩ := hSᵣ
  -- massaging the assumption
  have hXxxx := standardReprSum3_X_xxx hS
  have hYyyy := standardReprSum3_Y_yyy hS
  simp only [standardReprSum3, Option.ite_none_right_eq_some] at hS
  obtain ⟨hSS, hS'⟩ := hS
  rw [Option.some.injEq, Eq.comm] at hS'
  -- elements are distinct
  have hx₀ : x₁ ≠ x₂
  · tauto
  have hx₁ : x₀ ≠ x₂
  · tauto
  have hx₂ : x₀ ≠ x₁
  · tauto
  have hy₀ : y₁ ≠ y₂
  · tauto
  have hy₁ : y₀ ≠ y₂
  · tauto
  have hy₂ : y₀ ≠ y₁
  · tauto
  have hx₀ₗ : x₁ₗ ≠ x₂ₗ
  · simpa [x₁ₗ, x₂ₗ] using hx₀
  have hx₁ₗ : x₀ₗ ≠ x₂ₗ
  · simpa [x₀ₗ, x₂ₗ] using hx₁
  have hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ
  · simpa [x₁ᵣ, x₂ᵣ] using hx₀
  have hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ
  · simpa [x₀ᵣ, x₂ᵣ] using hx₁
  have hx₂ᵣ : x₀ᵣ ≠ x₁ᵣ
  · simpa [x₀ᵣ, x₁ᵣ] using hx₂
  have hy₀ₗ : y₁ₗ ≠ y₂ₗ
  · simpa [y₁ₗ, y₂ₗ] using hy₀
  have hy₁ₗ : y₀ₗ ≠ y₂ₗ
  · simpa [y₀ₗ, y₂ₗ] using hy₁
  have hy₂ₗ : y₀ₗ ≠ y₁ₗ
  · simpa [y₀ₗ, y₁ₗ] using hy₂
  have hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ
  · simpa [y₁ᵣ, y₂ᵣ] using hy₀
  have hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ
  · simpa [y₀ᵣ, y₂ᵣ] using hy₁
  -- two options what `D₀` is (up to reindexing)
  obtain ⟨f, g, hfg⟩ := !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ].isUnit_2x2 (by
    convert hSS.right.right.left
    exact (Matrix.eta_fin_two (Sₗ.B.submatrix ![x₀ₗ, x₁ₗ] ![y₀ₗ, y₁ₗ])).symm)
  -- cases analysis over those reindexings
  if hf : f = fin2refl then
    if hg : g = fin2refl then
      simp [hf, hg] at hfg
      clear hg hf g f
      let M := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
      have hM : M.HasCanonicalSigning
      · constructor
        · constructor
          · use Bₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ, hBₗ.submatrix _ _
            convert hSBₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
            conv_rhs => rw [←(Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bₗ, blocksToMatrixSum3, Matrix.fromCols_toCols, Matrix.fromBlocks_inj, true_and]
            constructor
            · ext i j
              fin_cases j
              simp [Matrix.toBlockSummandₗ, Matrix.toBlocks₁₂]
              cases i with
              | inl x => exact (hSS.rrrr.right.right.right.left x.val x.property.left ⟨drop3_ne₀ x, drop3_ne₁ x⟩).symm
              | inr => exact (hSS.rrrr.right.right.right.left x₂ hXX.mem3₂ₗ (by tauto)).symm
            · ext i j
              have : Sₗ.B x₀ₗ y₂ₗ = Sᵣ.B x₀ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₀ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₀ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₁ₗ y₂ₗ = Sᵣ.B x₁ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₁ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₁ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases j
              fin_cases i <;> tauto
          · use Bᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ, hBᵣ.submatrix _ _
            convert hSBᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
            conv_rhs => rw [←(Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bᵣ, blocksToMatrixSum3, Matrix.fromRows_toRows, Matrix.fromBlocks_inj, and_true]
            constructor
            · ext i j
              have : Sₗ.B x₂ₗ y₀ₗ = Sᵣ.B x₂ᵣ y₀ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₀ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₀ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₂ₗ y₁ₗ = Sᵣ.B x₂ᵣ y₁ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₁ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₁ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases i
              fin_cases j <;> tauto
            · ext i j
              fin_cases i
              simp [Matrix.toBlockSummandᵣ, Matrix.toBlocks₁₂]
              cases j with
              | inl => exact (hSS.rrrr.rrrr.rrrr y₂ hYY.mem3₂ᵣ (by tauto)).symm
              | inr y => exact (hSS.rrrr.rrrr.rrrr y.val y.property.left ⟨drop3_ne₀ y, drop3_ne₁ y⟩).symm
        · cases hfg with
          | inl h1001 =>
            left
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1001 0 0
              · exact congr_fun₂ h1001 0 1
              · exact hSS.rrrr.rrrr.left
              · exact congr_fun₂ h1001 1 0
              · exact congr_fun₂ h1001 1 1
              · exact hSS.rrrr.rrrr.right.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1001 0 0
                have h00' := congr_fun₂ hSS.right.left.symm 0 0
                simp at h00 h00'
                rwa [←h00'] at h00
              · have h01 := congr_fun₂ h1001 0 1
                have h01' := congr_fun₂ hSS.right.left.symm 0 1
                simp at h01 h01'
                rwa [←h01'] at h01
              · tauto
              · have h10 := congr_fun₂ h1001 1 0
                have h10' := congr_fun₂ hSS.right.left.symm 1 0
                simp at h10 h10'
                rwa [←h10'] at h10
              · have h11 := congr_fun₂ h1001 1 1
                have h11' := congr_fun₂ hSS.right.left.symm 1 1
                simp at h11 h11'
                rwa [←h11'] at h11
              · tauto
              · exact hSS.rrrr.right.left
              · exact hSS.rrrr.right.right.left
              · rfl
          | inr h1101 =>
            right
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1101 0 0
              · exact congr_fun₂ h1101 0 1
              · exact hSS.rrrr.rrrr.left
              · exact congr_fun₂ h1101 1 0
              · exact congr_fun₂ h1101 1 1
              · exact hSS.rrrr.rrrr.right.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1101 0 0
                have h00' := congr_fun₂ hSS.right.left.symm 0 0
                simp at h00 h00'
                rwa [←h00'] at h00
              · have h01 := congr_fun₂ h1101 0 1
                have h01' := congr_fun₂ hSS.right.left.symm 0 1
                simp at h01 h01'
                rwa [←h01'] at h01
              · tauto
              · have h10 := congr_fun₂ h1101 1 0
                have h10' := congr_fun₂ hSS.right.left.symm 1 0
                simp at h10 h10'
                rwa [←h10'] at h10
              · have h11 := congr_fun₂ h1101 1 1
                have h11' := congr_fun₂ hSS.right.left.symm 1 1
                simp at h11 h11'
                rwa [←h11'] at h11
              · tauto
              · exact hSS.rrrr.right.left
              · exact hSS.rrrr.right.right.left
              · rfl
      obtain ⟨B, hB, hBM⟩ := hM.HasTuSigning
      use (B.toIntermediate hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ).toMatrixElemElem hXxxx hYyyy
      constructor
      · apply Matrix.IsTotallyUnimodular.toMatrixElemElem
        apply hB.submatrix
      · rw [Matrix.toMatrixDropUnionDrop_eq_toMatrixDropUnionDropInternal hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ] at hS'
        exact hS' ▸ (hBM.reindex (equiv₃X hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ) (equiv₃Y hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ)).toMatrixElemElem hXxxx hYyyy
    else
      have hg' : g = fin2swap := eq_fin2swap_of_ne_fin2refl hg
      simp [hf, hg'] at hfg
      clear hg' hg hf g f
      let M := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
      have hM : M.HasCanonicalSigning
      · constructor
        · constructor
          · use Bₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ, hBₗ.submatrix _ _
            convert hSBₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ
            conv_rhs => rw [←(Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bₗ, blocksToMatrixSum3, Matrix.fromCols_toCols, Matrix.fromBlocks_inj, true_and]
            constructor
            · ext i j
              fin_cases j
              simp [Matrix.toBlockSummandₗ, Matrix.toBlocks₁₂]
              cases i with
              | inl x => exact (hSS.rrrr.right.right.right.left x.val x.property.left ⟨drop3_ne₀ x, drop3_ne₁ x⟩).symm
              | inr => exact (hSS.rrrr.right.right.right.left x₂ hXX.mem3₂ₗ (by tauto)).symm
            · ext i j
              have : Sₗ.B x₀ₗ y₂ₗ = Sᵣ.B x₀ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₀ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₀ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₁ₗ y₂ₗ = Sᵣ.B x₁ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₁ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₁ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases j
              fin_cases i <;> tauto
          · use Bᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ, hBᵣ.submatrix _ _
            convert hSBᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
            conv_rhs => rw [←(Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bᵣ, blocksToMatrixSum3, Matrix.fromRows_toRows, Matrix.fromBlocks_inj, and_true]
            constructor
            · ext i j
              have : Sₗ.B x₂ₗ y₀ₗ = Sᵣ.B x₂ᵣ y₀ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₀ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₀ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₂ₗ y₁ₗ = Sᵣ.B x₂ᵣ y₁ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₁ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₁ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases i
              fin_cases j <;> tauto
            · ext i j
              fin_cases i
              simp [Matrix.toBlockSummandᵣ, Matrix.toBlocks₁₂]
              cases j with
              | inl => exact (hSS.rrrr.rrrr.rrrr y₂ hYY.mem3₂ᵣ (by tauto)).symm
              | inr y => exact (hSS.rrrr.rrrr.rrrr y.val y.property.left ⟨drop3_ne₁ y, drop3_ne₀ y⟩).symm
        · cases hfg with
          | inl h1001 =>
            left
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1001 0 0
              · exact congr_fun₂ h1001 0 1
              · exact hSS.rrrr.rrrr.left
              · exact congr_fun₂ h1001 1 0
              · exact congr_fun₂ h1001 1 1
              · exact hSS.rrrr.rrrr.right.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1001 0 0
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h00 h01
                rwa [←h01] at h00
              · have h01 := congr_fun₂ h1001 0 1
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h01 h00
                rwa [←h00] at h01
              · tauto
              · have h10 := congr_fun₂ h1001 1 0
                have h00 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h10 h00
                rwa [←h00] at h10
              · have h11 := congr_fun₂ h1001 1 1
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h11 h10
                rwa [←h10] at h11
              · tauto
              · exact hSS.rrrr.right.right.left
              · exact hSS.rrrr.right.left
              · rfl
          | inr h1101 =>
            right
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1101 0 0
              · exact congr_fun₂ h1101 0 1
              · exact hSS.rrrr.rrrr.left
              · exact congr_fun₂ h1101 1 0
              · exact congr_fun₂ h1101 1 1
              · exact hSS.rrrr.rrrr.right.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1101 0 0
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h00 h01
                rwa [←h01] at h00
              · have h01 := congr_fun₂ h1101 0 1
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h01 h00
                rwa [←h00] at h01
              · tauto
              · have h10 := congr_fun₂ h1101 1 0
                have h11 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h10 h11
                rwa [←h11] at h10
              · have h11 := congr_fun₂ h1101 1 1
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h11 h10
                rwa [←h10] at h11
              · tauto
              · exact hSS.rrrr.right.right.left
              · exact hSS.rrrr.right.left
              · rfl
      obtain ⟨B, hB, hBM⟩ := hM.HasTuSigning
      have hX₀₁ : Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ = Sₗ.X.drop2 x₁ₗ x₀ₗ ∪ Sᵣ.X.drop1 x₂ᵣ
      · rw [drop2_comm x₀ₗ x₁ₗ]
      have hY₀₁ : Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ = Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ
      · rw [drop2_comm y₀ᵣ y₁ᵣ]
      rw [hY₀₁] at hYyyy
      use (B.toIntermediate hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ).toMatrixElemElem hXxxx hYyyy
      constructor
      · apply Matrix.IsTotallyUnimodular.toMatrixElemElem
        apply hB.submatrix
      · rw [Matrix.toMatrixDropUnionDrop_eq_toMatrixDropUnionDropInternal hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ] at hS'
        convert (hBM.reindex (equiv₃X hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ) (equiv₃Y hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ)).toMatrixElemElem hXxxx hYyyy
        simp only [Eq.interAll3, Matrix.toMatrixDropUnionDropInternal, Matrix.toIntermediate] at hS'
        simp only [M, Matrix.reindex_apply]
        have hSB := congr_arg_heq StandardRepr.B hS'
        simp at hSB
        set Q := (matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ).matrix
        set W := (matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix
        have hQW : Q = W.reindex =.≃
            (Equiv.sumCongr (Equiv.sumCongr (drop3_comm y₁ₗ y₀ₗ y₂ₗ).≃ fin2swap) (drop3_comm y₁ᵣ y₀ᵣ y₂ᵣ).≃.rightCongr).symm
        · ext i j
          cases i with
          | inl iₗ =>
            cases iₗ with
            | inl iₗₗ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
            | inr iₗ₁ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
          | inr iᵣ =>
            cases iᵣ with
            | inl iᵣ₂ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
            | inr iᵣᵣ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix]
                  set M₀ := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
                  set M₁ := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
                  have hDᵣ :
                      M₁.Dᵣ = M₀.Dᵣ.reindex =.≃ fin2swap
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases j <;> rfl
                  have hD₀ :
                      M₁.D₀ₗ = M₀.D₀ₗ.reindex fin2refl fin2swap
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> fin_cases j <;> rfl
                  have hDₗ :
                      M₁.Dₗ = M₀.Dₗ.reindex fin2refl (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> rfl
                  have hDᵣ₀ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ =
                      M₀.Dᵣ.reindex =.≃ fin2swap * (M₀.D₀ₗ.reindex fin2refl fin2swap)⁻¹
                  · rw [hDᵣ, hD₀]
                  have hDᵣ₀ₗ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ =
                      M₀.Dᵣ.reindex =.≃ fin2swap * (M₀.D₀ₗ.reindex fin2refl fin2swap)⁻¹
                      * M₀.Dₗ.reindex fin2refl (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · rw [hDᵣ₀, hDₗ]
                  have hDᵣ₀ₗ' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ = (
                        (M₀.Dᵣ.reindex =.≃ fin2swap
                        * (M₀.D₀ₗ.reindex fin2refl fin2swap)⁻¹
                        * M₀.Dₗ)
                      ).reindex =.≃ (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · rewrite [hDᵣ₀ₗ]
                    rfl
                  simp only [hDᵣ₀ₗ', Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.inv_submatrix_equiv]
                  simp
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
        have hyyyyyy :
          (equiv₃Y hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ) =
          (Equiv.sumCongr (Equiv.sumCongr (drop3_comm y₁ₗ y₀ₗ y₂ₗ).≃ fin2swap) (drop3_comm y₁ᵣ y₀ᵣ y₂ᵣ).≃.rightCongr :
            ((((Sₗ.Y.drop3 y₁ₗ y₀ₗ y₂ₗ).Elem ⊕ Fin 2) ⊕ (Unit ⊕ (Sᵣ.Y.drop3 y₁ᵣ y₀ᵣ y₂ᵣ).Elem)) ≃
              ((Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ).Elem ⊕ Fin 2) ⊕ (Unit ⊕ (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ).Elem))
          ).trans
            ((equiv₃Y hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ).trans
              ((drop2_comm y₀ᵣ y₁ᵣ).≃.rightCongr :
                (Sₗ.Y.drop1 y₂ₗ).Elem ⊕ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ).Elem ≃
                (Sₗ.Y.drop1 y₂ₗ).Elem ⊕ (Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ).Elem))
        · ext j
          cases j with
          | inl jₗ =>
            cases jₗ with
            | inl => rfl
            | inr j₂ => fin_cases j₂ <;> rfl
          | inr jᵣ =>
            cases jᵣ with
            | inl => rfl
            | inr => rfl
        rw [hyyyyyy, hQW]
        ext i j
        have hYyy : Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ = Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ
        · apply drop2_comm
        have hYyyy' : S.Y = Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ
        · rw [hYyyy, hYyy]
        rw [Matrix.toMatrixElemElem_apply, hSB.standardRepr_matrix_apply i j hXxxx hYyyy']
        cases hi : (hXxxx ▸ i).toSum with
        | inl iₗ =>
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            have hj' : (hYyyy' ▸ j).toSum = ◩jₗ
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi, hj']
          | inr jᵣ =>
            have hjj : HEq (hYyy ▸ jᵣ) jᵣ
            · apply eqRec_heq
            have hj' : (hYyyy' ▸ j).toSum = ◪(hYyy ▸ jᵣ)
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi, hj']
            rfl
        | inr iᵣ =>
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            have hj' : (hYyyy' ▸ j).toSum = ◩jₗ
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi, hj']
          | inr jᵣ =>
            have hjj : HEq (hYyy ▸ jᵣ) jᵣ
            · apply eqRec_heq
            have hj' : (hYyyy' ▸ j).toSum = ◪(hYyy ▸ jᵣ)
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi, hj']
            congr
  else
    have hf' : f = fin2swap := eq_fin2swap_of_ne_fin2refl hf
    if hg : g = fin2refl then
      simp [hf', hg] at hfg
      clear hg hf' hf g f
      let M := matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
      have hM : M.HasCanonicalSigning
      · constructor
        · constructor
          · use Bₗ.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ, hBₗ.submatrix _ _
            convert hSBₗ.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
            conv_rhs => rw [←(Sₗ.B.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bₗ, blocksToMatrixSum3, Matrix.fromCols_toCols, Matrix.fromBlocks_inj, true_and]
            constructor
            · ext i j
              fin_cases j
              simp [Matrix.toBlockSummandₗ, Matrix.toBlocks₁₂]
              cases i with
              | inl x => exact (hSS.rrrr.right.right.right.left x.val x.property.left ⟨drop3_ne₁ x, drop3_ne₀ x⟩).symm
              | inr => exact (hSS.rrrr.right.right.right.left x₂ hXX.mem3₂ₗ (by tauto)).symm
            · ext i j
              have : Sₗ.B x₀ₗ y₂ₗ = Sᵣ.B x₀ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₀ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₀ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₁ₗ y₂ₗ = Sᵣ.B x₁ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₁ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₁ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases j
              fin_cases i <;> tauto
          · use Bᵣ.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ, hBᵣ.submatrix _ _
            convert hSBᵣ.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
            conv_rhs => rw [←(Sᵣ.B.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bᵣ, blocksToMatrixSum3, Matrix.fromRows_toRows, Matrix.fromBlocks_inj, and_true]
            constructor
            · ext i j
              have : Sₗ.B x₂ₗ y₀ₗ = Sᵣ.B x₂ᵣ y₀ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₀ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₀ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₂ₗ y₁ₗ = Sᵣ.B x₂ᵣ y₁ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₁ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₁ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases i
              fin_cases j <;> tauto
            · ext i j
              fin_cases i
              simp [Matrix.toBlockSummandᵣ, Matrix.toBlocks₁₂]
              cases j with
              | inl => exact (hSS.rrrr.rrrr.rrrr y₂ hYY.mem3₂ᵣ (by tauto)).symm
              | inr y => exact (hSS.rrrr.rrrr.rrrr y.val y.property.left ⟨drop3_ne₀ y, drop3_ne₁ y⟩).symm
        · cases hfg with
          | inl h1001 =>
            left
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1001 0 0
              · exact congr_fun₂ h1001 0 1
              · exact hSS.rrrr.rrrr.right.left
              · exact congr_fun₂ h1001 1 0
              · exact congr_fun₂ h1001 1 1
              · exact hSS.rrrr.rrrr.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1001 0 0
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h00 h10
                rwa [←h10] at h00
              · have h01 := congr_fun₂ h1001 0 1
                have h11 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h01 h11
                rwa [←h11] at h01
              · tauto
              · have h10 := congr_fun₂ h1001 1 0
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h10 h00
                rwa [←h00] at h10
              · have h11 := congr_fun₂ h1001 1 1
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h11 h01
                rwa [←h01] at h11
              · tauto
              · exact hSS.rrrr.right.left
              · exact hSS.rrrr.right.right.left
              · rfl
          | inr h1101 =>
            right
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1101 0 0
              · exact congr_fun₂ h1101 0 1
              · exact hSS.rrrr.rrrr.right.left
              · exact congr_fun₂ h1101 1 0
              · exact congr_fun₂ h1101 1 1
              · exact hSS.rrrr.rrrr.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1101 0 0
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h00 h10
                rwa [←h10] at h00
              · have h01 := congr_fun₂ h1101 0 1
                have h11 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h01 h11
                rwa [←h11] at h01
              · tauto
              · have h10 := congr_fun₂ h1101 1 0
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h10 h00
                rwa [←h00] at h10
              · have h11 := congr_fun₂ h1101 1 1
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h11 h01
                rwa [←h01] at h11
              · tauto
              · exact hSS.rrrr.right.left
              · exact hSS.rrrr.right.right.left
              · rfl
      obtain ⟨B, hB, hBM⟩ := hM.HasTuSigning
      have hX₀₁ : Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ = Sₗ.X.drop2 x₁ₗ x₀ₗ ∪ Sᵣ.X.drop1 x₂ᵣ
      · rw [drop2_comm x₀ₗ x₁ₗ]
      rw [hX₀₁] at hXxxx
      use (B.toIntermediate hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ).toMatrixElemElem hXxxx hYyyy
      constructor
      · apply Matrix.IsTotallyUnimodular.toMatrixElemElem
        apply hB.submatrix
      · rw [Matrix.toMatrixDropUnionDrop_eq_toMatrixDropUnionDropInternal hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ] at hS'
        convert (hBM.reindex (equiv₃X hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm) (equiv₃Y hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ)).toMatrixElemElem hXxxx hYyyy
        simp only [Eq.interAll3, Matrix.toMatrixDropUnionDropInternal, Matrix.toIntermediate] at hS'
        simp only [M, Matrix.reindex_apply]
        have hSB := congr_arg_heq StandardRepr.B hS'
        simp at hSB
        set Q := (matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix
        set W := (matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix
        have hQW : Q = W.reindex
            (Equiv.sumCongr (drop3_comm x₁ₗ x₀ₗ x₂ₗ).≃.leftCongr (Equiv.sumCongr fin2swap (drop3_comm x₁ᵣ x₀ᵣ x₂ᵣ).≃)).symm
            =.≃
        · ext i j
          cases i with
          | inl iₗ =>
            cases iₗ with
            | inl iₗₗ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
            | inr iₗ₁ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
          | inr iᵣ =>
            cases iᵣ with
            | inl iᵣ₂ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
            | inr iᵣᵣ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix]
                  set M₀ := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
                  set M₁ := matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
                  have hDᵣ :
                      M₁.Dᵣ = M₀.Dᵣ.reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ fin2refl
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases j <;> rfl
                  have hD₀ :
                      M₁.D₀ₗ = M₀.D₀ₗ.reindex fin2swap fin2refl
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> fin_cases j <;> rfl
                  have hDₗ :
                      M₁.Dₗ = M₀.Dₗ.reindex fin2swap =.≃
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> rfl
                  have hDᵣ₀ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ =
                      M₀.Dᵣ.reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ fin2refl * (M₀.D₀ₗ.reindex fin2swap fin2refl)⁻¹
                  · rw [hDᵣ, hD₀]
                  have hDᵣ₀' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ =
                      (M₀.Dᵣ * (M₀.D₀ₗ.reindex fin2swap fin2refl)⁻¹).reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                  · rewrite [hDᵣ₀]
                    rfl
                  have hDᵣ₀ₗ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ =
                      (M₀.Dᵣ * (M₀.D₀ₗ.reindex fin2swap fin2refl)⁻¹).reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                      * M₀.Dₗ.reindex fin2swap =.≃
                  · rw [hDᵣ₀', hDₗ]
                  have hDᵣ₀ₗ' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ =
                      (M₀.Dᵣ * (M₀.D₀ₗ.reindex fin2swap fin2refl)⁻¹ * M₀.Dₗ.reindex fin2swap =.≃
                      ).reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                  · rewrite [hDᵣ₀ₗ]
                    rfl
                  simp only [hDᵣ₀ₗ', Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_apply,
                    Matrix.submatrix_submatrix, Matrix.submatrix_id_id, Matrix.inv_submatrix_equiv]
                  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.submatrix_mul_equiv]
                  simp
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
        have hxxxxxx :
          (equiv₃X hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm) =
          (Equiv.sumCongr (drop3_comm x₁ₗ x₀ₗ x₂ₗ).≃.leftCongr (Equiv.sumCongr fin2swap (drop3_comm x₁ᵣ x₀ᵣ x₂ᵣ).≃) :
            ((((Sₗ.X.drop3 x₁ₗ x₀ₗ x₂ₗ).Elem ⊕ Unit) ⊕ (Fin 2 ⊕ (Sᵣ.X.drop3 x₁ᵣ x₀ᵣ x₂ᵣ).Elem)) ≃
              ((Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ).Elem ⊕ Unit) ⊕ (Fin 2 ⊕ (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ).Elem))
          ).trans
            ((equiv₃X hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ).trans
              ((drop2_comm x₀ₗ x₁ₗ).≃.leftCongr :
                (Sₗ.X.drop2 x₀ₗ x₁ₗ).Elem ⊕ (Sᵣ.X.drop1 x₂ᵣ).Elem ≃
                (Sₗ.X.drop2 x₁ₗ x₀ₗ).Elem ⊕ (Sᵣ.X.drop1 x₂ᵣ).Elem))
        · ext i
          cases i with
          | inl iₗ =>
            cases iₗ with
            | inl => rfl
            | inr => rfl
          | inr iᵣ =>
            cases iᵣ with
            | inl i₂ => fin_cases i₂ <;> rfl
            | inr => rfl
        rw [hxxxxxx, hQW]
        ext i j
        have hXxx : Sₗ.X.drop2 x₀ₗ x₁ₗ = Sₗ.X.drop2 x₁ₗ x₀ₗ
        · apply drop2_comm
        have hXxxx' : S.X = Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ
        · rw [hXxxx, hXxx]
        rw [Matrix.toMatrixElemElem_apply, hSB.standardRepr_matrix_apply i j hXxxx' hYyyy]
        cases hi : (hXxxx ▸ i).toSum with
        | inl iₗ =>
          have hii : HEq (hXxx ▸ iₗ) iₗ
          · apply eqRec_heq
          have hi' : (hXxxx' ▸ i).toSum = ◩(hXxx ▸ iₗ)
          · convert hi
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj]
            congr
          | inr jᵣ =>
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj]
            rfl
        | inr iᵣ =>
          have hi' : (hXxxx' ▸ i).toSum = ◪iᵣ
          · convert hi
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj]
          | inr jᵣ =>
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj]
    else
      have hg' : g = fin2swap := eq_fin2swap_of_ne_fin2refl hg
      simp [hf', hg'] at hfg
      clear hg' hg hf' hf g f
      let M := matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
      have hM : M.HasCanonicalSigning
      · constructor
        · constructor
          · use Bₗ.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ, hBₗ.submatrix _ _
            convert hSBₗ.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ
            conv_rhs => rw [←(Sₗ.B.toBlockSummandₗ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bₗ, blocksToMatrixSum3, Matrix.fromCols_toCols, Matrix.fromBlocks_inj, true_and]
            constructor
            · ext i j
              fin_cases j
              simp [Matrix.toBlockSummandₗ, Matrix.toBlocks₁₂]
              cases i with
              | inl x => exact (hSS.rrrr.right.right.right.left x.val x.property.left ⟨drop3_ne₁ x, drop3_ne₀ x⟩).symm
              | inr => exact (hSS.rrrr.right.right.right.left x₂ hXX.mem3₂ₗ (by tauto)).symm
            · ext i j
              have : Sₗ.B x₀ₗ y₂ₗ = Sᵣ.B x₀ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₀ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₀ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₁ₗ y₂ₗ = Sᵣ.B x₁ᵣ y₂ᵣ
              · have h1ₗ : Sₗ.B x₁ₗ y₂ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₁ᵣ y₂ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases j
              fin_cases i <;> tauto
          · use Bᵣ.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ, hBᵣ.submatrix _ _
            convert hSBᵣ.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
            conv_rhs => rw [←(Sᵣ.B.toBlockSummandᵣ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ).fromBlocks_toBlocks]
            simp_rw [M, MatrixSum3.Bᵣ, blocksToMatrixSum3, Matrix.fromRows_toRows, Matrix.fromBlocks_inj, and_true]
            constructor
            · ext i j
              have : Sₗ.B x₂ₗ y₀ₗ = Sᵣ.B x₂ᵣ y₀ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₀ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₀ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              have : Sₗ.B x₂ₗ y₁ₗ = Sᵣ.B x₂ᵣ y₁ᵣ
              · have h1ₗ : Sₗ.B x₂ₗ y₁ₗ = 1
                · tauto
                have h1ᵣ : Sᵣ.B x₂ᵣ y₁ᵣ = 1
                · tauto
                rw [h1ₗ, h1ᵣ]
              fin_cases i
              fin_cases j <;> tauto
            · ext i j
              fin_cases i
              simp [Matrix.toBlockSummandᵣ, Matrix.toBlocks₁₂]
              cases j with
              | inl => exact (hSS.rrrr.rrrr.rrrr y₂ hYY.mem3₂ᵣ (by tauto)).symm
              | inr y => exact (hSS.rrrr.rrrr.rrrr y.val y.property.left ⟨drop3_ne₁ y, drop3_ne₀ y⟩).symm
        · cases hfg with
          | inl h1001 =>
            left
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1001 0 0
              · exact congr_fun₂ h1001 0 1
              · exact hSS.rrrr.rrrr.right.left
              · exact congr_fun₂ h1001 1 0
              · exact congr_fun₂ h1001 1 1
              · exact hSS.rrrr.rrrr.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1001 0 0
                have h11 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h00 h11
                rwa [←h11] at h00
              · have h01 := congr_fun₂ h1001 0 1
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h01 h10
                rwa [←h10] at h01
              · tauto
              · have h10 := congr_fun₂ h1001 1 0
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h10 h01
                rwa [←h01] at h10
              · have h11 := congr_fun₂ h1001 1 1
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h11 h00
                rwa [←h00] at h11
              · tauto
              · exact hSS.rrrr.right.right.left
              · exact hSS.rrrr.right.left
              · rfl
          | inr h1101 =>
            right
            constructor
            · ext i j
              fin_cases i <;> fin_cases j
              · exact congr_fun₂ h1101 0 0
              · exact congr_fun₂ h1101 0 1
              · exact hSS.rrrr.rrrr.right.left
              · exact congr_fun₂ h1101 1 0
              · exact congr_fun₂ h1101 1 1
              · exact hSS.rrrr.rrrr.left
              · tauto
              · tauto
              · rfl
            · ext i j
              fin_cases i <;> fin_cases j
              · have h00 := congr_fun₂ h1101 0 0
                have h11 := congr_fun₂ hSS.right.left.symm 1 1
                simp at h00 h11
                rwa [←h11] at h00
              · have h01 := congr_fun₂ h1101 0 1
                have h10 := congr_fun₂ hSS.right.left.symm 1 0
                simp at h01 h10
                rwa [←h10] at h01
              · tauto
              · have h10 := congr_fun₂ h1101 1 0
                have h01 := congr_fun₂ hSS.right.left.symm 0 1
                simp at h10 h01
                rwa [←h01] at h10
              · have h11 := congr_fun₂ h1101 1 1
                have h00 := congr_fun₂ hSS.right.left.symm 0 0
                simp at h11 h00
                rwa [←h00] at h11
              · tauto
              · exact hSS.rrrr.right.right.left
              · exact hSS.rrrr.right.left
              · rfl
      obtain ⟨B, hB, hBM⟩ := hM.HasTuSigning
      have hX₀₁ : Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ = Sₗ.X.drop2 x₁ₗ x₀ₗ ∪ Sᵣ.X.drop1 x₂ᵣ
      · rw [drop2_comm x₀ₗ x₁ₗ]
      have hY₀₁ : Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ = Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ
      · rw [drop2_comm y₀ᵣ y₁ᵣ]
      rw [hX₀₁] at hXxxx
      rw [hY₀₁] at hYyyy
      use (B.toIntermediate hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ).toMatrixElemElem hXxxx hYyyy
      constructor
      · apply Matrix.IsTotallyUnimodular.toMatrixElemElem
        apply hB.submatrix
      · rw [Matrix.toMatrixDropUnionDrop_eq_toMatrixDropUnionDropInternal hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ] at hS'
        convert (hBM.reindex (equiv₃X hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm) (equiv₃Y hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ)).toMatrixElemElem hXxxx hYyyy
        simp only [Eq.interAll3, Matrix.toMatrixDropUnionDropInternal, Matrix.toIntermediate] at hS'
        simp only [M, Matrix.reindex_apply]
        have hSB := congr_arg_heq StandardRepr.B hS'
        simp at hSB
        set Q := (matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ).matrix
        set W := (matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix
        have hQW : Q = W.reindex
            (Equiv.sumCongr (drop3_comm x₁ₗ x₀ₗ x₂ₗ).≃.leftCongr (Equiv.sumCongr fin2swap (drop3_comm x₁ᵣ x₀ᵣ x₂ᵣ).≃)).symm
            (Equiv.sumCongr (Equiv.sumCongr (drop3_comm y₁ₗ y₀ₗ y₂ₗ).≃ fin2swap) (drop3_comm y₁ᵣ y₀ᵣ y₂ᵣ).≃.rightCongr).symm
        · ext i j
          cases i with
          | inl iₗ =>
            cases iₗ with
            | inl iₗₗ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
            | inr iₗ₁ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
          | inr iᵣ =>
            cases iᵣ with
            | inl iᵣ₂ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases iᵣ₂ <;> rfl
            | inr iᵣᵣ =>
              cases j with
              | inl jₗ =>
                cases jₗ with
                | inl jₗₗ =>
                  simp [Q, W, MatrixSum3.matrix]
                  set M₀ := matrixSum3aux Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
                  set M₁ := matrixSum3aux Sₗ Sᵣ x₁ₗ x₀ₗ x₂ₗ y₁ₗ y₀ₗ y₂ₗ x₁ᵣ x₀ᵣ x₂ᵣ y₁ᵣ y₀ᵣ y₂ᵣ
                  have hDᵣ :
                      M₁.Dᵣ = M₀.Dᵣ.reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ fin2swap
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases j <;> rfl
                  have hD₀ :
                      M₁.D₀ₗ = M₀.D₀ₗ.reindex fin2swap fin2swap
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> fin_cases j <;> rfl
                  have hDₗ :
                      M₁.Dₗ = M₀.Dₗ.reindex fin2swap (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · simp [M₀, M₁, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                    ext i j
                    fin_cases i <;> rfl
                  have hDᵣ₀ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ =
                      M₀.Dᵣ.reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ fin2swap * (M₀.D₀ₗ.reindex fin2swap fin2swap)⁻¹
                  · rw [hDᵣ, hD₀]
                  have hDᵣ₀' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ =
                      (M₀.Dᵣ.reindex =.≃ fin2swap * (M₀.D₀ₗ.reindex fin2swap fin2swap)⁻¹).reindex
                        (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                  · rewrite [hDᵣ₀]
                    rfl
                  have hDᵣ₀ₗ :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ =
                      (M₀.Dᵣ.reindex =.≃ fin2swap * (M₀.D₀ₗ.reindex fin2swap fin2swap)⁻¹).reindex
                        (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                      * M₀.Dₗ.reindex fin2swap (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · rw [hDᵣ₀', hDₗ]
                  have hDᵣ₀ₗ' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ =
                      ((M₀.Dᵣ.reindex =.≃ fin2swap * (M₀.D₀ₗ.reindex fin2swap fin2swap)⁻¹).reindex
                        (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ =.≃
                      * M₀.Dₗ.reindex fin2swap =.≃).reindex =.≃ (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · rewrite [hDᵣ₀ₗ]
                    rfl
                  have hDᵣ₀ₗ'' :
                      M₁.Dᵣ * M₁.D₀ₗ⁻¹ * M₁.Dₗ = (
                        (M₀.Dᵣ.reindex =.≃ fin2swap
                        * (M₀.D₀ₗ.reindex fin2swap fin2swap)⁻¹
                        * M₀.Dₗ.reindex fin2swap =.≃)
                      ).reindex (drop3_comm x₀ᵣ x₁ᵣ x₂ᵣ).≃ (drop3_comm y₀ₗ y₁ₗ y₂ₗ).≃
                  · rewrite [hDᵣ₀ₗ']
                    rfl
                  simp [hDᵣ₀ₗ'']
                | inr jₗ₂ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  fin_cases jₗ₂ <;> rfl
              | inr jᵣ =>
                cases jᵣ with
                | inl jᵣ₁ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
                | inr jᵣᵣ =>
                  simp [Q, W, MatrixSum3.matrix, blocksToMatrixSum3, Matrix.toBlockSummandₗ, Matrix.toBlockSummandᵣ]
                  rfl
        have hxxxxxx :
          (equiv₃X hx₁ₗ hx₀ₗ hx₁ᵣ hx₀ᵣ hx₂ᵣ.symm) =
          (Equiv.sumCongr (drop3_comm x₁ₗ x₀ₗ x₂ₗ).≃.leftCongr (Equiv.sumCongr fin2swap (drop3_comm x₁ᵣ x₀ᵣ x₂ᵣ).≃) :
            ((((Sₗ.X.drop3 x₁ₗ x₀ₗ x₂ₗ).Elem ⊕ Unit) ⊕ (Fin 2 ⊕ (Sᵣ.X.drop3 x₁ᵣ x₀ᵣ x₂ᵣ).Elem)) ≃
              ((Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ).Elem ⊕ Unit) ⊕ (Fin 2 ⊕ (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ).Elem))
          ).trans
            ((equiv₃X hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ).trans
              ((drop2_comm x₀ₗ x₁ₗ).≃.leftCongr :
                (Sₗ.X.drop2 x₀ₗ x₁ₗ).Elem ⊕ (Sᵣ.X.drop1 x₂ᵣ).Elem ≃
                (Sₗ.X.drop2 x₁ₗ x₀ₗ).Elem ⊕ (Sᵣ.X.drop1 x₂ᵣ).Elem))
        · ext i
          cases i with
          | inl iₗ =>
            cases iₗ with
            | inl => rfl
            | inr => rfl
          | inr iᵣ =>
            cases iᵣ with
            | inl i₂ => fin_cases i₂ <;> rfl
            | inr => rfl
        have hyyyyyy :
          (equiv₃Y hy₁ₗ hy₀ₗ hy₂ₗ.symm hy₁ᵣ hy₀ᵣ) =
          (Equiv.sumCongr (Equiv.sumCongr (drop3_comm y₁ₗ y₀ₗ y₂ₗ).≃ fin2swap) (drop3_comm y₁ᵣ y₀ᵣ y₂ᵣ).≃.rightCongr :
            ((((Sₗ.Y.drop3 y₁ₗ y₀ₗ y₂ₗ).Elem ⊕ Fin 2) ⊕ (Unit ⊕ (Sᵣ.Y.drop3 y₁ᵣ y₀ᵣ y₂ᵣ).Elem)) ≃
              ((Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ).Elem ⊕ Fin 2) ⊕ (Unit ⊕ (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ).Elem))
          ).trans
            ((equiv₃Y hy₀ₗ hy₁ₗ hy₂ₗ hy₀ᵣ hy₁ᵣ).trans
              ((drop2_comm y₀ᵣ y₁ᵣ).≃.rightCongr :
                (Sₗ.Y.drop1 y₂ₗ).Elem ⊕ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ).Elem ≃
                (Sₗ.Y.drop1 y₂ₗ).Elem ⊕ (Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ).Elem))
        · ext j
          cases j with
          | inl jₗ =>
            cases jₗ with
            | inl => rfl
            | inr j₂ => fin_cases j₂ <;> rfl
          | inr jᵣ =>
            cases jᵣ with
            | inl => rfl
            | inr => rfl
        rw [hxxxxxx, hyyyyyy, hQW]
        ext i j
        have hXxx : Sₗ.X.drop2 x₀ₗ x₁ₗ = Sₗ.X.drop2 x₁ₗ x₀ₗ
        · apply drop2_comm
        have hYyy : Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ = Sᵣ.Y.drop2 y₁ᵣ y₀ᵣ
        · apply drop2_comm
        have hXxxx' : S.X = Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ
        · rw [hXxxx, hXxx]
        have hYyyy' : S.Y = Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ
        · rw [hYyyy, hYyy]
        rw [Matrix.toMatrixElemElem_apply, hSB.standardRepr_matrix_apply i j hXxxx' hYyyy']
        cases hi : (hXxxx ▸ i).toSum with
        | inl iₗ =>
          have hii : HEq (hXxx ▸ iₗ) iₗ
          · apply eqRec_heq
          have hi' : (hXxxx' ▸ i).toSum = ◩(hXxx ▸ iₗ)
          · convert hi
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            have hj' : (hYyyy' ▸ j).toSum = ◩jₗ
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj']
            congr
          | inr jᵣ =>
            have hjj : HEq (hYyy ▸ jᵣ) jᵣ
            · apply eqRec_heq
            have hj' : (hYyyy' ▸ j).toSum = ◪(hYyy ▸ jᵣ)
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj']
            rfl
        | inr iᵣ =>
          have hi' : (hXxxx' ▸ i).toSum = ◪iᵣ
          · convert hi
          cases hj : (hYyyy ▸ j).toSum with
          | inl jₗ =>
            have hj' : (hYyyy' ▸ j).toSum = ◩jₗ
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj']
          | inr jᵣ =>
            have hjj : HEq (hYyy ▸ jᵣ) jᵣ
            · apply eqRec_heq
            have hj' : (hYyyy' ▸ j).toSum = ◪(hYyy ▸ jᵣ)
            · convert hj
            simp [equiv₃X, equiv₃Y, Matrix.toMatrixUnionUnion, ←Function.comp_assoc, hi', hj']
            congr


/-! ### The 3-sum of matroids -/

/-- Matroid `M` is a result of 3-summing `Mₗ` and `Mᵣ` in some way. -/
def Matroid.IsSum3of (M : Matroid α) (Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ x₀ x₁ x₂ y₀ y₁ y₂ : α,
  ∃ hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂},
  ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂},
  ∃ hXY : Sₗ.X ⫗ Sᵣ.Y,
  ∃ hYX : Sₗ.Y ⫗ Sᵣ.X,
  standardReprSum3 hXX hYY hXY hYX = some S
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

lemma Matroid.IsSum3of.E_eq (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hMMM : M.IsSum3of Mₗ Mᵣ) :
    M.E = Mₗ.E ∪ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, _, _, _, _, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  have hX := standardReprSum3_X_eq hS
  have hY := standardReprSum3_Y_eq hS
  simp only [StandardRepr.toMatroid_E]
  tauto_set

/-- Any 3-sum of two regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsSum3of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum3of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, _, _, _, _, _, _, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum3_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum3_hasTuSigning hMₗ hMᵣ hSSS
