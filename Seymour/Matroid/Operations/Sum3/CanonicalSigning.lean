import Seymour.Matroid.Operations.Sum3.Basic


/-! # Canonical signing of matrices -/

/-! ## Definition -/

/-- Canonical re-signing of a matrix. -/
def Matrix.toCanonicalSigning {X Y : Type} [DecidableEq X] [DecidableEq Y]
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
def Matrix.toCanonicalSigning_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `toCanonicalSigning))
  | _ => throw ()


/-! ## General results -/

set_option maxHeartbeats 333333 in
/-- Canonical re-signing of a matrix has the same absolute value as the original matrix. -/
@[simp]
lemma Matrix.toCanonicalSigning_apply_abs {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (Q : Matrix X Y ℚ) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (_ : |Q x₀ y₀| = 1) (_ : |Q x₀ y₂| = 1) (_ : |Q x₂ y₀| = 1) (_ : |Q x₁ y₂| = 1) (_ : |Q x₂ y₁| = 1) (i : X) (j : Y) :
    |(Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂) i j| = |Q i j| := by
  aesop (add simp [abs_mul, Matrix.toCanonicalSigning])

/-- Canonical re-signing of a TU matrix is TU. -/
lemma Matrix.IsTotallyUnimodular.toCanonicalSigning {X Y : Type} [DecidableEq X] [DecidableEq Y] {Q : Matrix X Y ℚ}
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
  exact Q.entryProd_outerProd_eq_mul_col_mul_row _ _ ▸ (hQ.mul_rows hu).mul_cols hv


/-! ## Definition of re-signing in two special cases -/

/-- Proposition that `Q` is a TU canonical signing in the first special case. -/
def Matrix.IsTuCanonicalSigning₀ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂] = matrix3x3signed₀

@[app_unexpander Matrix.IsTuCanonicalSigning₀]
def Matrix.IsTuCanonicalSigning₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicalSigning₀))
  | _ => throw ()

/-- Proposition that `Q` is a TU canonical signing in the second special case. -/
def Matrix.IsTuCanonicalSigning₁ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂] = matrix3x3signed₁

@[app_unexpander Matrix.IsTuCanonicalSigning₁]
def Matrix.IsTuCanonicalSigning₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicalSigning₁))
  | _ => throw ()

/-- Sufficient condition for existence of a TU canonical signing in the first special case. -/
def Matrix.HasTuCanonicalSigning₀ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₀ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₀]
def Matrix.HasTuCanonicalSigning₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₀))
  | _ => throw ()

/-- Sufficient condition for existence of a TU canonical signing in the second spcial case. -/
def Matrix.HasTuCanonicalSigning₁ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular ∧ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₁ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₁]
def Matrix.HasTuCanonicalSigning₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₁))
  | _ => throw ()


/-! ## Lemmas about distinctness of row and column indices -/

lemma Matrix.IsTuCanonicalSigning₀.distinct_x₀_x₁_x₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hxx
    rw [hxx] at hQ
    have hQ01 := congr_fun₂ hQ.right 0 1
    have hQ11 := congr_fun₂ hQ.right 1 1
    have hQ21 := congr_fun₂ hQ.right 2 1
    simp at hQ01 hQ11 hQ21
    linarith

lemma Matrix.IsTuCanonicalSigning₀.distinct_y₀_y₁_y₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁ := by
  constructor
  on_goal 2 => constructor
  all_goals
    by_contra hyy
    rw [hyy] at hQ
    have hQ10 := congr_fun₂ hQ.right 1 0
    have hQ11 := congr_fun₂ hQ.right 1 1
    have hQ12 := congr_fun₂ hQ.right 1 2
    simp at hQ10 hQ11 hQ12
    linarith

lemma Matrix.IsTuCanonicalSigning₁.distinct_x₀_x₁_x₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
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
    simp at hQ01 hQ11 hQ21 hQ02 hQ22
    linarith

lemma Matrix.IsTuCanonicalSigning₁.distinct_y₀_y₁_y₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
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
    simp at hQ10 hQ11 hQ12 hQ21 hQ22
    linarith

lemma Matrix.HasTuCanonicalSigning₀.distinct_x₀_x₁_x₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
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

lemma Matrix.HasTuCanonicalSigning₀.distinct_y₀_y₁_y₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
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

lemma Matrix.HasTuCanonicalSigning₁.distinct_x₀_x₁_x₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
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

lemma Matrix.HasTuCanonicalSigning₁.distinct_y₀_y₁_y₂ {X Y : Type} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
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
lemma Matrix.HasTuCanonicalSigning₀.toCanonicalSigning_submatrix3x3 {X Y : Type} [DecidableEq X] [DecidableEq Y]
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

/-- Re-signing a TU matrix in the second special case transforms the 3×3 submatrix to its canonically signed version.
    Note: the proof takes a long time to compile due to the large number of case distinctions. -/
lemma Matrix.HasTuCanonicalSigning₁.toCanonicalSigning_submatrix3x3 {X Y : Type} [DecidableEq X] [DecidableEq Y]
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

/-- Canonical re-signing of a TU matrix yields its canonically signed version in the first special case. -/
lemma Matrix.HasTuCanonicalSigning₀.toCanonicalSigning_IsTuCanonicalSigning₀ {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂ :=
  ⟨hQ.left.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hQ.toCanonicalSigning_submatrix3x3⟩

/-- Canonical re-signing of a TU matrix yields its canonically signed version in the second special case. -/
lemma Matrix.HasTuCanonicalSigning₁.toCanonicalSigning_IsTuCanonicalSigning₁ {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂ :=
  ⟨hQ.left.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hQ.toCanonicalSigning_submatrix3x3⟩
