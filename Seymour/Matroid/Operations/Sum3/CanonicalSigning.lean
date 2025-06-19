import Seymour.Matroid.Operations.Sum3.Basic


/-! # Canonical signing of matrices -/

/-! ## Additional notation for convenience -/

/-- The 3×3 submatrix indexed by the given 6 elements. -/
@[simp]
abbrev Matrix.submatrix3x3 {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![Q x₀ y₀, Q x₀ y₁, Q x₀ y₂;
     Q x₁ y₀, Q x₁ y₁, Q x₁ y₂;
     Q x₂ y₀, Q x₂ y₁, Q x₂ y₂]

@[app_unexpander Matrix.submatrix3x3]
def Matrix.submatrix3x3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `submatrix3x3))
  | _ => throw ()

/-- Equivalent way to obtain the 3×3 submatrix. -/
lemma Matrix.submatrix3x3_eq {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ =
    Q.submatrix
      (match · with
        | 0 => x₀
        | 1 => x₁
        | 2 => x₂)
      (match · with
        | 0 => y₀
        | 1 => y₁
        | 2 => y₂)
    := by
  ext
  rw [Matrix.submatrix_apply]
  split <;> split <;> rfl

/-- The 3×3 submatrix of a totally unimodular matrix is totally unimodular. -/
lemma Matrix.IsTotallyUnimodular.submatrix3x3 {X Y : Type} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    (Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂).IsTotallyUnimodular := by
  rw [Matrix.submatrix3x3_eq]
  apply hQ.submatrix


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


/-! ## Re-signing in two special cases -/

/-- Proposition that `Q` is a TU canonical signing in the first special case. -/
def Matrix.IsTuCanonicalSigning₀ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀

/-- Proposition that `Q` is a TU canonical signing in the second special case. -/
def Matrix.IsTuCanonicalSigning₁ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁

/-- Sufficient condition for existence of a TU canonical signing in the first special case. -/
def Matrix.HasTuCanonicalSigning₀ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₀ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₀]
def Matrix.HasTuCanonicalSigning₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₀))
  | _ => throw ()

/-- Sufficient condition for existence of a TU canonical signing in the second spcial case. -/
def Matrix.HasTuCanonicalSigning₁ {X Y : Type} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₁ ℚ

@[app_unexpander Matrix.HasTuCanonicalSigning₁]
def Matrix.HasTuCanonicalSigning₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `HasTuCanonicalSigning₁))
  | _ => throw ()

/-- Re-signing a TU matrix in the first special case transforms the 3×3 submatrix to its canonically signed version.
    Note: the proof takes a long time to compile due to the large number of case distinctions. -/
lemma Matrix.HasTuCanonicalSigning₀.toCanonicalSigning_submatrix3x3 {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₀] at hQxy
  have hQ₀₀ := congr_fun₂ hQxy 0 0
  have hQ₀₁ := congr_fun₂ hQxy 0 1
  have hQ₀₂ := congr_fun₂ hQxy 0 2
  have hQ₁₀ := congr_fun₂ hQxy 1 0
  have hQ₁₁ := congr_fun₂ hQxy 1 1
  have hQ₁₂ := congr_fun₂ hQxy 1 2
  have hQ₂₀ := congr_fun₂ hQxy 2 0
  have hQ₂₁ := congr_fun₂ hQxy 2 1
  have hQ₂₂ := congr_fun₂ hQxy 2 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₀,
        hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hQ₀₁, hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d, hd⟩ := hQ3x3tu 3 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_three] at hd
  clear hQtu hQ3x3tu hQxy hQ₀₁ hQ₁₀ hQ₂₂ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
  cases hQ₀₀ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd

/-- Re-signing a TU matrix in the second special case transforms the 3×3 submatrix to its canonically signed version.
    Note: the proof takes a long time to compile due to the large number of case distinctions. -/
lemma Matrix.HasTuCanonicalSigning₁.toCanonicalSigning_submatrix3x3 {X Y : Type} [DecidableEq X] [DecidableEq Y]
    {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₁] at hQxy
  have hQ₀₀ := congr_fun₂ hQxy 0 0
  have hQ₀₁ := congr_fun₂ hQxy 0 1
  have hQ₀₂ := congr_fun₂ hQxy 0 2
  have hQ₁₀ := congr_fun₂ hQxy 1 0
  have hQ₁₁ := congr_fun₂ hQxy 1 1
  have hQ₁₂ := congr_fun₂ hQxy 1 2
  have hQ₂₀ := congr_fun₂ hQxy 2 0
  have hQ₂₁ := congr_fun₂ hQxy 2 1
  have hQ₂₂ := congr_fun₂ hQxy 2 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₁, matrix3x3unsigned₁,
        hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d₁, hd₁⟩ := (hQ3x3tu.submatrix ![0, 2] ![0, 1]) 2 id id Function.injective_id Function.injective_id
  obtain ⟨d₂, hd₂⟩ := (hQ3x3tu.submatrix ![0, 1] ![1, 2]) 2 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_two] at hd₁ hd₂
  clear hQtu hQ3x3tu hQxy hQ₁₀ hQ₂₂ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
  cases hQ₀₀ <;> cases hQ₀₁ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd₁ hd₂

/-- Re-signing a TU matrix in the first special case yields its canonically signed version. -/
lemma Matrix.HasTuCanonicalSigning₀.toCanonicalSigning {X Y : Type} [DecidableEq X] [DecidableEq Y] {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

/-- Re-signing a TU matrix in the second special case yields its canonically signed version. -/
lemma Matrix.HasTuCanonicalSigning₁.toCanonicalSigning {X Y : Type} [DecidableEq X] [DecidableEq Y] {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.HasTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩
