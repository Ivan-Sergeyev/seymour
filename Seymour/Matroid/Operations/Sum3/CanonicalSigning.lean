import Seymour.Matroid.Operations.Sum3.Basic


variable {α : Type} [DecidableEq α]

-- ## Canonical signing definition and API

/-- Proposition that `Q` is a TU canonical signing with `0` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀

/-- Proposition that `Q` is a TU canonical signing with `1` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
/-private-/ def Matrix.IsTuCanonicallySignable₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₀

@[app_unexpander Matrix.IsTuCanonicallySignable₀]
/-private-/ def Matrix.IsTuCanonicallySignable₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicallySignable₀))
  | _ => throw ()

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
/-private-/ def Matrix.IsTuCanonicallySignable₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₁

@[app_unexpander Matrix.IsTuCanonicallySignable₁]
/-private-/ def Matrix.IsTuCanonicallySignable₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicallySignable₁))
  | _ => throw ()

/-- Converts a matrix to the form of canonical TU signing, does not check assumptions. -/
@[simp]
/-private-/ def Matrix.toCanonicalSigning {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
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
/-private-/ def Matrix.toCanonicalSigning_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `toCanonicalSigning))
  | _ => throw ()

/-- Canonical signing of a TU matrix is TU. -/
/-private-/ lemma Matrix.IsTotallyUnimodular.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ}
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

/-private-/ lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₀] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
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

/-private-/ lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₁] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
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

/-private-/ lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

/-private-/ lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩


-- ## Special columns and rows

/-- `c₀` or `c₁` -/
@[simp] /-private-/ abbrev Matrix._col {X Y : Set α} {a : α} (B : Matrix X Y ℚ) (y : Y) (i : (X \ {a}).Elem) : ℚ :=
  B (Set.diff_subset.elem i) y

@[app_unexpander Matrix._col]
/-private-/ def Matrix._col_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_col))
  | _ => throw ()

/-- `d₀` or `d₁` -/
@[simp] /-private-/ abbrev Matrix._row {X Y : Set α} {a : α} (B : Matrix X Y ℚ) (x : X) (j : (Y \ {a}).Elem) : ℚ :=
  B x (Set.diff_subset.elem j)

@[app_unexpander Matrix._row]
/-private-/ def Matrix._row_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_row))
  | _ => throw ()

/-- `r₀` and `r₁` and `r₂` -/
/-private-/ abbrev Matrix._rrr {X Y : Set α} (B' : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    let D₀ := |B'.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂|
    (D₀ = matrix3x3unsigned₀ ∨ D₀ = matrix3x3unsigned₁) →
      (((Y \ {y₂.val}).Elem → ℚ) × ((Y \ {y₂.val}).Elem → ℚ) × ((Y \ {y₂.val}).Elem → ℚ)) :=
  fun hB' =>
    let B := B'.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂
    let d₀ : (Y \ {y₂.val}).Elem → ℚ := B._row x₀
    let d₁ : (Y \ {y₂.val}).Elem → ℚ := B._row x₁
    let D₀ := |B'.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂|
    if hD₀₀ : D₀ = matrix3x3unsigned₀ then ⟨d₀, d₁, d₀ - d₁⟩ else
    if hD₀₁ : D₀ = matrix3x3unsigned₁ then ⟨d₀ - d₁, d₁, d₀⟩ else
    (False.elim (by
      simp only [D₀, hD₀₀, hD₀₁] at hB'
      exact hB'.casesOn id id))

@[app_unexpander Matrix._rrr]
/-private-/ def Matrix._rrr_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_rrr))
  | _ => throw ()

-- lemma 15.a
set_option maxHeartbeats 300000 in
/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion₀ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B : Matrix X Y ℚ := Q.shortTableauPivot x₂ y₀
  let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₀) ↓y₁),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◩◪() else if hy₁ : y = y₁ then ◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).submatrix id e.symm
  · ext i j
    have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
    have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
    if hjy₀ : j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀]
    else if hjy₁ : j = y₁ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
      have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₀]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) (-1))
  have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 15.b
set_option maxHeartbeats 300000 in
/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion₁ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B := Q.shortTableauPivot x₂ y₁
  let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₁) ↓y₀),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◪() else if hy₁ : y = y₁ then ◩◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).submatrix id e.symm
  · ext i j
    have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
    have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
    if hjy₀ : j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else if hjy₁ : j = y₁ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
      have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₁]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
  have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 16.1
omit [DecidableEq α] in
/-private-/ lemma Matrix.IsTotallyUnimodular.special_form_cols {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    ∀ i : X.drop1 x₂, ![c₀ i, c₁ i] ≠ ![1, -1] ∧ ![c₀ i, c₁ i] ≠ ![-1, 1] := by
  intro c₀ c₁ i
  constructor <;>
  · intro contr
    simp only [c₀, c₁] at contr
    have := congr_fun contr 0
    have := congr_fun contr 1
    have := hQ.det ![x₂, Set.diff_subset.elem i] ![y₀, y₁]
    simp_all [Matrix.det_fin_two]

-- lemma 16.2
/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_weak {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  sorry

/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_aux {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intros
  convert (hQ.signing_expansion_cols_weak hyy hQy₀ hQy₁ hQy).comp_cols
    (fun j : ((((((Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (◩◩◩·) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) ↓◪()) ↓◪()))
  aesop

/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion_cols {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ ▮0).IsTotallyUnimodular := by
  intros
  convert ((hQ.signing_expansion_cols_aux hyy hQy₀ hQy₁ hQy).mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 1) (-1)) 1) (-1)) 1) (-1)) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).fromCols_zero Unit
  aesop

-- Lemma 18.2's corollary
/-private-/ lemma Matrix.IsTotallyUnimodular.signing_expansion_rows {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₀ x₁ : X} {y₂ : Y} (hxx : x₀ ≠ x₁) (hQx₀ : Q x₀ y₂ = 1) (hQx₁ : Q x₁ y₂ = 1)
    (hQx : ∀ x : X, x.val ≠ x₀ ∧ x.val ≠ x₁ → Q x y₂ = 0) :
    let d₀ := Q._row x₀
    let d₁ := Q._row x₁
    let Q' := Q.Aₗ x₀ x₁ y₂
    (Q' ⊟ ▬d₀ ⊟ ▬(-d₀) ⊟ ▬d₁ ⊟ ▬(-d₁) ⊟ ▬(d₀ - d₁) ⊟ ▬(d₁ - d₀) ⊟ ▬0).IsTotallyUnimodular := by
  intros
  convert (hQ.transpose.signing_expansion_cols hxx hQx₀ hQx₁ hQx).transpose
  aesop

/-- Canonical signing of 3-sum constructed from TU signings of summands. -/
@[simp]
/-private-/ noncomputable def matrix3sumCompositionCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (Bₗ' : Matrix Xₗ Yₗ ℚ) (Bᵣ' : Matrix Xᵣ Yᵣ ℚ) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    let ⟨⟨x₀ₗ, x₁ₗ, _⟩, ⟨_, _, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨_, _, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _⟩⟩ := hYY.inter3all
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ⊕ Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ ⊕ Yᵣ.drop2 y₀ᵣ y₁ᵣ) ℚ :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  -- convert summands to canonical form
  let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
  let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
  -- pieces of the bottom left submatrix
  let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  -- the actual definition
  ⊞ (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ) 0 ((⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ)

-- lemma 19.1
/-private-/ lemma matrix3sumCompositionCanonicalSigning_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- assumptions
    ∀ hBₗ' : |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
             |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ ,
    ∀ hBᵣ' : |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
             |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ ,
    -- two just-constructed rows
    let ⟨r₀, r₁, _⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    ((⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) = c₀ ⊗ r₀ + c₁ ⊗ r₁ :=
  sorry

-- lemma 19.2
/-private-/ lemma matrix3sumCompositionCanonicalSigning_D_rows {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY
    -- assumptions
    ∀ hBₗ' : |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
             |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ ,
    ∀ hBᵣ' : |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
             |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ ,
    -- three just-constructed rows
    let ⟨r₀, r₁, r₂⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    ∀ i, D i = r₀ ∨ D i = -r₀ ∨ D i = r₁ ∨ D i = -r₁ ∨ D i = r₂ ∨ D i = -r₂ ∨ D i = 0 :=
  sorry

-- lemma 19.3
/-private-/ lemma matrix3sumCompositionCanonicalSigning_D_cols {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    ∀ j, (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀ ∨ (D · j) = 0 :=
  sorry


-- ## Total unimodularity of constituents

-- lemma 19.5
/-private-/ lemma matrix3sumCompositionCanonicalSigning_Aᵣ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bᵣ.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ ◫ (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY).IsTotallyUnimodular :=
  sorry

-- lemma 19.7
/-private-/ lemma matrix3sumCompositionCanonicalSigning_Aₗ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- assumptions
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₀ ∨
    |Bₗ'.submatrix3x3 x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ| = matrix3x3unsigned₁ →
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₀ ∨
    |Bᵣ'.submatrix3x3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ| = matrix3x3unsigned₁ →
    -- the actual statement
    (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ ⊟ (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY).IsTotallyUnimodular := by
  sorry
