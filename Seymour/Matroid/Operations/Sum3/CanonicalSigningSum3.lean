import Seymour.Matrix.Determinants
import Seymour.Matroid.Operations.Sum3.CanonicalSigning


/-! # Canonical signing of 3-sum of matrices -/

/-! ## Additional notation for special rows and columns and their properties -/

/-- First special column of `S.Bᵣ` used to generate `S.D`. -/
@[simp]
abbrev MatrixSum3.c₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Fin 2 ⊕ Xᵣ → F :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 0)

/-- Second special column of `S.Bᵣ` used to generate `S.D`. -/
@[simp]
abbrev MatrixSum3.c₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Fin 2 ⊕ Xᵣ → F :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 1)

/-- First special row of `S.Bₗ` used to generate `S.D`. -/
@[simp]
abbrev MatrixSum3.d₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Yₗ ⊕ Fin 2 → F :=
  (S.Dₗ ◫ S.D₀ₗ) 0

/-- Second special row of `S.Bₗ` used to generate `S.D`. -/
@[simp]
abbrev MatrixSum3.d₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Yₗ ⊕ Fin 2 → F :=
  (S.Dₗ ◫ S.D₀ₗ) 1

/-- Property of a vector to be in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`. -/
abbrev VecIsParallel3 {X F : Type} [Zero F] [Neg F] (v : X → F) (c₀ c₁ c₂ : X → F) : Prop :=
  v = 0 ∨ v = c₀ ∨ v = -c₀ ∨ v = c₁ ∨ v = -c₁ ∨ v = c₂ ∨ v = -c₂

/-- If a vector is in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`, then its opposite belongs to the same set. -/
lemma VecIsParallel3.neg {X F : Type} [Field F] {v : X → F} {c₀ c₁ c₂ : X → F}
    (hv : VecIsParallel3 v c₀ c₁ c₂) :
    VecIsParallel3 (-v) c₀ c₁ c₂ := by
  rcases hv with (hv | hv | hv | hv | hv | hv | hv)
  all_goals
    rw [hv]
    ring_nf
    simp only [VecIsParallel3, true_or, or_true]

/-- If a vector is in `{0, c₀, -c₀, c₁, -c₁, c₂, -c₂}`, then scaling it by a `{0, ±1}` factor keeps it by the same set. -/
lemma VecIsParallel3.mul_sign {X F : Type} [Field F] {v : X → F} {c₀ c₁ c₂ : X → F}
    (hv : VecIsParallel3 v c₀ c₁ c₂) {q : F} (hq : q ∈ SignType.cast.range) :
    VecIsParallel3 (fun i : X => v i * q) c₀ c₁ c₂ := by
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


/-! ## Main definitions -/

/-- Sufficient condition for existence of a canonical signing of a 3-sum of matrices over `Z2`. -/
def MatrixSum3.HasCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  (S.Bₗ.HasTuSigning ∧ S.Bᵣ.HasTuSigning)
  ∧ ((S.Sₗ = matrix3x3unsigned₀ Z2 ∧ S.Sᵣ = matrix3x3unsigned₀ Z2) ∨
     (S.Sₗ = matrix3x3unsigned₁ Z2 ∧ S.Sᵣ = matrix3x3unsigned₁ Z2))

/-- Proposition that `S` is a canonical signing of a 3-sum of matrices. -/
def MatrixSum3.IsCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  (S.Bₗ.IsTotallyUnimodular ∧ S.Bᵣ.IsTotallyUnimodular)
  ∧ ((S.Sₗ = matrix3x3signed₀ ∧ S.Sᵣ = matrix3x3signed₀) ∨
     (S.Sₗ = matrix3x3signed₁ ∧ S.Sᵣ = matrix3x3signed₁))

/-- Canonically re-signs the left summand of a 3-sum. -/
noncomputable abbrev Matrix.HasTuSigning.toCanonicalSummandₗ {Xₗ Yₗ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ]
    {Bₗ : Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) Z2} (hBₗ : Bₗ.HasTuSigning) :
    Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) ℚ :=
  hBₗ.choose.toCanonicalSigning ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0

/-- Canonically re-signs the right summand of a 3-sum. -/
noncomputable abbrev Matrix.HasTuSigning.toCanonicalSummandᵣ {Xᵣ Yᵣ : Type} [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Bᵣ : Matrix (Fin 1 ⊕ Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ Fin 1 ⊕ Yᵣ) Z2} (hBᵣ : Bᵣ.HasTuSigning) :
    Matrix (Fin 1 ⊕ Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ Fin 1 ⊕ Yᵣ) ℚ :=
  hBᵣ.choose.toCanonicalSigning ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0

/-- Canonical re-signing of a 3-sum of matrices over `Z2`. -/
noncomputable def MatrixSum3.HasCanonicalSigning.toCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ :=
  MatrixSum3.fromBlockSummands hS.left.left.toCanonicalSummandₗ hS.left.right.toCanonicalSummandᵣ


/-! ## Soundness of definitions -/

/-!
  In this section we prove that `MatrixSum3.HasCanonicalSigning.toCanonicalSigning` satisfies `IsCanonicalSigning`.
-/

lemma MatrixSum3.HasCanonicalSigning.summands_HasTuCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2}
    (hS : S.HasCanonicalSigning) :
    (hS.left.left.choose.HasTuCanonicalSigning₀ ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0
     ∧ hS.left.right.choose.HasTuCanonicalSigning₀ ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0)
    ∨ (hS.left.left.choose.HasTuCanonicalSigning₁ ◪0 ◪1 ◩◪0 ◩◪0 ◩◪1 ◪0
       ∧ hS.left.right.choose.HasTuCanonicalSigning₁ ◪◩0 ◪◩1 ◩0 ◩0 ◩1 ◪◩0) := by
  rcases hS.right with hSr | hSr
  <;> [left; right]
  all_goals constructor
  <;> [have htu := hS.left.left.choose_spec.left; have htu := hS.left.right.choose_spec.left]
  <;> [have heq := hSr.left; have heq := hSr.right]
  <;> [have hsgn := hS.left.left.choose_spec.right; have hsgn := hS.left.right.choose_spec.right]
  all_goals
    constructor
    · exact htu
    ext i j
    have h := congr_fun₂ heq i j
    fin_cases i <;> fin_cases j <;> simp at h <;> simp [Matrix.abs, h, hsgn _ _]

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bₗ = hS.left.left.toCanonicalSummandₗ := by
  unfold MatrixSum3.HasCanonicalSigning.toCanonicalSigning
  rw [MatrixSum3.fromBlockSummands_Bₗ_eq]
  rcases hS.summands_HasTuCanonicalSigning with h | h
  all_goals
    simp only [Matrix.HasTuSigning.toCanonicalSummandₗ, Matrix.HasTuSigning.toCanonicalSummandᵣ]
    constructor
    · have h1 := congr_fun₂ h.left.toCanonicalSigning_submatrix3x3 0 2
      have h2 := congr_fun₂ h.right.toCanonicalSigning_submatrix3x3 0 2
      simp at h1 h2
      rw [h1, h2]
    · constructor
      · have h1 := congr_fun₂ h.left.toCanonicalSigning_submatrix3x3 1 2
        have h2 := congr_fun₂ h.right.toCanonicalSigning_submatrix3x3 1 2
        simp at h1 h2
        rw [h1, h2]
      · intro i
        cases i with
        | inl iₗ =>
          simp [Matrix.toCanonicalSigning]
          left
          exact abs_eq_zero.→ (hS.left.left.choose_spec.right ◩◩iₗ ◪0)
        | inr iᵣ =>
          fin_cases iᵣ
          have h1 := congr_fun₂ h.left.toCanonicalSigning_submatrix3x3 2 2
          simp at h1
          exact h1

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bᵣ = hS.left.right.toCanonicalSummandᵣ := by
  unfold MatrixSum3.HasCanonicalSigning.toCanonicalSigning
  rw [MatrixSum3.fromBlockSummands_Bᵣ_eq]
  rcases hS.summands_HasTuCanonicalSigning with h | h
  all_goals
    simp only [Matrix.HasTuSigning.toCanonicalSummandₗ, Matrix.HasTuSigning.toCanonicalSummandᵣ]
    constructor
    · have h1 := congr_fun₂ h.left.toCanonicalSigning_submatrix3x3 2 0
      have h2 := congr_fun₂ h.right.toCanonicalSigning_submatrix3x3 2 0
      simp at h1 h2
      rw [h1, h2]
    · constructor
      · have h1 := congr_fun₂ h.left.toCanonicalSigning_submatrix3x3 2 1
        have h2 := congr_fun₂ h.right.toCanonicalSigning_submatrix3x3 2 1
        simp at h1 h2
        rw [h1, h2]
      · intro i
        cases i with
        | inl iₗ =>
          fin_cases iₗ
          have h2 := congr_fun₂ h.right.toCanonicalSigning_submatrix3x3 2 2
          simp at h2
          exact h2
        | inr iᵣ =>
          simp [Matrix.toCanonicalSigning]
          exact abs_eq_zero.→ (hS.left.right.choose_spec.right ◩0 ◪◪iᵣ)

/-- Canonical re-signing transforms a 3-sum of matrices into its canonically signed version. -/
lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_isCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.IsCanonicalSigning := by
  constructor
  · rw [MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq, MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq]
    constructor
    · exact hS.left.left.choose_spec.left.toCanonicalSigning _ _ _ _ _ _
    · exact hS.left.right.choose_spec.left.toCanonicalSigning _ _ _ _ _ _
  · unfold MatrixSum3.Sₗ MatrixSum3.Sᵣ
    rw [MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_eq, MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bᵣ_eq]
    rcases hS.summands_HasTuCanonicalSigning with h | h <;> [left; right]
    all_goals
      exact ⟨h.left.toCanonicalSigning_submatrix3x3, h.right.toCanonicalSigning_submatrix3x3⟩


/-! ## Lemmas about extending bottom-right block with special columns and top-left block with special rows -/

lemma MatrixSum3.HasTuBᵣ.special_form_cols {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    ∀ i : Fin 2 ⊕ Xᵣ, ![S.c₀ i, S.c₁ i] ≠ ![1, -1] ∧ ![S.c₀ i, S.c₁ i] ≠ ![-1, 1] := by
  intro i
  have := hS.det ![◪i, ◩0] ![◩0, ◩1]
  constructor
  <;> intro contr
  <;> have := congr_fun contr 0
  <;> have := congr_fun contr 1
  <;> simp_all [Matrix.det_fin_two]

lemma MatrixSum3.HasTuBᵣ.c₀_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  let B : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) ℚ := S.Bᵣ.shortTableauPivot ◩0 ◩0
  let B' : Matrix (Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) ℚ := B.submatrix Sum.inr id
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
  let q : (Unit ⊕ Unit) ⊕ (Fin 1 ⊕ Yᵣ) → ℚ := (·.casesOn (-1) 1)
  have hq : ∀ i : (Unit ⊕ Unit) ⊕ (Fin 1 ⊕ Yᵣ), q i ∈ SignType.cast.range
  · rintro (_|_) <;> simp [q]
  convert hScc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

lemma MatrixSum3.HasTuBᵣ.c₂_c₁_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮(S.c₀ - S.c₁) ◫ ▮S.c₁ ◫ S.Aᵣ).IsTotallyUnimodular := by
  let B : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) ℚ := S.Bᵣ.shortTableauPivot ◩0 ◩1
  let B' : Matrix (Fin 2 ⊕ Xᵣ) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) ℚ := B.submatrix Sum.inr id
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
  let q : (Unit ⊕ Unit) ⊕ (Fin 1 ⊕ Yᵣ) → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
  have hq : ∀ i : (Unit ⊕ Unit) ⊕ (Fin 1 ⊕ Yᵣ), q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hScc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

lemma MatrixSum3.HasTuBᵣ.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  intro k f g hf hg
  if hgc₂ : ∃ j, g j = ◩◪() then -- `c₂` is contained in the submatrix
    obtain ⟨j₂, hj₂⟩ := hgc₂
    if hgc₀ : ∃ j, g j = ◩◩◩() then -- `c₀` is contained in the submatrix
      obtain ⟨j₀, hj₀⟩ := hgc₀
      if hgc₁ : ∃ j, g j = ◩◩◪() then -- `c₁` is contained in the submatrix
        obtain ⟨j₁, hj₁⟩ := hgc₁
        use 0
        symm
        apply ((▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).submatrix f g).det_eq_zero_of_col_sub_col_eq_col j₀ j₁ j₂
        simp [hj₀, hj₁, hj₂]
        rfl
      else
        convert (hS.c₀_c₂_Aᵣ_isTotallyUnimodular hSAₗ).det f ((·.map (·.casesOn (·.casesOn Sum.inl Sum.inl) Sum.inr) id) ∘ g)
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
      convert (hS.c₂_c₁_Aᵣ_isTotallyUnimodular hSAₗ).det f ((·.map (·.casesOn (·.casesOn Sum.inr Sum.inr) Sum.inl) id) ∘ g)
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
    let f' : Fin k → Fin 1 ⊕ (Fin 2 ⊕ Xᵣ) := Sum.inr ∘ f
    let g' : Fin k → Fin 2 ⊕ (Fin 1 ⊕ Yᵣ) := (·.map (·.casesOn equivUnitSumUnit ↓0) id) ∘ g
    convert hS.det f' g'
    ext i j
    cases hgj : g j with
    | inl z₃ => cases z₃ with
      | inl z₂ => cases z₂ <;> simp [hgj, f', g']
      | inr => tauto
    | inr z₁ => cases z₁ <;> simp [hgj, f', g']

lemma MatrixSum3.HasTuBᵣ.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮S.c₀ ◫ ▮S.c₀ ◫ ▮S.c₁ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular := by
  convert (hS.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular hSAₗ).comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ (Fin 1 ⊕ Yᵣ)) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩()) ↓◩◩◩()) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) Sum.inr))
  aesop

lemma MatrixSum3.HasTuBᵣ.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) (hSAₗ : S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1) :
    (▮0 ◫ (▮S.c₀ ◫ ▮(-S.c₀) ◫ ▮S.c₁ ◫ ▮(-S.c₁) ◫ ▮(S.c₀ - S.c₁) ◫ ▮(S.c₁ - S.c₀) ◫ S.Aᵣ)).IsTotallyUnimodular := by
  convert ((hS.c₀_c₀_c₁_c₁_c₂_c₂_Aᵣ_isTotallyUnimodular hSAₗ).mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

lemma MatrixSum3.HasTuBₗ.pmz_d₀_d₁_d₂_Aₗ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ] {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBₗ) (hSAᵣ : S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1) :
    (▬0 ⊟ (▬S.d₀ ⊟ ▬(-S.d₀) ⊟ ▬S.d₁ ⊟ ▬(-S.d₁) ⊟ ▬(S.d₀ - S.d₁) ⊟ ▬(S.d₁ - S.d₀) ⊟ S.Aₗ)).IsTotallyUnimodular := by
  have hS' : S.transpose.HasTuBᵣ
  · simp only [MatrixSum3.HasTuBₗ, MatrixSum3.Bₗ] at hS
    simp only [MatrixSum3.HasTuBᵣ, MatrixSum3.Bᵣ, MatrixSum3.transpose]
    convert hS.transpose.submatrix (Sum.map Sum.swap id ∘ Sum.swap) (Sum.map Sum.swap id ∘ Sum.swap)
    ext (_|_|_) (j | _)
    · fin_cases j <;> simp
    all_goals simp
  rw [←Matrix.transpose_isTotallyUnimodular_iff]
  convert (hS'.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular hSAᵣ).submatrix Sum.swap (Sum.map id (Sum.map id Sum.swap))
  aesop

/-- Lemma 55.1 -/
lemma MatrixSum3.HasTuBₗ.special_form_cols {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBₗ) (hSAᵣ : S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1) :
    ∀ i : Yₗ ⊕ Fin 2, ![S.d₀ i, S.d₁ i] ≠ ![1, -1] ∧ ![S.d₀ i, S.d₁ i] ≠ ![-1, 1] := by
  intro i
  have := hS.det (Z := Fin 2) ![◪0, ◪1] ![◩i, ◪0] --![◩0, ◩1] ![◪i, ◩0]
  constructor
  <;> intro contr
  <;> have := congr_fun contr 0
  <;> have := congr_fun contr 1
  <;> simp_all [Matrix.det_fin_two]


/-! ## Properties of canonical signings of 3-sums -/

lemma MatrixSum3.IsCanonicalSigning.hSAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    S.Aₗ ◪0 ◪0 = 1 ∧ S.Aₗ ◪0 ◪1 = 1 := by
  rcases hS.right with hSS | hSS
  <;> exact ⟨congr_fun₂ hSS.left 2 0, congr_fun₂ hSS.left 2 1⟩

lemma MatrixSum3.IsCanonicalSigning.hSAᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    S.Aᵣ ◩0 ◩0 = 1 ∧ S.Aᵣ ◩1 ◩0 = 1 := by
  rcases hS.right with hSS | hSS
  <;> exact ⟨congr_fun₂ hSS.right 0 2, congr_fun₂ hSS.right 1 2⟩

/-- The bottom-left block of a canonical signing of a 3-sum of matrices in the first special case. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
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
lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (hSₗ₁ : S.Sₗ = matrix3x3signed₁) :
    S.D = S.c₀ ⊗ S.d₀ - S.c₀ ⊗ S.d₁ + S.c₁ ⊗ S.d₁ := by
  have hSᵣ₀ : S.Sᵣ = matrix3x3signed₁
  · cases hS.right with
    | inl h =>
      exfalso
      have contr := congr_fun₂ (h.left ▸ hSₗ₁) 1 1
      simp at contr
      clear * - contr
      linarith
    | inr h => exact h.right
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

/-- Every col of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±c₀, ±c₁, ±c₂}`. Lemma 56.3. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_cols {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning)
    (j : Yₗ ⊕ Fin 2) :
    VecIsParallel3 (S.D · j) S.c₀ S.c₁ (S.c₀ - S.c₁) := by
  have hTuBₗ : S.HasTuBₗ := hS.left.left
  have h19 := hTuBₗ.special_form_cols hS.hSAᵣ j
  rcases hS.right with ⟨hDₗ, hDᵣ⟩ | ⟨hDₗ, hDᵣ⟩
  on_goal 1 => have hD := hS.D_eq_sum_outer₀ hDₗ
  on_goal 2 => have hD := hS.D_eq_sum_outer₁ hDₗ
  all_goals
    simp_rw [hD]
    obtain ⟨y, hy⟩ : S.d₀ j ∈ SignType.cast.range := hS.left.left.apply ◪0 ◩j
    obtain ⟨z, hz⟩ : S.d₁ j ∈ SignType.cast.range := hS.left.left.apply ◪1 ◩j
    eta_expand
    rcases y <;> rcases z
    <;> simp only [SignType.pos_eq_one, SignType.coe_one, SignType.zero_eq_zero,
      SignType.coe_zero, SignType.neg_eq_neg_one, SignType.coe_neg] at hy hz
    <;> simp [-c₀, -c₁, ←hy, ←hz, VecIsParallel3, Pi.zero_def, Pi.neg_def, sub_eq_add_neg] at h19 ⊢
    repeat right
    ext
    abel

/-- Every row of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±d₀, ±d₁, ±d₂}`. Lemma 56.4. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_rows {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning)
    (i : Fin 2 ⊕ Xᵣ) :
    VecIsParallel3 (S.D i) S.d₀ S.d₁ (S.d₀ - S.d₁) := by
  have hTuBᵣ : S.HasTuBᵣ := hS.left.right
  have h19 := hTuBᵣ.special_form_cols hS.hSAₗ i
  rcases hS.right with ⟨hDₗ, hDᵣ⟩ | ⟨hDₗ, hDᵣ⟩
  on_goal 1 => have hD := hS.D_eq_sum_outer₀ hDₗ
  on_goal 2 => have hD := hS.D_eq_sum_outer₁ hDₗ
  all_goals
    simp_rw [hD]
    obtain ⟨y, hy⟩ : S.c₀ i ∈ SignType.cast.range := hS.left.right.apply ◪i ◩0
    obtain ⟨z, hz⟩ : S.c₁ i ∈ SignType.cast.range := hS.left.right.apply ◪i ◩1
    eta_expand
    rcases y <;> rcases z
    <;> simp only [SignType.pos_eq_one, SignType.coe_one, SignType.zero_eq_zero,
      SignType.coe_zero, SignType.neg_eq_neg_one, SignType.coe_neg] at hy hz
    <;> simp [-c₀, -c₁, ←hy, ←hz, VecIsParallel3, Pi.zero_def, Pi.neg_def, sub_eq_add_neg] at h19 ⊢
    repeat right
    ext
    abel

/-- The left block of a canonical signing of a 3-sum of matrices is totally unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.Aₗ_D_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (hS : S.IsCanonicalSigning) :
    (S.Aₗ ⊟ S.D).IsTotallyUnimodular := by
  classical
  let e : ((Xₗ ⊕ Fin 1) ⊕ Fin 2 ⊕ Xᵣ → (Unit ⊕ (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Xₗ ⊕ Fin 1)) :=
    (·.casesOn
      (Sum.inr ∘ Sum.inr)
      fun j : Fin 2 ⊕ Xᵣ =>
        if h0 : S.D j = 0 then ◩() else
        if hpc₀ : S.D j = S.d₀ then ◪◩◩◩◩◩◩() else
        if hmc₀ : S.D j = -S.d₀ then ◪◩◩◩◩◩◪() else
        if hpc₁ : S.D j = S.d₁ then ◪◩◩◩◩◪() else
        if hmc₁ : S.D j = -S.d₁ then ◪◩◩◩◪() else
        if hpc₂ : S.D j = S.d₀ - S.d₁ then ◪◩◩◪() else
        if hmc₂ : S.D j = S.d₁ - S.d₀ then ◪◩◪() else
        False.elim (have := hS.D_eq_rows j; by aesop))
  convert (MatrixSum3.HasTuBₗ.pmz_d₀_d₁_d₂_Aₗ_isTotallyUnimodular hS.left.left hS.hSAᵣ).submatrix e id
  ext i j
  cases i with
  | inl => rfl
  | inr i =>
    simp only [Matrix.fromRows_apply_inr, Matrix.replicateRow_zero, Fin.isValue, Matrix.submatrix_apply, id_eq]
    wlog h0 : ¬ S.D i = 0
    · rw [not_not] at h0
      simp [e, h0, congr_fun h0 j]
    wlog hpd₀ : ¬ S.D i = S.d₀
    · rw [not_not] at hpd₀
      simp only [e, h0]
      simp [hpd₀, congr_fun hpd₀ j]
    wlog hmd₀ : ¬ S.D i = -S.d₀
    · rw [not_not] at hmd₀
      simp only [e, h0, hpd₀]
      simp [hmd₀, congr_fun hmd₀ j]
    wlog hpd₁ : ¬ S.D i = S.d₁
    · rw [not_not] at hpd₁
      simp only [e, h0, hpd₀, hmd₀]
      simp [hpd₁, congr_fun hpd₁ j]
    wlog hmd₁ : ¬ S.D i = -S.d₁
    · rw [not_not] at hmd₁
      simp only [e, h0, hpd₀, hmd₀, hpd₁]
      simp [hmd₁, congr_fun hmd₁ j]
    wlog hpd₂ : ¬ S.D i = S.d₀ - S.d₁
    · rw [not_not] at hpd₂
      simp only [e, h0, hpd₀, hmd₀, hpd₁, hmd₁]
      simp [hpd₂, congr_fun hpd₂ j]
    wlog hmd₂ : ¬ S.D i = S.d₁ - S.d₀
    · rw [not_not] at hmd₂
      simp only [e, h0, hpd₀, hmd₀, hpd₁, hmd₁, hpd₂]
      simp [hmd₂, congr_fun hmd₂ j]
    exfalso
    have hSd := hS.D_eq_rows i
    rw [VecIsParallel3, neg_sub] at hSd
    tauto

/-- The extension of the bottom-right block of a canonical signing of a 3-sum of matrices with special columns is totally
    unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮(S.c₀ - S.c₁) ◫ S.Aᵣ).IsTotallyUnimodular :=
  MatrixSum3.HasTuBᵣ.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular hS.left.right hS.hSAₗ


/-! ## Correcntess -/

/-!
  In this section we prove that `MatrixSum3.HasCanonicalSigning.toCanonicalSigning` is indeed a signing of the original 3-sum.
-/

lemma Matrix.toCanonicalSigning_apply_abs' {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (Q : Matrix X Y ℚ) {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₀ ℚ
        ∨ |Q.submatrix ![x₀, x₁, x₂] ![y₀, y₁, y₂]| = matrix3x3unsigned₁ ℚ)
    (i : X) (j : Y) :
    |(Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂) i j| = |Q i j| := by
  rcases hQ with (hQ | hQ)
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

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Bₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bₗ.IsSigningOf S.Bₗ := by
  rw [hS.toCanonicalSigning_Bₗ_eq]
  have hBₗ' := hS.left.left.choose_spec.right
  intro i j
  convert hS.left.left.choose.toCanonicalSigning_apply_abs' ?_ i j
  · exact (hBₗ' i j).symm
  · rcases hS.right with ⟨hSS, _⟩ | ⟨hSS, _⟩ <;> [left; right]
    all_goals
      ext i j
      have hBₗ'ij := hBₗ' (![◪0, ◪1, ◩◪0] i) (![◩◪0, ◩◪1, ◪0] j)
      have hSSij := congr_fun₂ hSS i j
      fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.abs] at hBₗ'ij hSSij ⊢
      try rw [hSSij] at hBₗ'ij
      try simp at hBₗ'ij
      rw [hBₗ'ij]

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_isSigningBᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Bᵣ.IsSigningOf S.Bᵣ := by
  rw [hS.toCanonicalSigning_Bᵣ_eq]
  have hBᵣ' := hS.left.right.choose_spec.right
  intro i j
  convert hS.left.right.choose.toCanonicalSigning_apply_abs' ?_ i j
  · exact (hBᵣ' i j).symm
  · rcases hS.right with ⟨_, hSS⟩ | ⟨_, hSS⟩ <;> [left; right]
    all_goals
      ext i j
      have hBᵣ'ij := hBᵣ' (![◪◩0, ◪◩1, ◩0] i) (![◩0, ◩1, ◪◩0] j)
      have hSSij := congr_fun₂ hSS i j
      fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.abs] at hBᵣ'ij hSSij ⊢
      try rw [hSSij] at hBᵣ'ij
      try simp at hBᵣ'ij
      rw [hBᵣ'ij]

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Aₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Aₗ.IsSigningOf S.Aₗ := by
  intro i j
  exact hS.toCanonicalSigning_Bₗ_isSigning ◩i ◩j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Dₗ.IsSigningOf S.Dₗ := by
  intro i j
  exact hS.toCanonicalSigning_Bₗ_isSigning ◪i ◩◩j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ₗ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ₗ.IsSigningOf S.D₀ₗ := by
  intro i j
  exact hS.toCanonicalSigning_Bₗ_isSigning ◪i ◩◪j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Aᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Aᵣ.IsSigningOf S.Aᵣ := by
  intro i j
  exact hS.toCanonicalSigning_isSigningBᵣ ◪i ◪j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_Dᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.Dᵣ.IsSigningOf S.Dᵣ := by
  intro i j
  exact hS.toCanonicalSigning_isSigningBᵣ ◪◪i ◩j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ᵣ.IsSigningOf S.D₀ᵣ := by
  intro i j
  exact hS.toCanonicalSigning_isSigningBᵣ ◪◩i ◩j

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ₗ = !![1, 0; 0, -1] ∨ hS.toCanonicalSigning.D₀ₗ = !![1, 1; 0, 1] := by
  rcases hS.toCanonicalSigning_isCanonicalSigning.right with ⟨hSₗ, _⟩ | ⟨hSₗ, _⟩
  <;> [left; right]
  all_goals
    ext i j
    have hSₗij := congr_fun₂ hSₗ i j
    fin_cases i <;> fin_cases j <;> exact hSₗij

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ᵣ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ᵣ = !![1, 0; 0, -1] ∨ hS.toCanonicalSigning.D₀ᵣ = !![1, 1; 0, 1] := by
  rcases hS.toCanonicalSigning_isCanonicalSigning.right with ⟨_, hSᵣ⟩ | ⟨_, hSᵣ⟩
  <;> [left; right]
  all_goals
    ext i j
    have hSᵣij := congr_fun₂ hSᵣ i j
    fin_cases i <;> fin_cases j <;> exact hSᵣij

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D₀ₗ_eq_D₀ᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.D₀ₗ = hS.toCanonicalSigning.D₀ᵣ := by
  rcases hS.toCanonicalSigning_isCanonicalSigning.right with ⟨hSₗ, hSᵣ⟩ | ⟨hSₗ, hSᵣ⟩
  all_goals
    ext i j
    have hSₗij := congr_fun₂ hSₗ i j
    have hSᵣij := congr_fun₂ hSᵣ i j
    fin_cases i <;> fin_cases j <;> simp at hSₗij hSᵣij <;> simp [hSₗij, hSᵣij]

lemma signing_mul {a' b' : ℚ} {a b : Z2}
    (haa : |a'| = a.val) (hbb : |b'| = b.val) : |a' * b'| = (a * b).val := by
  rcases Z2_eq_0_or_1 a with ha | ha
  <;> rcases Z2_eq_0_or_1 b with hb | hb
  all_goals
    rw [ha] at haa ⊢
    rw [hb] at hbb ⊢
    rw [abs_mul, haa, hbb]
    simp

lemma MatrixSum3.HasCanonicalSigning.summands_submatrix3x3 {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2}
    (hS : S.HasCanonicalSigning) :
    (|hS.left.left.choose.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]| = matrix3x3unsigned₀ ℚ
     ∧ |hS.left.right.choose.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]| = matrix3x3unsigned₀ ℚ)
    ∨ (|hS.left.left.choose.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]| = matrix3x3unsigned₁ ℚ
      ∧ |hS.left.right.choose.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]| = matrix3x3unsigned₁ ℚ) := by
  rcases hS.right with hSr | hSr
  <;> [left; right]
  all_goals constructor
  <;> [have heq := hSr.left; have heq := hSr.right]
  <;> [have hsgn := hS.left.left.choose_spec.right; have hsgn := hS.left.right.choose_spec.right]
  all_goals
    ext i j
    have hSij := congr_fun₂ heq i j
    fin_cases i <;> fin_cases j <;> simp at hSij <;> simp [Matrix.abs, hSij, hsgn _ _]

private lemma pn_inv_eq_self {a : ℚ} (ha : a = 1 ∨ a = -1) : a⁻¹ = a :=
  ha.casesOn (· ▸ inv_one) (· ▸ inv_neg_one)

private lemma pn_pow_2 {a : ℚ} (ha : a = 1 ∨ a = -1) : a ^ 2 = 1 :=
  sq_eq_one_iff.← ha

private lemma pn_pow_5 {a : ℚ} (ha : a = 1 ∨ a = -1) : a ^ 5 = a :=
  ha.casesOn (· ▸ rfl) (· ▸ rfl)

private lemma pn_pow_6 {a : ℚ} (ha : a = 1 ∨ a = -1) : a ^ 6 = 1 :=
  ha.casesOn (by rw [·]; exact rfl) (· ▸ rfl)

lemma zmodval_in_SignTypeCastRange (x : Z2) :
    (x.val.cast : ℚ) ∈ SignType.cast.range := by
  rcases Z2_eq_0_or_1 x with h | h
  <;> rw [h]
  <;> [use SignType.zero; use SignType.pos]
  <;> rfl

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSIgning_c₀_in_SignTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    ∀ iᵣ, hS.toCanonicalSigning.c₀ iᵣ ∈ SignType.cast.range := by
  intro iᵣ
  rw [MatrixSum3.c₀, in_signTypeCastRange_iff_abs]
  cases iᵣ with
  | inl i₀ =>
    rw [Matrix.fromRows_apply_inl, hS.toCanonicalSigning_D₀ᵣ_isSigning i₀ 0]
    exact zmodval_in_SignTypeCastRange (S.D₀ᵣ i₀ 0)
  | inr iᵣ =>
    rw [Matrix.fromRows_apply_inr, hS.toCanonicalSigning_Dᵣ_isSigning iᵣ 0]
    exact zmodval_in_SignTypeCastRange (S.Dᵣ iᵣ 0)

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSIgning_c₁_in_SignTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    ∀ iᵣ, hS.toCanonicalSigning.c₁ iᵣ ∈ SignType.cast.range := by
  intro iᵣ
  rw [MatrixSum3.c₁, in_signTypeCastRange_iff_abs]
  cases iᵣ with
  | inl i₀ =>
    rw [Matrix.fromRows_apply_inl, hS.toCanonicalSigning_D₀ᵣ_isSigning i₀ 1]
    exact zmodval_in_SignTypeCastRange (S.D₀ᵣ i₀ 1)
  | inr iᵣ =>
    rw [Matrix.fromRows_apply_inr, hS.toCanonicalSigning_Dᵣ_isSigning iᵣ 1]
    exact zmodval_in_SignTypeCastRange (S.Dᵣ iᵣ 1)

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSIgning_c₂_in_SignTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    ∀ iᵣ, (hS.toCanonicalSigning.c₀ - hS.toCanonicalSigning.c₁) iᵣ ∈ SignType.cast.range := by
  intro iᵣ
  rw [Pi.sub_apply]
  have hSBᵣ : hS.toCanonicalSigning.HasTuBᵣ := hS.toCanonicalSigning_isCanonicalSigning.left.right
  have hc₀c₁ := hSBᵣ.special_form_cols hS.toCanonicalSigning_isCanonicalSigning.hSAₗ iᵣ
  obtain ⟨s₀, hs₀⟩ := hS.toCanonicalSIgning_c₀_in_SignTypeCastRange iᵣ
  obtain ⟨s₁, hs₁⟩ :=  hS.toCanonicalSIgning_c₁_in_SignTypeCastRange iᵣ
  cases s₀ <;> cases s₁ <;> simp [←hs₀, ←hs₁] at hc₀c₁ ⊢

lemma neg_in_signTypeCastRange_iff {x : ℚ} : -x ∈ SignType.cast.range ↔ x ∈ SignType.cast.range :=
  ⟨fun hx => in_signTypeCastRange_of_neg hx, fun hx => neg_in_signTypeCastRange hx⟩

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSIgning_Dₗᵣ_in_SignTypeCastRange {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Xᵣ) (jₗ : Yₗ) :
    hS.toCanonicalSigning.D ◪iᵣ ◩jₗ ∈ SignType.cast.range := by
  rcases hS.toCanonicalSigning_isCanonicalSigning.D_eq_cols ◩jₗ with hc | hc | hc | hc | hc | hc | hc
  <;> rw [congr_fun hc ◪iᵣ]
  · exact zero_in_signTypeCastRange
  · exact hS.toCanonicalSIgning_c₀_in_SignTypeCastRange ◪iᵣ
  · rw [Pi.neg_apply, neg_in_signTypeCastRange_iff]
    exact hS.toCanonicalSIgning_c₀_in_SignTypeCastRange ◪iᵣ
  · exact hS.toCanonicalSIgning_c₁_in_SignTypeCastRange ◪iᵣ
  · rw [Pi.neg_apply, neg_in_signTypeCastRange_iff]
    exact hS.toCanonicalSIgning_c₁_in_SignTypeCastRange ◪iᵣ
  · exact hS.toCanonicalSIgning_c₂_in_SignTypeCastRange ◪iᵣ
  · rw [Pi.neg_apply, neg_in_signTypeCastRange_iff]
    exact hS.toCanonicalSIgning_c₂_in_SignTypeCastRange ◪iᵣ

lemma Z2_cast_mul (a b : Z2) : (ZMod.cast (a * b) : ℚ) = (ZMod.cast a : ℚ) * (ZMod.cast b : ℚ) := by
  cases Z2_eq_0_or_1 a <;> cases Z2_eq_0_or_1 b <;> simp [*]

lemma MatrixSum3.HasCanonicalSigning.choose_Dₗ_elem_mul_Dᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Xᵣ) (jₗ : Yₗ) (i₀ j₀ : Fin 2) :
    |hS.left.left.choose ◪i₀ ◩◩jₗ * hS.left.right.choose ◪◪iᵣ ◩j₀| = ZMod.cast (S.Dᵣ iᵣ j₀ * S.Dₗ i₀ jₗ) := by
  rw [abs_mul]
  have hDₗ' := hS.left.left.choose_spec.right ◪i₀ ◩◩jₗ
  have hDᵣ' := hS.left.right.choose_spec.right ◪◪iᵣ ◩j₀
  rw [Z2_cast_mul, hDₗ', hDᵣ']
  exact Rat.mul_comm ↑(ZMod.val (S.Dₗ i₀ jₗ)) ↑(ZMod.val (S.Dᵣ iᵣ j₀))

lemma MatrixSum3.HasCanonicalSigning.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) (iᵣ : Xᵣ) (jₗ : Yₗ) (i₀ j₀ : Fin 2) :
    |hS.toCanonicalSigning.Dₗ i₀ jₗ * hS.toCanonicalSigning.Dᵣ iᵣ j₀| = ZMod.cast (S.Dᵣ iᵣ j₀ * S.Dₗ i₀ jₗ) := by
  rw [abs_mul]
  have hDₗ' := hS.toCanonicalSigning_Dₗ_isSigning i₀ jₗ
  have hDᵣ' := hS.toCanonicalSigning_Dᵣ_isSigning iᵣ j₀
  rw [Z2_cast_mul, hDₗ', hDᵣ']
  exact Rat.mul_comm ↑(ZMod.val (S.Dₗ i₀ jₗ)) ↑(ZMod.val (S.Dᵣ iᵣ j₀))

lemma abs_add_eq_zmod_cast {a b : Z2} {a' b' : ℚ} (haa : |a'| = a.cast) (hbb : |b'| = b.cast)
    (hab : a' + b' ∈ SignType.cast.range) :
    |a' + b'| = (a + b).cast := by
  cases Z2_eq_0_or_1 a with
  | inl ha0 =>
    rw [ha0, ZMod.cast_zero, abs_eq_zero] at haa
    rw [ha0, haa, zero_add, zero_add, hbb]
  | inr ha1 =>
    cases Z2_eq_0_or_1 b with
    | inl hb0 =>
      rw [hb0, ZMod.cast_zero, abs_eq_zero] at hbb
      rw [hb0, hbb, add_zero, add_zero, haa]
    | inr hb1 =>
      rw [ha1, cast_1_fromZ2_toRat, abs_eq rfl] at haa
      rw [hb1, cast_1_fromZ2_toRat, abs_eq rfl] at hbb
      rw [ha1, hb1, show (1 : Z2) + (1 : Z2) = (0 : Z2) by rfl, ZMod.cast_zero, abs_eq_zero]
      rcases haa with ha' | ha' <;> rcases hbb with hb' | hb' -- @Martin: is using vanilla cases better here?
      all_goals
        simp only [ha', hb', add_neg_cancel, neg_add_cancel]
      all_goals
        exfalso
        rw [ha', hb', Set.mem_range] at hab
        obtain ⟨s, hs⟩ := hab
        cases s <;> norm_num at hs -- @Martin: close enough or optimize?

lemma abs_add_add_eq_zmod_cast {a b c : Z2} {a' b' c' : ℚ} (haa : |a'| = a.cast) (hbb : |b'| = b.cast) (hcc : |c'| = c.cast)
    (habc : a' + b' + c' ∈ SignType.cast.range) :
    |a' + b' + c'| = (a + b + c).cast := by
  cases Z2_eq_0_or_1 a with
  | inl ha0 =>
    rw [ha0, ZMod.cast_zero, abs_eq_zero] at haa
    rw [haa, zero_add] at habc ⊢
    rw [ha0, zero_add]
    exact abs_add_eq_zmod_cast hbb hcc habc
  | inr ha1 =>
    cases Z2_eq_0_or_1 b with
    | inl hb0 =>
      rw [hb0, ZMod.cast_zero, abs_eq_zero] at hbb
      rw [hbb, add_zero] at habc ⊢
      rw [hb0, add_zero]
      exact abs_add_eq_zmod_cast haa hcc habc
    | inr hb1 =>
      cases Z2_eq_0_or_1 c with
      | inl hc0 =>
        rw [hc0, ZMod.cast_zero, abs_eq_zero] at hcc
        rw [hcc, add_zero] at habc ⊢
        rw [hc0, add_zero]
        exact abs_add_eq_zmod_cast haa hbb habc
      | inr hc1 =>
        rw [ha1, cast_1_fromZ2_toRat, abs_eq rfl] at haa
        rw [hb1, cast_1_fromZ2_toRat, abs_eq rfl] at hbb
        rw [hc1, cast_1_fromZ2_toRat, abs_eq rfl] at hcc
        rw [ha1, hb1, hc1, show (1 : Z2) + (1 : Z2) + (1 : Z2) = (1 : Z2) by rfl, cast_1_fromZ2_toRat]
        rcases haa with ha' | ha' <;> rcases hbb with hb' | hb' <;> rcases hcc with hc' | hc'
        all_goals
          simp only [ha', hb', hc',
            add_neg_cancel, add_neg_cancel_right, neg_add_cancel, neg_add_cancel_right, zero_add, abs_one, abs_neg]
        all_goals
          exfalso
          rw [ha', hb', hc', Set.mem_range] at habc
          obtain ⟨s, hs⟩ := habc
          cases s <;> norm_num at hs

set_option maxHeartbeats 0 in
lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_D_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
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
      obtain ⟨s, hs⟩ := hS.toCanonicalSIgning_Dₗᵣ_in_SignTypeCastRange iᵣ jₗ
      rw [←hs]
      simp [Matrix.mul_apply] at hs ⊢
      cases hS.toCanonicalSigning_isCanonicalSigning.right with
      | inl hSS =>
        obtain ⟨hBₗ', hBᵣ'⟩ := hSS
        have hD₀ₗ : S.D₀ₗ = !![1, 0; 0, 1] := by
          ext i j
          have hD₀ₗij := hS.toCanonicalSigning_D₀ₗ_isSigning i j
          have hBₗ'ij := congr_fun₂ hBₗ' i j
          fin_cases i <;> fin_cases j
          <;> simp at hD₀ₗij hBₗ'ij ⊢
          <;> simp [hBₗ'ij] at hD₀ₗij
          <;> clear * - hD₀ₗij
          · cases Z2_eq_0_or_1 (S.D₀ₗ 0 0) <;> simp_all -- @Matrin: please fix this monstrosity
          · cases Z2_eq_0_or_1 (S.D₀ₗ 0 1) <;> simp_all
          · cases Z2_eq_0_or_1 (S.D₀ₗ 1 0) <;> simp_all
          · cases Z2_eq_0_or_1 (S.D₀ₗ 1 1) <;> simp_all
        have hD₀ₗ' : hS.toCanonicalSigning.D₀ₗ = !![1, 0; 0, -1] := by
          ext i j
          have hBₗ'ij := congr_fun₂ hBₗ' i j
          fin_cases i <;> fin_cases j <;> exact hBₗ'ij
        rw [hD₀ₗ]
        rw [hD₀ₗ'] at hs
        rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two] at hs ⊢
        simp [inv_neg] at hs ⊢
        rw [hs]
        apply abs_add_eq_zmod_cast
        · rw [mul_comm]
          exact hS.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning iᵣ jₗ 0 0
        · rw [abs_neg, mul_comm]
          exact hS.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning iᵣ jₗ 1 1
        · exact hs ▸ Set.mem_range_self s
      | inr hSS =>
        obtain ⟨hBₗ', hBᵣ'⟩ := hSS
        have hD₀ₗ : S.D₀ₗ = !![1, 1; 0, 1] := by
          ext i j
          have hD₀ₗij := hS.toCanonicalSigning_D₀ₗ_isSigning i j
          have hBₗ'ij := congr_fun₂ hBₗ' i j
          fin_cases i <;> fin_cases j
          <;> simp at hD₀ₗij hBₗ'ij ⊢
          <;> simp [hBₗ'ij] at hD₀ₗij
          <;> clear * - hD₀ₗij
          · cases Z2_eq_0_or_1 (S.D₀ₗ 0 0) <;> simp_all -- @Matrin: please fix this monstrosity
          · cases Z2_eq_0_or_1 (S.D₀ₗ 0 1) <;> simp_all
          · cases Z2_eq_0_or_1 (S.D₀ₗ 1 0) <;> simp_all
          · cases Z2_eq_0_or_1 (S.D₀ₗ 1 1) <;> simp_all
        rw [hD₀ₗ]
        have hD₀ₗ' : hS.toCanonicalSigning.D₀ₗ = !![1, 1; 0, 1] := by
          ext i j
          have hBₗ'ij := congr_fun₂ hBₗ' i j
          fin_cases i <;> fin_cases j <;> exact hBₗ'ij
        rw [hD₀ₗ'] at hs
        rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two] at hs ⊢
        simp [inv_neg] at hs ⊢
        simp [add_mul, ←add_assoc] at hs ⊢
        rw [hs]
        have habc : (s.cast : ℚ) ∈ SignType.cast.range := Set.mem_range_self s
        rw [hs] at habc
        have hDₗᵣ00 := hS.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning iᵣ jₗ 0 0
        rw [mul_comm] at hDₗᵣ00
        have hDₗᵣ01 := hS.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning iᵣ jₗ 1 0
        rw [mul_comm, ←abs_neg] at hDₗᵣ01
        have hDₗᵣ11 := hS.toCanonicalSIgning_Dₗ_elem_mul_Dᵣ_isSigning iᵣ jₗ 1 1
        rw [mul_comm] at hDₗᵣ11
        exact abs_add_add_eq_zmod_cast hDₗᵣ00 hDₗᵣ01 hDₗᵣ11 habc
    | inr jᵣ => exact hS.toCanonicalSigning_Dᵣ_isSigning iᵣ jᵣ

/-- Canonical re-signing yields a signing of the original 3-sum of marices. -/
lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning_isSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    hS.toCanonicalSigning.matrix.IsSigningOf S.matrix := by
  intro i j
  cases i <;> cases j
  · exact hS.toCanonicalSigning_Aₗ_isSigning _ _
  · rfl
  · exact hS.toCanonicalSigning_D_isSigning _ _
  · exact hS.toCanonicalSigning_Aᵣ_isSigning _ _
