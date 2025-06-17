import Seymour.Matroid.Operations.Sum3.CanonicalSigningSum3


/-! # Family of 3-sum-like matrices: new version -/

/-! ## Definition -/

/-- Structural data of 3-sum-like matrices. -/
-- todo: rename to `MatrixLikeSum3`
structure MatrixLikeSum3' (Xₗ Yₗ Xᵣ Yᵣ : Type) (c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ) where
  Aₗ   : Matrix Xₗ Yₗ ℚ
  D    : Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ
  Aᵣ   : Matrix (Fin 2 ⊕ Xᵣ) Yᵣ ℚ
  hAₗD : (Aₗ ⊟ D).IsTotallyUnimodular
  hcD  : ∀ j, VecIsParallel3 (D · j) c₀ c₁ (c₀ - c₁)
  hcAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular
  -- note: the following conditions are needed to prove the lemma about short tableau pivots preserving the family
  hBₗ  : (⊞ Aₗ 0 (D.submatrix Sum.inl id) !![1; 1]).IsTotallyUnimodular
  hc₀ : c₀ ◩0 = 1 ∧ c₀ ◩1 = 0
  hc₁ : (c₁ ◩0 = 0 ∧ c₁ ◩1 = -1) ∨ (c₁ ◩0 = 1 ∧ c₁ ◩1 = 1)

/-- The resulting 3-sum-like matrix. -/
abbrev MatrixLikeSum3'.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ (Fin 2 ⊕ Xᵣ)) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ


/-! ## Pivoting -/

/-- Effect on `Aₗ` after pivoting on an element in `Aₗ`. -/
abbrev MatrixLikeSum3'.shortTableauPivotAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.shortTableauPivot x y

/-- Equivalent expression for `Aₗ` after pivoting on an element in `Aₗ`. -/
lemma MatrixLikeSum3'.shortTableauPivot_Aₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotAₗ x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext
  simp

/-- Effect on `D` after pivoting on an element in `Aₗ`. -/
abbrev MatrixLikeSum3'.shortTableauPivotD {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  ((▬(M.Aₗ x) ⊟ M.D).shortTableauPivot ◩() y).toRows₂

/-- Equivalent expression for `D` after pivoting on an element in `Aₗ`. -/
lemma MatrixLikeSum3'.shortTableauPivot_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotD x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext
  simp

/-- After pivoting on an element in `Aₗ`, adjoining `Aₗ` and `D` (row-wise) still gives a totally unimodular matrix. -/
lemma MatrixLikeSum3'.shortTableauPivot_hAₗD {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.shortTableauPivotAₗ x y ⊟ M.shortTableauPivotD x y).IsTotallyUnimodular := by
  rw [M.shortTableauPivot_D_eq x y, M.shortTableauPivot_Aₗ_eq x y, Matrix.fromRows_toRows]
  exact M.hAₗD.shortTableauPivot hxy

/-! Auxiliary results about multiplying columns of the left block by `0, ±1` factors . -/

abbrev Matrix.mul_col {X Y F : Type} [HMul F F F] (A : Matrix X Y F) (q : Y → F) :
    Matrix X Y F :=
  Matrix.of (fun i j => A i j * q j)

abbrev MatrixLikeSum3'.mulColsAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.mul_col q

lemma MatrixLikeSum3'.mulColsAₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsAₗ q = ((M.Aₗ ⊟ M.D).mul_col q).toRows₁ := by
  ext
  simp only [Matrix.of_apply, Matrix.toRows₁_apply, Matrix.fromRows_apply_inl]

abbrev MatrixLikeSum3'.mulColsD {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  Matrix.of (fun i j => M.D i j * q j)

lemma MatrixLikeSum3'.mulColsD_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsD q = ((M.Aₗ ⊟ M.D).mul_col q).toRows₂ := by
  ext
  simp only [Matrix.of_apply, Matrix.toRows₂_apply, Matrix.fromRows_apply_inr]

lemma MatrixLikeSum3'.mulCols_hAₗD {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yₗ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (M.mulColsAₗ q ⊟ M.mulColsD q).IsTotallyUnimodular := by
  rw [M.mulColsAₗ_eq, M.mulColsD_eq, Matrix.fromRows_toRows]
  exact M.hAₗD.mul_cols hq

lemma MatrixLikeSum3'.mulCols_hBₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (⊞ (M.mulColsAₗ q) 0 ((M.mulColsD q).submatrix Sum.inl id) !![1; 1]).IsTotallyUnimodular := by
  let q' : Yₗ ⊕ Fin 1 → ℚ := (·.casesOn q 1)
  have hq' : ∀ j, q' j ∈ SignType.cast.range := (·.casesOn hq (by simp [q']))
  convert M.hBₗ.mul_cols hq'
  ext
  aesop

-- todo: move upstream?
lemma vecIsParallel3_mul_signType {X F : Type} [Field F] {v : X → F} {c₀ c₁ c₂ : X → F}
    (hv : VecIsParallel3 v c₀ c₁ c₂) {q : F} (hq : q ∈ SignType.cast.range) :
    VecIsParallel3 (fun i => v i * q) c₀ c₁ c₂ := by
  obtain ⟨s, hs⟩ := hq
  cases s with
  | zero =>
      simp only [SignType.zero_eq_zero, SignType.coe_zero] at hs
      simp only [←hs, mul_zero]
      exact Or.inl rfl
  | neg =>
      simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      simp only [←hs, mul_neg, mul_one]
      exact vecIsParallel3_neg hv
      -- todo: maybe incorporate `vecIsParallel3_neg` into this lemma by improving the proof below:
      -- rcases hv with (hv | hv | hv | hv | hv | hv | hv)
      -- all_goals simp only [VecIsParallel3, hv, Pi.zero_apply, neg_zero]
      -- all_goals aesop -- note: this is not ideal in terms of performance
  | pos =>
      simp only [SignType.pos_eq_one, SignType.coe_one] at hs
      simp [←hs]
      exact hv

abbrev MatrixLikeSum3'.mulCols {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ   := M.mulColsAₗ q
  D    := M.mulColsD q
  Aᵣ   := M.Aᵣ
  hAₗD := M.mulCols_hAₗD hq
  hcD  := fun j => vecIsParallel3_mul_signType (M.hcD j) (hq j)
  hcAᵣ := M.hcAᵣ
  hBₗ  := M.mulCols_hBₗ hq
  hc₀ := M.hc₀
  hc₁ := M.hc₁

abbrev MatrixLikeSum3'.Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Fin 2) (Yₗ ⊕ Fin 1) ℚ :=
  ⊞ M.Aₗ 0 (M.D.submatrix Sum.inl id) !![1; 1]

lemma sign_type_neq_neg_one_plus_neg_one (s : SignType) : ↑s ≠ (-1 : ℚ) + (-1 : ℚ) := by
  intro hs
  cases s with
  | zero =>
      simp only [SignType.zero_eq_zero, SignType.coe_zero] at hs
      linarith
  | neg =>
      simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hs
      linarith
  | pos =>
      simp only [SignType.pos_eq_one, SignType.coe_one] at hs
      linarith

set_option maxHeartbeats 0 in
lemma MatrixLikeSum3'.shortTableauPivot_hcD_sum {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} {j : Yₗ} (hDiv : M.Aₗ x j / M.Aₗ x y = -1) :
    VecIsParallel3 (fun i => M.D i j + M.D i y) c₀ c₁ (c₀ - c₁) := by
  cases M.hcD y with
  | inl hu0 => simpa [congrFun hu0] using M.hcD j
  | inr huc =>
    cases M.hcD j with
    | inl hv0 => simpa [congrFun hv0] using M.hcD y
    | inr hvc =>
      -- simplify goal by introducing notation for pivot column and non-pivot column in `D`
      let u := (M.D · y)
      let v := (M.D · j)
      have hu : (M.D · y) = u := rfl
      have hv : (M.D · j) = v := rfl
      simp [congrFun hv, congrFun hu]
      rw [show (fun i => v i + u i) = v + u by rfl]
      -- apply TUness
      let S := !![M.Aₗ x y, M.Aₗ x j, 0; u ◩0, v ◩0, 1; u ◩1, v ◩1, 1]
      have hS_eq : M.Bₗ.submatrix ![◩x, ◪0, ◪1] ![◩y, ◩j, ◪0] = S :=
        Matrix.eta_fin_three _
      have hS : S.IsTotallyUnimodular := by
        convert M.hBₗ.submatrix ![◩x, ◪0, ◪1] ![◩y, ◩j, ◪0]
        exact hS_eq.symm
      have hS00 : S 0 0 ≠ 0 := by
        intro contr
        simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, S] at contr
        simp [contr] at hDiv
      have hSstp := hS.shortTableauPivot hS00
      have huv0 := hSstp.apply 1 1
      simp [S, ←div_mul_comm, hDiv, one_mul] at huv0
      have huv1 := hSstp.apply 2 1
      simp [S, ←div_mul_comm, hDiv, one_mul] at huv1
      have huv2 := hSstp.det ![1, 2] ![1, 2]
      simp [S, Matrix.det_fin_two, ←div_mul_comm, hDiv, one_mul] at huv2
      -- go case bashing
      rcases hu ▸ huc with (huc | huc | huc | huc | huc | huc)
      <;> rcases hv ▸ hvc with (hvc | hvc | hvc | hvc | hvc | hvc) -- spawns 36 cases
      <;> simp [huc, hvc]
      all_goals
        unfold VecIsParallel3
        ring_nf
        try simp only [true_or, or_true] -- reduces from 36 to 18 cases
      all_goals
        rcases M.hc₁ with hc₁ | hc₁ -- goes up from 18 to 36 cases
        <;> try simp [huc, hvc, M.hc₀, hc₁, sign_type_neq_neg_one_plus_neg_one] at huv0 -- reduces from 36 to 20 cases
        <;> try simp [huc, hvc, M.hc₀, hc₁, sign_type_neq_neg_one_plus_neg_one] at huv1 -- reduces from 20 to 8 cases
        <;> try simp [huc, hvc, M.hc₀, hc₁, sign_type_neq_neg_one_plus_neg_one] at huv2 -- reduces from 8 to 0 cases

/-- After pivoting on an element in `Aₗ`, columns of resulting `D` are still generated by `c₀` and `c₁`. -/
lemma MatrixLikeSum3'.shortTableauPivot_hcD {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    ∀ j : Yₗ, VecIsParallel3 ((M.shortTableauPivotD x y) · j) c₀ c₁ (c₀ - c₁) := by
  intro j
  have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
  · obtain ⟨s, hs⟩ := M.hAₗD.apply ◩x y
    cases s <;> tauto
  if hjy : j = y then -- pivot column
    have hPC : VecIsParallel3 (-M.D · y / M.Aₗ x y) c₀ c₁ (c₀ - c₁)
    · cases hAxy with
      | inl h1 =>
        simp only [h1, div_one]
        exact vecIsParallel3_neg (M.hcD y)
      | inr h9 =>
        simp only [h9, neg_div_neg_eq, div_one]
        exact M.hcD y
    simpa [hjy] using hPC
  else -- non-pivot column
    have hDiv : M.Aₗ x j / M.Aₗ x y = 0 ∨ M.Aₗ x j / M.Aₗ x y = 1 ∨ M.Aₗ x j / M.Aₗ x y = -1 := by
      obtain ⟨sᵣ, hsᵣ⟩ := M.hAₗD.apply ◩x j
      cases sᵣ with
      | zero =>
          simp only [SignType.zero_eq_zero, SignType.coe_zero, Matrix.fromRows_apply_inl] at hsᵣ
          simp [←hsᵣ]
      | neg =>
          simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, Matrix.fromRows_apply_inl] at hsᵣ
          rcases hAxy with h | h <;> simp [←hsᵣ, h]
      | pos =>
          simp only [SignType.pos_eq_one, SignType.coe_one, Matrix.fromRows_apply_inl] at hsᵣ
          rcases hAxy with h | h <;> simp [←hsᵣ, h]
    rcases hDiv with h0 | h1 | h9
    · have : ∀ i, M.D i y / M.Aₗ x y * M.Aₗ x j = 0 := by aesop
      have : (M.shortTableauPivotD x y · j) = (M.D · j) := by simp [hjy, this]
      exact this ▸ (M.hcD j)
    · have : (M.D · y / M.Aₗ x y * M.Aₗ x j) = (M.D · y) := by simp_rw [←div_mul_comm, h1, one_mul]
      have : (M.shortTableauPivotD x y · j) = (fun i => M.D i j - M.D i y) := by
        ext i
        simp [hjy, congrFun this i]
      rw [this]
      let q : Yₗ → ℚ := fun j' => if j' = y then -1 else 1
      have hq : ∀ j' : Yₗ, q j' ∈ SignType.cast.range := by
        intro j'
        simp only [Set.mem_range, q]
        if hj' : j' = y then
          use SignType.neg
          simp [hj']
        else
          use SignType.pos
          simp [hj']
      let M' := M.mulCols hq
      let r := M'.Aₗ x j / M'.Aₗ x y
      have h9 : r = -1 := by simp [r, M', q, hjy, div_neg, h1]
      have hDj : (M.D · j) = (M'.D · j) := by
        ext i
        simp [M', q, hjy]
      have hDy : (M.D · y) = -(M'.D · y) := by
        ext i
        simp [M', q, hjy]
      have heq : (fun i => M.D i j - M.D i y) = (fun i => M'.D i j + M'.D i y) := by
        ext i
        simp [congrFun hDj i, congrFun hDy i]
      have hcols := M'.shortTableauPivot_hcD_sum h9
      exact heq ▸ hcols
    · have : (M.D · y / M.Aₗ x y * M.Aₗ x j) = (-M.D · y) := by simp_rw [←div_mul_comm, h9, ←neg_eq_neg_one_mul]
      have : (M.shortTableauPivotD x y · j) = (fun i => M.D i j + M.D i y) := by
        ext i
        simp [hjy, congrFun this i]
      rw [this]
      exact M.shortTableauPivot_hcD_sum h9

lemma MatrixLikeSum3'.shortTableauPivot_hBₗ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (⊞ (M.shortTableauPivotAₗ x y) 0 ((M.shortTableauPivotD x y).submatrix Sum.inl id) !![1; 1]).IsTotallyUnimodular := by
  have hxy' : (⊞ M.Aₗ 0 (M.D.submatrix Sum.inl id) !![1; 1]) ◩x ◩y ≠ 0 := hxy
  convert M.hBₗ.shortTableauPivot hxy'
  aesop

def MatrixLikeSum3'.shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ  := M.shortTableauPivotAₗ x y
  D   := M.shortTableauPivotD x y
  Aᵣ  := M.Aᵣ
  hAₗD := M.shortTableauPivot_hAₗD hxy
  hcD  := M.shortTableauPivot_hcD hxy
  hcAᵣ := M.hcAᵣ
  hBₗ  := M.shortTableauPivot_hBₗ hxy
  hc₀ := M.hc₀
  hc₁ := M.hc₁


/-! ## Total unimodularity -/

lemma MatrixLikeSum3'.hcAᵣext₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁) ◫ M.Aᵣ).IsTotallyUnimodular := by
  convert M.hcAᵣ.comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩()) ↓◩◩◩()) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) Sum.inr))
  aesop

lemma MatrixLikeSum3'.hcAᵣext₂ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮0 ◫ (▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ M.Aᵣ)).IsTotallyUnimodular := by
  convert (M.hcAᵣext₁.mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

/-- Adjoining `D` and `Aᵣ` (column-wise) gives a totally unimodular matrix. -/
lemma MatrixLikeSum3'.hDAᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (M.D ◫ M.Aᵣ).IsTotallyUnimodular := by
  classical
  let e : (Yₗ ⊕ Yᵣ → (Unit ⊕ (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ)) :=
    (·.casesOn
      (fun j =>
        if h0 : (M.D · j) = 0 then ◩() else
        if hpc₀ : (M.D · j) = c₀ then ◪◩◩◩◩◩◩() else
        if hmc₀ : (M.D · j) = -c₀ then ◪◩◩◩◩◩◪() else
        if hpc₁ : (M.D · j) = c₁ then ◪◩◩◩◩◪() else
        if hmc₁ : (M.D · j) = -c₁ then ◪◩◩◩◪() else
        if hpc₂ : (M.D · j) = c₀ - c₁ then ◪◩◩◪() else
        if hmc₂ : (M.D · j) = c₁ - c₀ then ◪◩◪() else
        (False.elim (by have := M.hcD j; aesop)))
      (Sum.inr ∘ Sum.inr))
  convert M.hcAᵣext₂.submatrix id e
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
    have hMD := M.hcD jₗ
    simp only [VecIsParallel3, neg_sub] at hMD
    tauto
  | inr => rfl

/-- Every 3-sum-like matrix is totally unimodular. -/
lemma MatrixLikeSum3'.IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3' Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    M.matrix.IsTotallyUnimodular :=
  sorry  -- todo: adapt proof of total unimodularity of 2-sum


/-! ## Implications for canonical signing of 3-sum of matrices -/

/-!
  In this section we prove that 3-sums of matrices belong to the family of 3-sum-like matrices.
-/

lemma MatrixSum3.IsCanonicalSigning.hc₀ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.c₀ ◩0 = 1 ∧ S.c₀ ◩1 = 0 := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> exact ⟨congrFun (congrFun hSᵣ.right 0) 0, congrFun (congrFun hSᵣ.right 1) 0⟩

lemma MatrixSum3.IsCanonicalSigning.hc₁ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    (S.c₁ ◩0 = 0 ∧ S.c₁ ◩1 = -1) ∨ (S.c₁ ◩0 = 1 ∧ S.c₁ ◩1 = 1) := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> [left; right]
  <;> exact ⟨congrFun (congrFun hSᵣ.right 0) 1, congrFun (congrFun hSᵣ.right 1) 1⟩

/-- Convert a canonical signing of 3-sum of matrices to a 3-sum-like matrix. -/
noncomputable def MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3' {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    MatrixLikeSum3' (Xₗ ⊕ Fin 1) (Yₗ ⊕ Fin 2) Xᵣ (Fin 1 ⊕ Yᵣ) S.c₀ S.c₁ where
  Aₗ := S.Aₗ
  D := S.D
  Aᵣ := S.Aᵣ
  hAₗD := hS.Aₗ_D_isTotallyUnimodular
  hcD := hS.D_eq_cols
  hcAᵣ := hS.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular
  hBₗ := hS.left.left
  hc₀ := hS.hc₀
  hc₁ := hS.hc₁

/-- The canonical signing of a 3-sum of matrices is totally unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.IsTotallyUnimodular' {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.matrix.IsTotallyUnimodular :=
  hS.toMatrixLikeSum3'.IsTotallyUnimodular

/-- If the reconstructed summands of a 3-sum have TU signings, then the canonical signing of the 3-sum has a TU signing. -/
lemma MatrixSum3.HasCanonicalSigning.HasTuSigning' {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    S.matrix.HasTuSigning :=
  ⟨(S.toCanonicalSigning hS.left.left hS.left.right).matrix, hS.isCanonicalSigning.IsTotallyUnimodular', hS.toCanonicalSigning⟩


/-! # Family of 3-sum like matrices: old version -/

/-! ## Definition -/

/-- Structural data of 3-sum-like matrices. -/
@[deprecated MatrixLikeSum3' (since := "2025-06-17")]
structure MatrixLikeSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (c₀ c₁ : Xᵣ → ℚ) where
  Aₗ  : Matrix Xₗ Yₗ ℚ
  D   : Matrix Xᵣ Yₗ ℚ
  Aᵣ  : Matrix Xᵣ Yᵣ ℚ
  hAₗ : (Aₗ ⊟ D).IsTotallyUnimodular
  hD  : ∀ j, VecIsParallel3 (D · j) c₀ c₁ (c₀ - c₁)
  hAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular

/-- The resulting 3-sum-like matrix. -/
abbrev MatrixLikeSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ


/-! ## TUness of bottom block -/

lemma MatrixLikeSum3.hAᵣext₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁) ◫ M.Aᵣ).IsTotallyUnimodular := by
  convert M.hAᵣ.comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩()) ↓◩◩◩()) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) Sum.inr))
  aesop

lemma MatrixLikeSum3.hAᵣext₂ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮0 ◫ (▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ M.Aᵣ)).IsTotallyUnimodular := by
  convert (M.hAᵣext₁.mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

lemma MatrixLikeSum3.hAᵣD {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (M.D ◫ M.Aᵣ).IsTotallyUnimodular := by
  classical
  let e : (Yₗ ⊕ Yᵣ → (Unit ⊕ (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ)) :=
    (·.casesOn
      (fun j =>
        if h0 : (M.D · j) = 0 then ◩() else
        if hpc₀ : (M.D · j) = c₀ then ◪◩◩◩◩◩◩() else
        if hmc₀ : (M.D · j) = -c₀ then ◪◩◩◩◩◩◪() else
        if hpc₁ : (M.D · j) = c₁ then ◪◩◩◩◩◪() else
        if hmc₁ : (M.D · j) = -c₁ then ◪◩◩◩◪() else
        if hpc₂ : (M.D · j) = c₀ - c₁ then ◪◩◩◪() else
        if hmc₂ : (M.D · j) = c₁ - c₀ then ◪◩◪() else
        (False.elim (by have := M.hD j; aesop)))
      (Sum.inr ∘ Sum.inr))
  convert M.hAᵣext₂.submatrix id e
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
    have hMD := M.hD jₗ
    simp only [VecIsParallel3, neg_sub] at hMD
    tauto
  | inr => rfl


/-! ## Pivoting -/

/-!
  In this section we prove that pivoting in the top-left block of a 3-sum-like matrix yields a 3-sum-like matrix.
-/

@[simp]
abbrev matrixStackTwoValsTwoCols {X F : Type} [Zero F] [One F] [Neg F] (u v : X → F) (s : SignType) :
    Matrix (Unit ⊕ X) (Unit ⊕ Unit) F :=
  ▮(·.casesOn ↓1 u) ◫ ▮(·.casesOn ↓s.cast v)

lemma Matrix.shortTableauPivot_col_in_ccVecSet_0 {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 0) (hA₂₂ : VecIsParallel3 (A ◪· ◪()) c₀ c₁ (c₀ - c₁)) :
    VecIsParallel3 ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) c₀ c₁ (c₀ - c₁) := by
  simp [hA₁₁, hA₁₂, hA₂₂]

lemma matrixStackTwoValsTwoCols9_addAssumption {X : Type} (c₀ : X → ℚ) (c₁ : X → ℚ) (u : X → ℚ) (v : X → ℚ) :
  ∃ i, ∃ j,
    (c₀ i = 1 ∧ c₀ j = 0)
    ∧ ((c₁ i = 0 ∧ c₁ j = -1) ∨ (c₁ i = 1 ∧ c₁ j = 1))
    ∧ (!![1, -1, 0; u i, v i, 1; u j, v j, 1].IsTotallyUnimodular) := sorry

lemma sign_type_neq_neg_one_plus_neg_one' (s : SignType) : ↑s ≠ (-1 : ℚ) + (-1 : ℚ) := by
  intro hs
  cases s with
  | zero =>
      simp only [SignType.zero_eq_zero, SignType.coe_zero] at hs
      linarith
  | neg =>
      simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hs
      linarith
  | pos =>
      simp only [SignType.pos_eq_one, SignType.coe_one] at hs
      linarith

set_option maxHeartbeats 0 in
lemma matrixStackTwoValsTwoCols9_shortTableauPivot {X : Type} [DecidableEq X]
    {c₀ : X → ℚ} {c₁ : X → ℚ} (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    (u : X → ℚ) (v : X → ℚ)
    (hA : (matrixStackTwoValsTwoCols u v SignType.neg).IsTotallyUnimodular)
    (hucc : VecIsParallel3 u c₀ c₁ (c₀ - c₁)) (hvcc : VecIsParallel3 v c₀ c₁ (c₀ - c₁)) :
    VecIsParallel3 (((matrixStackTwoValsTwoCols u v SignType.neg).shortTableauPivot ◩() ◩()) ◪· ◪()) c₀ c₁ (c₀ - c₁) := by
  simp
  rw [show (fun x : X => v x + u x) = v + u by rfl]
  cases hucc with
  | inl hu0 =>
    simp [hu0]
    exact hvcc
  | inr huc =>
    cases hvcc with
    | inl hv0 =>
      simp [hv0]
      right
      exact huc
    | inr hvc =>
      rcases huc with (hu | hu | hu | hu | hu | hu) <;> rcases hvc with (hv | hv | hv | hv | hv | hv) <;> simp [hu, hv]
      all_goals
        unfold VecIsParallel3
        ring_nf
        try tauto
      · -- 1) hu : u = c₀, hv : v = c₀
        left
        ext i
        have hc₀i := hcc.apply i ◩◩()
        rw [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inl, Matrix.replicateCol_apply] at hc₀i
        obtain ⟨s₀, hs₀⟩ := hc₀i
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        cases s₀ <;> simp [←hs₀, ←sub_eq_add_neg] at hs₂ ⊢
      · -- 2) hu : u = c₀, hv : v = c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₀] at t4
        | inr hc₁₁ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₁] at t6
      · -- 3) hu : u = c₀, hv : v = c₀ - c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₀] at t6
        | inr hc₁₁ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₁] at t4
      · -- 4) hu : u = -c₀, hv : v = -c₀
        -- same as 1)
        left
        ext i
        have hc₀i := hcc.apply i ◩◩()
        rw [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inl, Matrix.replicateCol_apply] at hc₀i
        obtain ⟨s₀, hs₀⟩ := hc₀i
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        cases s₀ <;> simp [←hs₀, ←sub_eq_add_neg] at hs₂ ⊢
      · -- 5) hu : u = -c₀, hv : v = -c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₀] at t4
        | inr hc₁₁ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₁] at t6
            exfalso
            clear * - t6
            obtain ⟨s, hs⟩ := t6
            exact (sign_type_neq_neg_one_plus_neg_one' s) hs
      · -- 6) hu : u = -c₀, hv : v = c₁ - c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₀] at t6
            exfalso
            clear * - t6
            obtain ⟨s, hs⟩ := t6
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
        | inr hc₁₁ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₁] at t4
      · -- 7) hu : u = c₁, hv : v = c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₀] at t4
        | inr hc₁₁ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₁] at t6
      · -- 8) hu : u = c₁, hv : v = c₁
        -- similar to 1), but with c₁ instead of c₀
        left
        ext i
        have hc₁i := hcc.apply i ◩◪()
        rw [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.replicateCol_apply] at hc₁i
        obtain ⟨s₁, hs₁⟩ := hc₁i
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        cases s₁ <;> simp [←hs₁, ←sub_eq_add_neg] at hs₂ ⊢
      · -- 9) hu : u = c₁, hv : v = c₁ - c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₀] at t7
            exfalso
            clear * - t7
            obtain ⟨s, hs⟩ := t7
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
        | inr hc₁₁ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₁] at t7
      · -- 10) hu : u = -c₁, hv : v = -c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₀] at t4
        | inr hc₁₁ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₁] at t6
            exfalso
            clear * - t6
            obtain ⟨s, hs⟩ := t6
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
      · -- 11) hu : u = -c₁, hv : v = -c₁
        -- same as 8)
        left
        ext i
        have hc₁i := hcc.apply i ◩◪()
        rw [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.replicateCol_apply] at hc₁i
        obtain ⟨s₁, hs₁⟩ := hc₁i
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        cases s₁ <;> simp [←hs₁, ←sub_eq_add_neg] at hs₂ ⊢
      · -- 12) hu : u = -c₁, hv : v = c₀ - c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₀] at t7
        | inr hc₁₁ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₁] at t7
            exfalso
            clear * - t7
            obtain ⟨s, hs⟩ := t7
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
      · -- 13) hu : u = c₀ - c₁, hv : v = c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₀] at t6
        | inr hc₁₁ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₁] at t4
      · -- 14) hu : u = c₀ - c₁, hv : v = -c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₀] at t7
        | inr hc₁₁ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₁] at t7
            exfalso
            clear * - t7
            obtain ⟨s, hs⟩ := t7
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
      · -- 15) hu : u = c₀ - c₁, hv : v = c₀ - c₁
        -- similar to on_goal 1, but with c₀ - c₁ (instead of c₀)
        left
        ext i
        have hicc := hcc.apply i ◪()
        rw [Matrix.fromCols_apply_inr, Matrix.replicateCol_apply] at hicc
        obtain ⟨s₁, hs₁⟩ := hicc
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        rw [←sub_mul]
        rw [Pi.sub_apply] at hs₁
        rw [sub_eq_add_neg, neg_sub, ←mul_two] at hs₂
        cases s₁ <;> cases s₂ <;> simp [←hs₁] at hs₂ ⊢ <;> linarith only [hs₂]
      · -- 16) hu : u = c₁ - c₀, hv : v = -c₀
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t6 := t2.apply 1 1
            simp [hu, hv, hc₀, hc₁₀] at t6
            exfalso
            clear * - t6
            obtain ⟨s, hs⟩ := t6
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
        | inr hc₁₁ =>
            have t4 := t2.det ![1, 2] ![1, 2]
            have t5 : !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1].submatrix ![1, 2] ![1, 2]
              = !![v i + u i, 1; v j + u j, 1] := Matrix.eta_fin_two _
            rw [t5] at t4
            simp [hu, hv, hc₀, hc₁₁] at t4
      · -- 17) hu : u = c₁ - c₀, hv : v = c₁
        -- can be solved with the following additional assumptions:
        obtain ⟨i, j, hc₀, hc₁, hS⟩ := matrixStackTwoValsTwoCols9_addAssumption c₀ c₁ u v
        have t1 : !![1, -1, 0; u i, v i, 1; u j, v j, 1] 0 0 ≠ 0 := (ne_of_beq_false rfl).symm
        have t2 := hS.shortTableauPivot t1
        have t3 : !![1, -1, 0; u i, v i, 1; u j, v j, 1].shortTableauPivot 0 0
            = !![1, -1, 0; -u i, v i + u i, 1; -u j, v j + u j, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.shortTableauPivot_eq]
        rw [t3] at t2
        cases hc₁ with
        | inl hc₁₀ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₀] at t7
            exfalso
            clear * - t7
            obtain ⟨s, hs⟩ := t7
            exact (sign_type_neq_neg_one_plus_neg_one s) hs
        | inr hc₁₁ =>
            have t7 := t2.apply 2 1
            simp [hu, hv, hc₀, hc₁₁] at t7
      · -- 18) hu : u = c₁ - c₀, hv : v = c₁ - c₀
        -- similar to 15), but with minor adjustments
        left
        ext i
        have hicc := hcc.apply i ◪()
        rw [Matrix.fromCols_apply_inr, Matrix.replicateCol_apply] at hicc
        obtain ⟨s₁, hs₁⟩ := hicc
        have hdet := hA.det ![◩(), ◪i] ![◩(), ◪()]
        simp [Matrix.det_fin_two, hu, hv] at hdet
        obtain ⟨s₂, hs₂⟩ := hdet
        rw [←sub_mul]
        rw [←neg_sub, Pi.neg_apply, ←neg_eq_iff_eq_neg, Pi.sub_apply] at hs₁ -- note minor adjustments
        rw [sub_eq_add_neg, neg_sub, ←mul_two] at hs₂
        cases s₁ <;> cases s₂ <;> simp [←hs₁] at hs₂ ⊢ <;> linarith only [hs₂]

lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_9 {X : Type} [DecidableEq X]
    {c₀ : X → ℚ} {c₁ : X → ℚ} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) ℚ} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = -1)
    (hA₂₁ : VecIsParallel3 (A ◪· ◩()) c₀ c₁ (c₀ - c₁)) (hA₂₂ : VecIsParallel3 (A ◪· ◪()) c₀ c₁ (c₀ - c₁))
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    VecIsParallel3 ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) c₀ c₁ (c₀ - c₁) := by
  have A_eq : A = matrixStackTwoValsTwoCols (fun x => A ◪x ◩()) (fun x => A ◪x ◪()) SignType.neg
  · ext (_|_) (_|_)
    · exact hA₁₁
    · exact hA₁₂
    · simp
    · simp
  exact A_eq ▸ matrixStackTwoValsTwoCols9_shortTableauPivot hcc (A ◪· ◩()) (A ◪· ◪()) (A_eq ▸ hA) hA₂₁ hA₂₂

lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_1 {X F : Type} [Field F] [DecidableEq X]
    {c₀ : X → F} {c₁ : X → F} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 1)
    (hA₂₁ : VecIsParallel3 (A ◪· ◩()) c₀ c₁ (c₀ - c₁)) (hA₂₂ : VecIsParallel3 (A ◪· ◪()) c₀ c₁ (c₀ - c₁))
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    VecIsParallel3 ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) c₀ c₁ (c₀ - c₁) := by
  sorry -- TODO reduce to `Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_9`

lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet {X : Type} [DecidableEq X]
    {c₀ : X → ℚ} {c₁ : X → ℚ} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) ℚ} (hA : A.IsTotallyUnimodular) (hA₁₁ : A ◩() ◩() ≠ 0)
    (hA₂₁ : VecIsParallel3 (A ◪· ◩()) c₀ c₁ (c₀ - c₁)) (hA₂₂ : VecIsParallel3 (A ◪· ◪()) c₀ c₁ (c₀ - c₁))
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    VecIsParallel3 ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) c₀ c₁ (c₀ - c₁) := by
  obtain ⟨sₗ, hsₗ⟩ := hA.apply ◩() ◩()
  cases sₗ with
  | zero =>
    exfalso
    exact hA₁₁ hsₗ.symm
  | pos =>
    obtain ⟨sᵣ, hsᵣ⟩ := hA.apply ◩() ◪()
    cases sᵣ with
    | zero => exact A.shortTableauPivot_col_in_ccVecSet_0 hsₗ.symm hsᵣ.symm hA₂₂
    | pos => exact hA.shortTableauPivot_col_in_ccVecSet_1 hsₗ.symm hsᵣ.symm hA₂₁ hA₂₂ hcc
    | neg => exact hA.shortTableauPivot_col_in_ccVecSet_9 hsₗ.symm hsᵣ.symm hA₂₁ hA₂₂ hcc
  | neg =>
    let q : Unit ⊕ X → ℚ := (·.casesOn ↓(-1) ↓1)
    have hq : ∀ i, q i ∈ SignType.cast.range
    · rintro (_|_) <;> simp [q]
    have hAq := hA.mul_rows hq
    obtain ⟨sᵣ, hsᵣ⟩ := hA.apply ◩() ◪()
    cases sᵣ with
    | zero =>
      convert
        (Matrix.of (fun i : Unit ⊕ X => fun j : Unit ⊕ Unit => A i j * q i)).shortTableauPivot_col_in_ccVecSet_0
          (by simp [←hsₗ, q])
          (by simp [←hsᵣ, q])
          (show VecIsParallel3 _ c₀ c₁ (c₀ - c₁) by simp [*, q, vecIsParallel3_neg])
        using 2
      simp only [Matrix.shortTableauPivot_eq, Matrix.of_apply, reduceCtorEq, ↓reduceIte]
      ring
    | pos =>
      convert
        hAq.shortTableauPivot_col_in_ccVecSet_9
          (by simp [←hsₗ, q])
          (by simp [←hsᵣ, q])
          (by simp [hA₂₁, q])
          (by simp [hA₂₂, q])
          hcc
        using 2
      simp only [Matrix.shortTableauPivot_eq, Matrix.of_apply, reduceCtorEq, ↓reduceIte]
      ring
    | neg =>
      convert
        hAq.shortTableauPivot_col_in_ccVecSet_1
          (by simp [←hsₗ, q])
          (by simp [←hsᵣ, q])
          (by simp [hA₂₁, q])
          (by simp [hA₂₂, q])
          hcc
        using 2
      simp only [Matrix.shortTableauPivot_eq, Matrix.of_apply, reduceCtorEq, ↓reduceIte]
      ring

abbrev Matrix.shortTableauPivotOuterRow {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (y : Y) :
    Matrix X Y ℚ :=
  ((▬r ⊟ A).shortTableauPivot ◩() y).toRows₂

lemma MatrixLikeSum3.shortTableauPivot_Aₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.Aₗ.shortTableauPivot x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext
  simp

lemma MatrixLikeSum3.shortTableauPivot_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.D.shortTableauPivotOuterRow (M.Aₗ x) y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext
  simp

lemma MatrixLikeSum3.shortTableauPivot_hAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.Aₗ.shortTableauPivot x y ⊟ M.D.shortTableauPivotOuterRow (M.Aₗ x) y).IsTotallyUnimodular := by
  rw [M.shortTableauPivot_D_eq x y, M.shortTableauPivot_Aₗ_eq x y, Matrix.fromRows_toRows]
  exact M.hAₗ.shortTableauPivot hxy

lemma MatrixLikeSum3.shortTableauPivot_D_cols_in_ccVecSet {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) (j : Yₗ) :
    VecIsParallel3 ((M.D.shortTableauPivotOuterRow (M.Aₗ x) y) · j) c₀ c₁ (c₀ - c₁) := by
  if hjy : j = y then
    have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
    · obtain ⟨s, hs⟩ := M.hAₗ.apply ◩x y
      cases s <;> tauto
    have hPC : VecIsParallel3 (-M.D · y / M.Aₗ x y) c₀ c₁ (c₀ - c₁)
    · cases hAxy with
      | inl h1 =>
        simp only [h1, div_one]
        exact vecIsParallel3_neg (M.hD y)
      | inr h9 =>
        simp only [h9, neg_div_neg_eq, div_one]
        exact M.hD y
    simpa [hjy] using hPC
  else
    let A : Matrix (Unit ⊕ Xᵣ) (Unit ⊕ Unit) ℚ :=
      Matrix.of (fun u : Unit ⊕ Unit => ·.casesOn (u.casesOn ↓↓(M.Aₗ x y) ↓↓(M.Aₗ x j)) (u.casesOn ↓(M.D · y) ↓(M.D · j)))
    have hA : A.IsTotallyUnimodular
    · convert M.hAₗ.submatrix (fun i : Unit ⊕ Xᵣ => i.map ↓x id) (fun u : Unit ⊕ Unit => u.casesOn ↓y ↓j)
      aesop
    simpa [hjy] using hA.shortTableauPivot_col_in_ccVecSet hxy (M.hD y) (M.hD j) (M.hAᵣ.submatrix id Sum.inl)

def MatrixLikeSum3.shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ  := M.Aₗ.shortTableauPivot x y
  D   := M.D.shortTableauPivotOuterRow (M.Aₗ x) y
  Aᵣ  := M.Aᵣ
  hAₗ := M.shortTableauPivot_hAₗ hxy
  hD  := M.shortTableauPivot_D_cols_in_ccVecSet hxy
  hAᵣ := M.hAᵣ


/-! ## Total unimodularity -/

/-!
  In this section we prove that every 3-sum-like matrix is totally unimodular.
-/

/-- Every 3-sum-like matrix is totally unimodular. -/
lemma MatrixLikeSum3.IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    M.matrix.IsTotallyUnimodular :=
  sorry  -- todo: adapt proof of total unimodularity of 2-sum


/-! ## Implications for canonical signing of 3-sum of matrices -/

/-!
  In this section we prove that 3-sums of matrices belong to the family of 3-sum-like matrices.
-/

/-- Convert a canonical signing of 3-sum of matrices to a 3-sum-like matrix. -/
noncomputable def MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3 {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    MatrixLikeSum3 (Xₗ ⊕ Fin 1) (Yₗ ⊕ Fin 2) (Fin 2 ⊕ Xᵣ) (Fin 1 ⊕ Yᵣ) S.c₀ S.c₁ where
  Aₗ := S.Aₗ
  D := S.D
  Aᵣ := S.Aᵣ
  hAₗ := hS.Aₗ_D_isTotallyUnimodular
  hD := hS.D_eq_cols
  hAᵣ := hS.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular

/-- The canonical signing of a 3-sum of matrices is totally unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.matrix.IsTotallyUnimodular :=
  hS.toMatrixLikeSum3.IsTotallyUnimodular

/-- If the reconstructed summands of a 3-sum have TU signings, then the canonical signing of the 3-sum has a TU signing. -/
lemma MatrixSum3.HasCanonicalSigning.HasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2} (hS : S.HasCanonicalSigning) :
    S.matrix.HasTuSigning :=
  ⟨(S.toCanonicalSigning hS.left.left hS.left.right).matrix, hS.isCanonicalSigning.IsTotallyUnimodular, hS.toCanonicalSigning⟩
