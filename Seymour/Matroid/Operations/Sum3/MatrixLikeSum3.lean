import Seymour.Matroid.Operations.Sum3.CanonicalSigningSum3


/-! # Family of 3-sum-like matrices -/

/-! ## Definition -/

/-- Structural data of 3-sum-like matrices. -/
structure MatrixLikeSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ) where
  Aₗ : Matrix Xₗ Yₗ ℚ
  D  : Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ
  Aᵣ : Matrix (Fin 2 ⊕ Xᵣ) Yᵣ ℚ
  LeftTU : (Aₗ ⊟ D).IsTotallyUnimodular
  Parallels : ∀ j : Yₗ, VecIsParallel3 (D · j) c₀ c₁ (c₀ - c₁)
  BottomTU : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular
  AuxTU : (⊞ Aₗ 0 D.toRows₁ !![1; 1]).IsTotallyUnimodular
  Col10 : c₀ ◩0 = 1 ∧ c₀ ◩1 = 0
  Col0911 : (c₁ ◩0 = 0 ∧ c₁ ◩1 = -1) ∨ (c₁ ◩0 = 1 ∧ c₁ ◩1 = 1)

/-- The resulting 3-sum-like matrix. -/
abbrev MatrixLikeSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ (Fin 2 ⊕ Xᵣ)) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ


/-! ## Pivoting -/

/-- Effect on `Aₗ` after pivoting on an element in `Aₗ`. -/
abbrev MatrixLikeSum3.shortTableauPivotAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.shortTableauPivot x y

/-- Equivalent expression for `Aₗ` after pivoting on an element in `Aₗ`. -/
lemma MatrixLikeSum3.shortTableauPivotAₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotAₗ x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext
  simp

/-- Effect on `D` after pivoting on an element in `Aₗ`. -/
abbrev MatrixLikeSum3.shortTableauPivotD {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  ((▬(M.Aₗ x) ⊟ M.D).shortTableauPivot ◩() y).toRows₂

/-- Equivalent expression for `D` after pivoting on an element in `Aₗ`. -/
lemma MatrixLikeSum3.shortTableauPivotD_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.shortTableauPivotD x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext
  simp

/-- After pivoting on an element in `Aₗ`, adjoining `Aₗ` and `D` (row-wise) still gives a totally unimodular matrix. -/
lemma MatrixLikeSum3.shortTableauPivot_leftTU {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.shortTableauPivotAₗ x y ⊟ M.shortTableauPivotD x y).IsTotallyUnimodular := by
  rw [M.shortTableauPivotD_eq x y, M.shortTableauPivotAₗ_eq x y, Matrix.fromRows_toRows]
  exact M.LeftTU.shortTableauPivot hxy

/-! Auxiliary results about multiplying columns of the left block by `0, ±1` factors . -/

abbrev Matrix.mulCols {X Y F : Type} [Mul F] (A : Matrix X Y F) (q : Y → F) :
    Matrix X Y F :=
  Matrix.of (fun i : X => fun j : Y => A i j * q j)

abbrev MatrixLikeSum3.mulColsAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix Xₗ Yₗ ℚ :=
  M.Aₗ.mulCols q

lemma MatrixLikeSum3.mulColsAₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsAₗ q = ((M.Aₗ ⊟ M.D).mulCols q).toRows₁ := by
  ext
  simp only [Matrix.of_apply, Matrix.toRows₁_apply, Matrix.fromRows_apply_inl]

abbrev MatrixLikeSum3.mulColsD {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    Matrix (Fin 2 ⊕ Xᵣ) Yₗ ℚ :=
  Matrix.of (fun i : Fin 2 ⊕ Xᵣ => fun j : Yₗ => M.D i j * q j)

lemma MatrixLikeSum3.mulColsD_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁)
    (q : Yₗ → ℚ) :
    M.mulColsD q = ((M.Aₗ ⊟ M.D).mulCols q).toRows₂ := by
  ext
  simp only [Matrix.of_apply, Matrix.toRows₂_apply, Matrix.fromRows_apply_inr]

lemma MatrixLikeSum3.mulCols_leftTU {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yₗ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (M.mulColsAₗ q ⊟ M.mulColsD q).IsTotallyUnimodular := by
  rw [M.mulColsAₗ_eq, M.mulColsD_eq, Matrix.fromRows_toRows]
  exact M.LeftTU.mul_cols hq

lemma MatrixLikeSum3.mulCols_auxTU {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    (⊞ (M.mulColsAₗ q) 0 (M.mulColsD q).toRows₁ !![1; 1]).IsTotallyUnimodular := by
  let q' : Yₗ ⊕ Fin 1 → ℚ := (·.casesOn q 1)
  have hq' : ∀ j, q' j ∈ SignType.cast.range := (·.casesOn hq (by simp [q']))
  convert M.AuxTU.mul_cols hq'
  aesop

abbrev MatrixLikeSum3.mulCols {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Xᵣ] [DecidableEq Yₗ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {q : Yₗ → ℚ} (hq : ∀ j : Yₗ, q j ∈ SignType.cast.range) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ := M.mulColsAₗ q
  D  := M.mulColsD q
  Aᵣ := M.Aᵣ
  LeftTU := M.mulCols_leftTU hq
  Parallels j := (M.Parallels j).mul_sign (hq j)
  BottomTU := M.BottomTU
  AuxTU := M.mulCols_auxTU hq
  Col10 := M.Col10
  Col0911 := M.Col0911

abbrev MatrixLikeSum3.Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Fin 2) (Yₗ ⊕ Fin 1) ℚ :=
  ⊞ M.Aₗ 0 M.D.toRows₁ !![1; 1]

lemma SignType.neq_neg_one_add_neg_one (s : SignType) : s.cast ≠ (-1 : ℚ) + (-1 : ℚ) := by
  intro hs
  cases s with
  | zero =>
    simp only [SignType.zero_eq_zero, SignType.coe_zero] at hs
    norm_num at hs
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one] at hs
    norm_num at hs
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one] at hs
    norm_num at hs

set_option maxHeartbeats 666666 in
lemma MatrixLikeSum3.vecIsParallel3 {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y j : Yₗ} (hAₗ : M.Aₗ x j / M.Aₗ x y = -1) :
    VecIsParallel3 (fun i : Fin 2 ⊕ Xᵣ => M.D i j + M.D i y) c₀ c₁ (c₀ - c₁) := by
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
      let S := !![M.Aₗ x y, M.Aₗ x j, 0; u ◩0, v ◩0, 1; u ◩1, v ◩1, 1]
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
      all_goals rw [huc, hvc]
      all_goals try
        unfold VecIsParallel3
        ring_nf
        simp only [true_or, or_true] -- reduces from 36 to 18 cases
      all_goals rcases M.Col0911 with hc₁ | hc₁ -- goes up from 18 to 36 cases
      all_goals try simp [huc, hvc, hc₁, M.Col10, SignType.neq_neg_one_add_neg_one] at huv0 -- reduces from 36 to 20 cases
      all_goals try simp [huc, hvc, hc₁, M.Col10, SignType.neq_neg_one_add_neg_one] at huv1 -- reduces from 20 to 8 cases
      all_goals try simp [huc, hvc, hc₁, M.Col10, SignType.neq_neg_one_add_neg_one] at huv01 -- reduces from 8 to 0 cases

/-- After pivoting on an element in `Aₗ`, columns of resulting `D` are still generated by `c₀` and `c₁`. -/
lemma MatrixLikeSum3.shortTableauPivot_vecIsParallel3 {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) (j : Yₗ) :
    VecIsParallel3 ((M.shortTableauPivotD x y) · j) c₀ c₁ (c₀ - c₁) := by
  have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
  · obtain ⟨s, hs⟩ := M.LeftTU.apply ◩x y
    cases s <;> tauto
  if hjy : j = y then -- pivot column
    have hPC : VecIsParallel3 (-M.D · y / M.Aₗ x y) c₀ c₁ (c₀ - c₁)
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
      exact hM' ▸ M'.vecIsParallel3 h9
    · have hMDAₗ : (M.D · y / M.Aₗ x y * M.Aₗ x j) = (-M.D · y)
      · simp_rw [←div_mul_comm, h9, ←neg_eq_neg_one_mul]
      have hMDj : (M.shortTableauPivotD x y · j) = (fun i : Fin 2 ⊕ Xᵣ => M.D i j + M.D i y)
      · ext i
        simp [hjy, congr_fun hMDAₗ i]
      exact hMDj ▸ M.vecIsParallel3 h9

lemma MatrixLikeSum3.shortTableauPivot_auxTU {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (⊞ (M.shortTableauPivotAₗ x y) 0 (M.shortTableauPivotD x y).toRows₁ !![1; 1]).IsTotallyUnimodular := by
  have hxy' : (⊞ M.Aₗ 0 M.D.toRows₁ !![1; 1]) ◩x ◩y ≠ 0 := hxy
  convert M.AuxTU.shortTableauPivot hxy'
  aesop

def MatrixLikeSum3.shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
     {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ := M.shortTableauPivotAₗ x y
  D  := M.shortTableauPivotD x y
  Aᵣ := M.Aᵣ
  LeftTU := M.shortTableauPivot_leftTU hxy
  Parallels := M.shortTableauPivot_vecIsParallel3 hxy
  BottomTU := M.BottomTU
  AuxTU := M.shortTableauPivot_auxTU hxy
  Col10 := M.Col10
  Col0911 := M.Col0911


/-! ## Total unimodularity -/

lemma MatrixLikeSum3.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁) ◫ M.Aᵣ).IsTotallyUnimodular := by
  convert M.BottomTU.comp_cols
    (fun j : ((((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Yᵣ) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (↓◩◩◩()) ↓◩◩◩()) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) Sum.inr))
  aesop

lemma MatrixLikeSum3.pmz_c₀_c₁_c₂_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    (▮0 ◫ (▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ M.Aᵣ)).IsTotallyUnimodular := by
  convert (M.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular.mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 (-1)) 1) (-1)) 1) (-1)) 1) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).zero_fromCols Unit
  aesop

/-- Adjoining `D` and `Aᵣ` gives a totally unimodular matrix. -/
lemma MatrixLikeSum3.D_Aᵣ_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ}
    (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
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
    simp only [VecIsParallel3, neg_sub] at hMD
    tauto
  | inr => rfl

/-- Every 3-sum-like matrix is totally unimodular. -/
lemma MatrixLikeSum3.IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Fin 2 ⊕ Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    M.matrix.IsTotallyUnimodular :=
  sorry  -- todo: adapt proof of total unimodularity of 2-sum


/-! ## Implications for canonical signing of 3-sum of matrices -/

/-!
  In this section we prove that 3-sums of matrices belong to the family of 3-sum-like matrices.
-/

lemma MatrixSum3.IsCanonicalSigning.col10 {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    S.c₀ ◩0 = 1 ∧ S.c₀ ◩1 = 0 := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> exact ⟨congr_fun₂ hSᵣ.right 0 0, congr_fun₂ hSᵣ.right 1 0⟩

lemma MatrixSum3.IsCanonicalSigning.col0911 {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    (S.c₁ ◩0 = 0 ∧ S.c₁ ◩1 = -1) ∨ (S.c₁ ◩0 = 1 ∧ S.c₁ ◩1 = 1) := by
  rcases hS.right with hSᵣ | hSᵣ
  <;> [left; right]
  <;> exact ⟨congr_fun₂ hSᵣ.right 0 1, congr_fun₂ hSᵣ.right 1 1⟩

/-- Convert a canonical signing of 3-sum of matrices to a 3-sum-like matrix. -/
noncomputable def MatrixSum3.IsCanonicalSigning.toMatrixLikeSum3 {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ} (hS : S.IsCanonicalSigning) :
    MatrixLikeSum3 (Xₗ ⊕ Fin 1) (Yₗ ⊕ Fin 2) Xᵣ (Fin 1 ⊕ Yᵣ) S.c₀ S.c₁ where
  Aₗ := S.Aₗ
  D  := S.D
  Aᵣ := S.Aᵣ
  LeftTU := hS.Aₗ_D_isTotallyUnimodular
  Parallels := hS.D_eq_cols
  BottomTU := hS.c₀_c₁_c₂_Aᵣ_isTotallyUnimodular
  AuxTU := hS.left.left
  Col10 := hS.col10
  Col0911 := hS.col0911

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
