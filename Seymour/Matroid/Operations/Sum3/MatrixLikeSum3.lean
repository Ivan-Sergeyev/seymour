import Seymour.Matroid.Operations.Sum3.CanonicalSigningSum3


/-! # Family of 3-sum-like matrices -/

/-! ## Definition -/

/-- Structural data of 3-sum-like matrices. -/
structure MatrixLikeSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (c₀ c₁ : Xᵣ → ℚ) where
  Aₗ  : Matrix Xₗ Yₗ ℚ
  D   : Matrix Xᵣ Yₗ ℚ
  Aᵣ  : Matrix Xᵣ Yᵣ ℚ
  hAₗ : (Aₗ ⊟ D).IsTotallyUnimodular
  hD  : D.HasColsIn c₀ c₁
  hAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular

/-- The resulting 3-sum-like matrix. -/
abbrev MatrixLikeSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ


/-! ## Pivoting -/

/-!
  In this section we prove that pivoting in the top-left block of a 3-sum-like matrix yields a 3-sum-like matrix.
-/

private abbrev VecSet {X F : Type} [Zero F] [Neg F] [Sub F] (c₀ : X → F) (c₁ : X → F) : Set (X → F) :=
  {0, c₀, -c₀, c₁, -c₁, c₀ - c₁, c₁ - c₀}

private lemma neg_vec_in_vecSet {X F : Type} [Zero F] [Neg F] [Sub F] {c₀ : X → F} {c₁ : X → F}
    {v : X → F} (hv : v ∈ VecSet c₀ c₁) : -v ∈ VecSet c₀ c₁ :=
  sorry

private lemma pivot_in_vecSet₁ {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F}
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 0) (hA₂₂ : (A ◪· ◪()) ∈ VecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ VecSet c₀ c₁ := by
  simp [hA₁₁, hA₁₂, hA₂₂]

private lemma pivot_in_vecSet₂ {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 1) (hA₂₁ : (A ◪· ◩()) ∈ VecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ VecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ VecSet c₀ c₁ := by
  simp [hA₁₁, hA₁₂, hA₂₂]
  have hA₂₁' := hA₂₁
  cases hA₂₁ with
  | inl hA₂₁0 =>
      simp [congr_fun hA₂₁0]
      exact hA₂₂
  | inr hA₂₁c =>
    cases hA₂₂ with
    | inl hA₂₂0 =>
      simp [congr_fun hA₂₂0]
      exact neg_vec_in_vecSet hA₂₁'
    | inr hA₂₂c =>
      sorry -- 6 x 6 cases

set_option maxHeartbeats 0 in
private lemma pivot_in_vecSet₃ {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = -1) (hA₂₁ : (A ◪· ◩()) ∈ VecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ VecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ VecSet c₀ c₁ := by
  simp [hA₁₁, hA₁₂, hA₂₂]
  have hA₂₁' := hA₂₁
  cases hA₂₁ with
  | inl hA₂₁0 =>
      simp [congr_fun hA₂₁0]
      exact hA₂₂
  | inr hA₂₁c =>
    cases hA₂₂ with
    | inl hA₂₂0 =>
      simp [congr_fun hA₂₂0]
      exact hA₂₁'
    | inr hA₂₂c =>
      rcases hA₂₁c with (hA₂₁c | hA₂₁c | hA₂₁c | hA₂₁c | hA₂₁c | hA₂₁c)
      <;> rcases hA₂₂c with (hA₂₂c | hA₂₂c | hA₂₂c | hA₂₂c | hA₂₂c | hA₂₂c)
      <;> simp [congr_fun hA₂₁c, congr_fun hA₂₂c]
      <;> clear hA₂₁c hA₂₂c hA₂₁'
      -- <;> try aesop
      <;> sorry

private lemma pivot_in_vecSet {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() ≠ 0) (hA₂₁ : (A ◪· ◩()) ∈ VecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ VecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ VecSet c₀ c₁ := by
  sorry -- reduction to 3 cases above by multiplying first row by A ◩() ◩()

abbrev Matrix.shortTableauPivotOuterRow {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (y : Y) :
    Matrix X Y ℚ :=
  ((▬r ⊟ A).shortTableauPivot ◩() y).toRows₂

lemma MatrixLikeSum3.shortTableauPivot_Aₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.Aₗ.shortTableauPivot x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext i j
  simp

lemma MatrixLikeSum3.shortTableauPivot_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.D.shortTableauPivotOuterRow (M.Aₗ x) y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext i j
  simp

lemma MatrixLikeSum3.shortTableauPivot_hAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.Aₗ.shortTableauPivot x y ⊟ M.D.shortTableauPivotOuterRow (M.Aₗ x) y).IsTotallyUnimodular := by
  rw [M.shortTableauPivot_D_eq x y, M.shortTableauPivot_Aₗ_eq x y, Matrix.fromRows_toRows]
  exact M.hAₗ.shortTableauPivot hxy

lemma MatrixLikeSum3.shortTableauPivot_D_hasColsIn'' {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0)
    (hMD : ∀ j, (M.D · j) ∈ VecSet c₀ c₁) :
    ∀ j, ((M.D.shortTableauPivotOuterRow (M.Aₗ x) y) · j) ∈ VecSet c₀ c₁ := by
  intro j
  if hjy : j = y then
    -- todo: convert as well?
    have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
    · obtain ⟨s, hs⟩ := M.hAₗ.apply ◩x y
      cases s <;> tauto
    have hPC : (-M.D · y / M.Aₗ x y) ∈ VecSet c₀ c₁
    · cases hAxy with
      | inl h1 =>
        simp only [h1, div_one]
        exact neg_vec_in_vecSet (hMD y)
      | inr h9 =>
        simp only [h9, neg_div_neg_eq, div_one]
        exact hMD y
    simp only [Matrix.toRows₂_apply, Matrix.shortTableauPivot_eq, Matrix.fromRows_apply_inl,
      Matrix.replicateRow_apply, one_div, Matrix.of_apply, reduceCtorEq, ↓reduceIte,
      Matrix.fromRows_apply_inr]
    simp only [hjy, if_true]
    exact hPC
  else
    have hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := sorry -- hAᵣ
    let A : Matrix (Unit ⊕ Xᵣ) (Unit ⊕ Unit) ℚ :=
      Matrix.of (fun i' j' => i'.casesOn (j'.casesOn ↓↓(M.Aₗ x y) ↓↓(M.Aₗ x j)) (j'.casesOn ↓(M.D · y) ↓(M.D · j)))
    have hA : A.IsTotallyUnimodular := sorry -- hAₗ
    have hA₁₁ : A ◩() ◩() ≠ 0 := sorry -- hAxy
    have hA₂₁ : (A ◪· ◩()) ∈ VecSet c₀ c₁ := sorry -- hMD y
    have hA₂₂ : (A ◪· ◪()) ∈ VecSet c₀ c₁ := sorry -- hMD j
    have final := pivot_in_vecSet hc hA hA₁₁ hA₂₁ hA₂₂
    convert final
    simp [hjy, A]

lemma test (X Y : Type) (D : Matrix X Y ℚ) (a : X → ℚ) (y : Y) : (fun x => -D x y) = a ↔ -(fun x => D x y) = a := by
  exact Eq.congr_right rfl

lemma MatrixLikeSum3.shortTableauPivot_D_hasColsIn' {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0)
    (hMD : ∀ j, (M.D · j) ∈ VecSet c₀ c₁) :
    ∀ j, ((M.D.shortTableauPivotOuterRow (M.Aₗ x) y) · j) ∈ VecSet c₀ c₁ := by
  simp only [Matrix.toRows₂_apply, Matrix.shortTableauPivot_eq, Matrix.fromRows_apply_inl,
    Matrix.replicateRow_apply, one_div, Matrix.of_apply, reduceCtorEq, ↓reduceIte,
    Matrix.fromRows_apply_inr]
  intro j
  have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
  · obtain ⟨s, hs⟩ := M.hAₗ.apply ◩x y
    cases s <;> tauto
  have hPC : (-M.D · y / M.Aₗ x y) ∈ VecSet c₀ c₁
  · cases hAxy with
    | inl h1 =>
      simp only [h1, div_one]
      exact neg_vec_in_vecSet (hMD y)
    | inr h9 =>
      simp only [h9, neg_div_neg_eq, div_one]
      exact hMD y
  if hjy : j = y then
    simp only [hjy, if_true]
    exact hPC
  else
    simp only [hjy, if_false]
    simp_rw [div_mul_comm, sub_eq_add_neg, ←neg_mul, ←neg_div]
    have t : -M.Aₗ x j / M.Aₗ x y ∈ SignType.cast.range := sorry
    obtain ⟨s, hs⟩ := t
    cases s with
    | zero =>
        simp only [← hs, SignType.zero_eq_zero, SignType.coe_zero, zero_mul, add_zero,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hMD j
    | neg =>
        rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
        simp only [← hs, neg_mul, one_mul, ← sub_eq_add_neg, Set.mem_insert_iff, Set.mem_singleton_iff]
        sorry
    | pos =>
        rw [SignType.pos_eq_one, SignType.coe_one] at hs
        simp only [← hs, one_mul, Set.mem_insert_iff, Set.mem_singleton_iff]

        sorry

-- crux of lemma 59
lemma MatrixLikeSum3.shortTableauPivot_D_hasColsIn {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.D.shortTableauPivotOuterRow (M.Aₗ x) y).HasColsIn c₀ c₁ := by
  intro j
  simp only [Matrix.toRows₂_apply, Matrix.shortTableauPivot_eq, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.of_apply, Matrix.replicateRow_apply, one_div, reduceCtorEq, if_false]
  have hDy := M.hD y
  if hjy : j = y then
    simp only [hjy, if_true]
    have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
    · obtain ⟨s, hs⟩ := M.hAₗ.apply ◩x y
      cases s <;> tauto
    cases hAxy with
    | inl h1 =>
      simp only [h1, div_one, test, neg_eq_iff_eq_neg, neg_zero, neg_neg, neg_sub]
      tauto
    | inr h9 =>
      simp only [h9, neg_div_neg_eq, div_one]
      exact hDy
  else
    simp only [hjy, if_false]
    simp_rw [div_mul_comm, sub_eq_add_neg, ←neg_mul, ←neg_div]
    have hDj := M.hD j
    -- have hdiv : (fun x => -M.Aₗ x j / M.Aₗ x y * M.D x y).HasColsIn c₀ c₁
    -- · sorry
    -- · obtain ⟨Aₗxy, hAₗxy⟩ := M.hAₗ.apply ◩x y
    --   obtain ⟨Aₗxj, hAₗxj⟩ := M.hAₗ.apply ◩x j
    --   cases Aₗxj <;> cases Aₗxy
    --   <;> rw [Matrix.fromRows_apply_inl] at hAₗxj hAₗxy
    --   <;> rw [←hAₗxj, ←hAₗxy]
    --   <;> simp
    if h0 : -M.Aₗ x j / M.Aₗ x y = 0 then
      simp_rw [h0, zero_mul, add_zero, ←sub_eq_add_neg]
      exact hDj
    else

      sorry -- 7 x 7 x 2 cases

def MatrixLikeSum3.shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁ where
  Aₗ  := M.Aₗ.shortTableauPivot x y
  D   := M.D.shortTableauPivotOuterRow (M.Aₗ x) y
  Aᵣ  := M.Aᵣ
  hAₗ := M.shortTableauPivot_hAₗ hxy
  hD  := M.shortTableauPivot_D_hasColsIn hxy
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
