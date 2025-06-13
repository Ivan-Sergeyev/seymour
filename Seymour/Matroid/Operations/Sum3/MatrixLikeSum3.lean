import Seymour.Matroid.Operations.Sum3.CanonicalSigningSum3


/-! # Family of 3-sum-like matrices -/

/-! ## Definition -/

/-- Structural data of 3-sum-like matrices. -/
structure MatrixLikeSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (c₀ c₁ : Xᵣ → ℚ) where
  Aₗ  : Matrix Xₗ Yₗ ℚ
  D   : Matrix Xᵣ Yₗ ℚ
  Aᵣ  : Matrix Xᵣ Yᵣ ℚ
  hAₗ : (Aₗ ⊟ D).IsTotallyUnimodular
  hD  : D.HasColsIn' c₀ c₁
  hAᵣ : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ Aᵣ).IsTotallyUnimodular

/-- The resulting 3-sum-like matrix. -/
abbrev MatrixLikeSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) ℚ :=
  ⊞ M.Aₗ 0 M.D M.Aᵣ


/-! ## Pivoting -/

/-!
  In this section we prove that pivoting in the top-left block of a 3-sum-like matrix yields a 3-sum-like matrix.
-/

private lemma neg_in_ccVecSet {X F : Type} [Zero F] [Neg F] [Sub F] {c₀ : X → F} {c₁ : X → F}
    {v : X → F} (hv : v ∈ ccVecSet c₀ c₁) : -v ∈ ccVecSet c₀ c₁ :=
  sorry

private lemma shortTableauPivot_ccVecSet_0 {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F}
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 0) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  simp [hA₁₁, hA₁₂, hA₂₂]

private lemma shortTableauPivot_ccVecSet_1 {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 1) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
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
      exact neg_in_ccVecSet hA₂₁'
    | inr hA₂₂c =>
      sorry -- 6 x 6 cases

set_option maxHeartbeats 0 in
private lemma shortTableauPivot_ccVecSet_9 {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = -1) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
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
      sorry
      -- <;> try aesop
      all_goals sorry

private lemma pivot_in_ccVecSet {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (hc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular)
    {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() ≠ 0) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  sorry -- reduction to 3 cases above by multiplying first row by A ◩() ◩()

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

lemma MatrixLikeSum3.shortTableauPivot_D_hasColsIn {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    ∀ j : Yₗ, ((M.D.shortTableauPivotOuterRow (M.Aₗ x) y) · j) ∈ ccVecSet c₀ c₁ := by
  intro j
  if hjy : j = y then
    have hAxy : M.Aₗ x y = 1 ∨ M.Aₗ x y = -1
    · obtain ⟨s, hs⟩ := M.hAₗ.apply ◩x y
      cases s <;> tauto
    have hPC : (-M.D · y / M.Aₗ x y) ∈ ccVecSet c₀ c₁
    · cases hAxy with
      | inl h1 =>
        simp only [h1, div_one]
        exact neg_in_ccVecSet (M.hD y)
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
    simpa [hjy] using pivot_in_ccVecSet (M.hAᵣ.submatrix id Sum.inl) hA hxy (M.hD y) (M.hD j)

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
