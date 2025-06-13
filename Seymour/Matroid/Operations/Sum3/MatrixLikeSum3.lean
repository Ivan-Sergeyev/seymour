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

private lemma ccVecSet_cases {X F : Type} [Zero F] [Neg F] [Sub F] {c₀ : X → F} {c₁ : X → F} {v : X → F} :
    v ∈ ccVecSet c₀ c₁ ↔ v = 0 ∨ v = c₀ ∨ v = -c₀ ∨ v = c₁ ∨ v = -c₁ ∨ v = c₀ - c₁ ∨ v = c₁ - c₀ :=
  Set.mem_def

private lemma neg_in_ccVecSet {X F : Type} [Field F] {c₀ : X → F} {c₁ : X → F} {v : X → F} (hv : v ∈ ccVecSet c₀ c₁) :
    -v ∈ ccVecSet c₀ c₁ := by
  rw [ccVecSet_cases] at hv ⊢
  rcases hv with (hv | hv | hv | hv | hv | hv | hv)
  all_goals
    rw [hv]
    ring_nf
    simp only [true_or, or_true]

private lemma Matrix.shortTableauPivot_col_in_ccVecSet_0 {X F : Type} [Field F] [DecidableEq X] {c₀ : X → F} {c₁ : X → F}
    (A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 0) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  simp [hA₁₁, hA₁₂, hA₂₂]

@[simp]
private abbrev matrixStackTwoValsTwoCols9 {X F : Type} [One F] [Neg F] (u : X → F) (v : X → F) :
    Matrix (Unit ⊕ X) (Unit ⊕ Unit) F :=
  ▮(·.casesOn ↓1 u) ◫ ▮(·.casesOn ↓(-1) v)

set_option maxHeartbeats 0 in
private lemma matrixStackTwoValsTwoCols9_shortTableauPivot {X F : Type} [Field F] [DecidableEq X]
    {c₀ : X → F} {c₁ : X → F} (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) (u : X → F) (v : X → F)
    (hA : (matrixStackTwoValsTwoCols9 u v).IsTotallyUnimodular)
    (hucc : u ∈ ccVecSet c₀ c₁) (hvcc : v ∈ ccVecSet c₀ c₁) :
    (((matrixStackTwoValsTwoCols9 u v).shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  simp
  rw [show (fun x : X => v x + u x) = v + u by rfl]
  cases ccVecSet_cases.→ hucc with
  | inl hu0 =>
    simp [hu0]
    exact hvcc
  | inr huc =>
    cases ccVecSet_cases.→ hvcc with
    | inl hv0 =>
      simp [hv0]
      right
      exact huc
    | inr hvc =>
      rcases huc with (hu | hu | hu | hu | hu | hu) <;> rcases hvc with (hv | hv | hv | hv | hv | hv)
      <;> simp [hu, hv]
      <;> clear hu hv
      all_goals ring_nf
      all_goals try tauto
      all_goals left
      all_goals sorry -- prove using TUness

private lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_9 {X F : Type} [Field F] [DecidableEq X]
    {c₀ : X → F} {c₁ : X → F} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = -1) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁)
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  have A_eq : A = matrixStackTwoValsTwoCols9 (fun x => A ◪x ◩()) fun x => A ◪x ◪()
  · ext (_|_) (_|_)
    · exact hA₁₁
    · exact hA₁₂
    · simp
    · simp
  exact A_eq ▸ matrixStackTwoValsTwoCols9_shortTableauPivot hcc (A ◪· ◩()) (A ◪· ◪()) (A_eq ▸ hA) hA₂₁ hA₂₂

private lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_1 {X F : Type} [Field F] [DecidableEq X]
    {c₀ : X → F} {c₁ : X → F} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() = 1) (hA₁₂ : A ◩() ◪() = 1) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁)
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
  sorry -- TODO reduce to `Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet_9`

private lemma Matrix.IsTotallyUnimodular.shortTableauPivot_col_in_ccVecSet {X F : Type} [Field F] [DecidableEq X]
    {c₀ : X → F} {c₁ : X → F} {A : Matrix (Unit ⊕ X) (Unit ⊕ Unit) F} (hA : A.IsTotallyUnimodular)
    (hA₁₁ : A ◩() ◩() ≠ 0) (hA₂₁ : (A ◪· ◩()) ∈ ccVecSet c₀ c₁) (hA₂₂ : (A ◪· ◪()) ∈ ccVecSet c₀ c₁)
    (hcc : (▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular) :
    ((A.shortTableauPivot ◩() ◩()) ◪· ◪()) ∈ ccVecSet c₀ c₁ := by
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
    let q : Unit ⊕ X → F := (·.casesOn ↓(-1) ↓1)
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
          (show _ ∈ ccVecSet c₀ c₁ by simp [*, q, neg_in_ccVecSet])
        using 2
      simp only [shortTableauPivot_eq, of_apply, reduceCtorEq, ↓reduceIte]
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

private abbrev Matrix.shortTableauPivotOuterRow {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (y : Y) :
    Matrix X Y ℚ :=
  ((▬r ⊟ A).shortTableauPivot ◩() y).toRows₂

private lemma MatrixLikeSum3.shortTableauPivot_Aₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.Aₗ.shortTableauPivot x y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₁ := by
  ext
  simp

private lemma MatrixLikeSum3.shortTableauPivot_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) (x : Xₗ) (y : Yₗ) :
    M.D.shortTableauPivotOuterRow (M.Aₗ x) y = ((M.Aₗ ⊟ M.D).shortTableauPivot ◩x y).toRows₂ := by
  ext
  simp

private lemma MatrixLikeSum3.shortTableauPivot_hAₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) :
    (M.Aₗ.shortTableauPivot x y ⊟ M.D.shortTableauPivotOuterRow (M.Aₗ x) y).IsTotallyUnimodular := by
  rw [M.shortTableauPivot_D_eq x y, M.shortTableauPivot_Aₗ_eq x y, Matrix.fromRows_toRows]
  exact M.hAₗ.shortTableauPivot hxy

private lemma MatrixLikeSum3.shortTableauPivot_D_cols_in_ccVecSet {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ]
    {c₀ c₁ : Xᵣ → ℚ} (M : MatrixLikeSum3 Xₗ Yₗ Xᵣ Yᵣ c₀ c₁) {x : Xₗ} {y : Yₗ} (hxy : M.Aₗ x y ≠ 0) (j : Yₗ) :
    ((M.D.shortTableauPivotOuterRow (M.Aₗ x) y) · j) ∈ ccVecSet c₀ c₁ := by
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
