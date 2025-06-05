import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


/-! # Matrix-level 3-sum -/

/-! ## Additional notation for convenience -/

/-!
  We provide canonical bijections between `Fin 1` or `Fin 2` and corresponding elements.
-/

@[simp]
def equivFin1 {α : Type} {Z : Set α} (z : Z) : Fin 1 ≃ Set.Elem {z.val} :=
  Equiv.ofUnique (Fin 1) (Set.Elem {z.val})

@[simp]
def equivFin2 {α : Type} [DecidableEq α] {Z : Set α} {z₀ z₁ : Z} (hzz : z₁ ≠ z₀) : Fin 2 ≃ Set.Elem {z₀.val, z₁.val} :=
⟨
  ![⟨z₀.val, Set.mem_insert z₀.val {z₁.val}⟩, ⟨z₁.val, Set.mem_insert_of_mem z₀.val rfl⟩],
  (if ·.val = z₀.val then 0 else 1),
  (if h0 : · = 0 then by simp [h0] else have := fin2_eq_1_of_ne_0 h0; by aesop),
  ↓(by aesop)
⟩

@[simp]
def equivUnitSumUnit : Fin 2 ≃ Unit ⊕ Unit :=
  ⟨![◩(), ◪()], (·.casesOn ↓0 ↓1), (by fin_cases · <;> simp), (·.casesOn (by simp) (by simp))⟩

/-!
  We define the unsigned and the signed version of the special cases of the 3×3 submatrix in the intersection of the summands.
-/

/-- Unsigned version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₀ (F : Type) [Zero F] [One F] :
    Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 1; 0, 1, 1; 1, 1, 0]

/-- Unsigned version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₁ (F : Type) [Zero F] [One F] :
    Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 1; 0, 1, 1; 1, 1, 0]

/-- Signed version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₀ :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 1; 0, -1, 1; 1, 1, 0]

/-- Signed version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₁ :
    Matrix (Fin 3) (Fin 3) ℚ :=
  matrix3x3unsigned₁ ℚ


/-! ## Definition -/

/-- Structural data of 3-sum of matrices. -/
structure MatrixSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (F : Type) where
  Aₗ : Matrix (Xₗ ⊕ Fin 1) (Yₗ ⊕ Fin 2) F
  Dₗ : Matrix (Fin 2) Yₗ F
  D₀ₗ : Matrix (Fin 2) (Fin 2) F
  D₀ᵣ : Matrix (Fin 2) (Fin 2) F
  Dᵣ : Matrix Xᵣ (Fin 2) F
  Aᵣ : Matrix (Fin 2 ⊕ Xᵣ) (Fin 1 ⊕ Yᵣ) F

/-- The bottom-left block of 3-sum. -/
noncomputable abbrev MatrixSum3.D {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 2 ⊕ Xᵣ) (Yₗ ⊕ Fin 2) F :=
  ⊞ S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ

/-- The resulting matrix of 3-sum. -/
noncomputable def MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin 1) ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ (Fin 1 ⊕ Yᵣ)) F :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ

/-! ## Transposition -/

def MatrixSum3.transpose {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
  MatrixSum3 Yᵣ Xᵣ Yₗ Xₗ F where
  Aₗ := S.Aᵣ.transpose.submatrix Sum.swap Sum.swap
  Dₗ := S.Dᵣ.transpose
  D₀ₗ := S.D₀ᵣ.transpose
  D₀ᵣ := S.D₀ₗ.transpose
  Dᵣ := S.Dₗ.transpose
  Aᵣ := S.Aₗ.transpose.submatrix Sum.swap Sum.swap

def backwards {α β γ δ : Type} : (α ⊕ β) ⊕ (γ ⊕ δ) ≃ (δ ⊕ γ) ⊕ (β ⊕ α) :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.sumComm _ _))

lemma MatrixSum3.transpose_matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F)
    (hS : S.D₀ₗ = S.D₀ᵣ) :
    S.transpose.matrix = S.matrix.transpose.submatrix backwards backwards := by
  simp [backwards, MatrixSum3.transpose, MatrixSum3.matrix]
  ext (_ | j) (i | _)
  · rfl
  · rfl
  · cases j with
    | inl =>
      cases i with
      | inl => simp
      | inr => simp [hS]
    | inr =>
      cases i with
      | inl => simp [hS, Matrix.fromBlocks_transpose, Matrix.transpose_nonsing_inv, Matrix.mul_assoc, -Matrix.transpose_apply]
      | inr => simp
  · rfl

/-! ## Re-construction of summands -/

/-- Reconstructed left summand. -/
abbrev MatrixSum3.Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) F :=
  ⊞ S.Aₗ 0 (S.Dₗ ◫ S.D₀ₗ) !![1; 1]

/-- Reconstructed right summand. -/
abbrev MatrixSum3.Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) F :=
  ⊞ !![1, 1] 0 (S.D₀ᵣ ⊟ S.Dᵣ) S.Aᵣ

/-- Reconstructed left summand's 3×3 submatrix in the intersection of the summands. -/
abbrev MatrixSum3.Sₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 3) (Fin 3) F :=
  S.Bₗ.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]

/-- Reconstructed right summand's 3×3 submatrix in the intersection of the summands. -/
abbrev MatrixSum3.Sᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 3) (Fin 3) F :=
  S.Bᵣ.submatrix ![◪◩0, ◪◩1, ◩0] ![◩0, ◩1, ◪◩0]


/-! ## Correctness -/

/-- Equality of absolute values of the 2×2 submatrices in the intersection of the summands. -/
abbrev MatrixSum3.HasEqD₀ₗD₀ᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  S.D₀ₗ = S.D₀ᵣ

/-- Equality of absolute values of the 3×3 submatrices in the intersection of the summands. -/
abbrev MatrixSum3.HasEqSₗSᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  S.Sₗ = S.Sᵣ

/-- Equality of the 2×2 submatrices in the intersection of the summands. -/
abbrev MatrixSum3.HasEqAbsD₀ₗD₀ᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [LinearOrderedAddCommGroup F]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  |S.D₀ₗ| = |S.D₀ᵣ|

/-- Equality of the 3×3 submatrices in the intersection of the summands. -/
abbrev MatrixSum3.HasEqAbsSₗSᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] [LinearOrderedAddCommGroup F]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  |S.Sₗ| = |S.Sᵣ|

/-- Absolute values of the 3×3 submatrices in the intersection of the summands match the first special case. -/
abbrev MatrixSum3.Has3x3abs₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] [LinearOrderedAddCommGroup F]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  |S.Sₗ| = matrix3x3unsigned₀ F ∧ |S.Sᵣ| = matrix3x3unsigned₀ F

/-- Absolute values of the 3×3 submatrices in the intersection of the summands match the second special case. -/
abbrev MatrixSum3.Has3x3abs₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] [LinearOrderedAddCommGroup F]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  |S.Sₗ| = matrix3x3unsigned₁ F ∧ |S.Sᵣ| = matrix3x3unsigned₁ F

/-- Absolute values of the 3×3 submatrices in the intersection of the summands match the first or the second special case. -/
abbrev MatrixSum3.Has3x3abs₀₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] [LinearOrderedAddCommGroup F]
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) : Prop :=
  S.Has3x3abs₀ ∨ S.Has3x3abs₁

/-- The signed 3×3 submatrices in the intersection of the summands match the first special case. -/
abbrev MatrixSum3.Has3x3signed₀ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Sₗ = matrix3x3signed₀ ∧ S.Sᵣ = matrix3x3signed₀

/-- The signed 3×3 submatrices in the intersection of the summands match the second special case. -/
abbrev MatrixSum3.Has3x3signed₁ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Sₗ = matrix3x3signed₁ ∧ S.Sᵣ = matrix3x3signed₁

/-- The signed 3×3 submatrices in the intersection of the summands match the first or the second special case. -/
abbrev MatrixSum3.Has3x3signed₀₁ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Has3x3signed₀ ∨ S.Has3x3signed₁


/-! ## Total unimodularity of summands -/

/-- Reconstructed left summand has a totally unimodular signing. -/
abbrev MatrixSum3.HasTuSigningBₗ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  S.Bₗ.HasTuSigning

/-- Reconstructed right summand has a totally unimodular signing. -/
abbrev MatrixSum3.HasTuSigningBᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  S.Bᵣ.HasTuSigning

/-- Both reconstructed summands have a totally unimodular signing. -/
abbrev MatrixSum3.HasTuSigningBₗᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  S.HasTuSigningBₗ ∧ S.HasTuSigningBᵣ

/-- Reconstructed left summand is totally unimodular. -/
abbrev MatrixSum3.HasTuBₗ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Bₗ.IsTotallyUnimodular

/-- Reconstructed right summand is totally unimodular. -/
abbrev MatrixSum3.HasTuBᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Bᵣ.IsTotallyUnimodular

/-- Both reconstructed summands are totally unimodular. -/
abbrev MatrixSum3.HasTuBₗᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.HasTuBₗ ∧ S.HasTuBᵣ
