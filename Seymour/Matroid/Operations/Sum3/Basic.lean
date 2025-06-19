import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


/-! # Matrix-level 3-sum -/

/-! ## Additional notation for convenience -/

@[simp]
def equivUnitSumUnit : Unit ⊕ Unit ≃ Fin 2 :=
  ⟨(·.casesOn ↓0 ↓1), ![◩(), ◪()], (·.casesOn (by simp) (by simp)), (by fin_cases · <;> simp)⟩

/-!
  We define the unsigned and the signed version of the special cases of the 3×3 submatrix in the intersection of the summands.
-/

/-- Unsigned version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₀ (F : Type) [Zero F] [One F] : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 1; 0, 1, 1; 1, 1, 0]

/-- Unsigned version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₁ (F : Type) [Zero F] [One F] : Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 1; 0, 1, 1; 1, 1, 0]

/-- Signed version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 1; 0, -1, 1; 1, 1, 0]

/-- Signed version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ :=
  matrix3x3unsigned₁ ℚ


/-! ## Definition -/

/-- Structural data of 3-sum of matrices. -/
structure MatrixSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (F : Type) where
  Aₗ  : Matrix (Xₗ ⊕ Fin 1) (Yₗ ⊕ Fin 2) F
  Dₗ  : Matrix (Fin 2) Yₗ F
  D₀ₗ : Matrix (Fin 2) (Fin 2) F
  D₀ᵣ : Matrix (Fin 2) (Fin 2) F
  Dᵣ  : Matrix Xᵣ (Fin 2) F
  Aᵣ  : Matrix (Fin 2 ⊕ Xᵣ) (Fin 1 ⊕ Yᵣ) F

/-- The bottom-left block of 3-sum. -/
noncomputable abbrev MatrixSum3.D {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 2 ⊕ Xᵣ) (Yₗ ⊕ Fin 2) F :=
  ⊞ S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ

/-- The resulting matrix of 3-sum. -/
noncomputable def MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin 1) ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ (Fin 1 ⊕ Yᵣ)) F :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ


/-! ## Conversion of summands -/

-- todo: maybe move definitions in comments below from MatroidSum3.lean here
-- /-- Converts the right summand matrix to block form. -/
-- def Matrix.toBlockSummandₗ {α : Type} {Xₗ Yₗ : Set α} {F : Type} (Bₗ : Matrix Xₗ Yₗ F) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
--     Matrix (((Xₗ \ {x₀.val, x₁.val, x₂.val}).Elem ⊕ Fin 1) ⊕ Fin 2) (((Yₗ \ {y₀.val, y₁.val, y₂.val}).Elem ⊕ Fin 2) ⊕ Fin 1) F :=
--   Bₗ.submatrix
--     (·.casesOn (·.casesOn (fun i => ⟨i.val, i.property.left⟩) ![x₂]) ![x₀, x₁])
--     (·.casesOn (·.casesOn (fun i => ⟨i.val, i.property.left⟩) ![y₀, y₁]) ![y₂])

-- /-- Converts the left summand matrix to block form. -/
-- def Matrix.toBlockSummandᵣ {α : Type} {Xᵣ Yᵣ : Set α} {F : Type} (Bᵣ : Matrix Xᵣ Yᵣ F) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
--     Matrix (Fin 1 ⊕ (Fin 2 ⊕ (Xᵣ \ {x₀.val, x₁.val, x₂.val}).Elem)) (Fin 2 ⊕ (Fin 1 ⊕ (Yᵣ \ {y₀.val, y₁.val, y₂.val}).Elem)) F :=
--   Bᵣ.submatrix
--     (·.casesOn ![x₂] (·.casesOn ![x₀, x₁] (fun i => ⟨i.val, i.property.left⟩)))
--     (·.casesOn ![y₀, y₁] (·.casesOn ![y₂] (fun i => ⟨i.val, i.property.left⟩)))

/-- Constructs 3-sum from summands in block form. -/
def MatrixSum3.fromBlockSummands {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type}
    (Bₗ : Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) F)
    (Bᵣ : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) F) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F where
  Aₗ  := Bₗ.toBlocks₁₁
  Dₗ  := Bₗ.toBlocks₂₁.toCols₁
  D₀ₗ := Bₗ.toBlocks₂₁.toCols₂
  D₀ᵣ := Bᵣ.toBlocks₂₁.toRows₁
  Dᵣ  := Bᵣ.toBlocks₂₁.toRows₂
  Aᵣ  := Bᵣ.toBlocks₂₂

/-- Reconstructs the left summand from the matrix 3-sum structure. -/
abbrev MatrixSum3.Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) F :=
  ⊞ S.Aₗ 0 (S.Dₗ ◫ S.D₀ₗ) !![S.Aᵣ ◩0 ◩0; S.Aᵣ ◩1 ◩0]

/-- Reconstructs the right summand from the matrix 3-sum structure. -/
abbrev MatrixSum3.Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) F :=
  ⊞ !![S.Aₗ ◪0 ◪0, S.Aₗ ◪0 ◪1] 0 (S.D₀ᵣ ⊟ S.Dᵣ) S.Aᵣ

/-- If the 3-sum is constructed from summands in block form, reconstructing the left summand yields the original one. -/
lemma MatrixSum3.fromBlockSummands_Bₗ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F]
    (Bₗ : Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) F)
    (Bᵣ : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) F)
    (hBₗ : Bₗ ◪0 ◪0 = Bᵣ ◪◩0 ◪◩0 ∧ Bₗ ◪1 ◪0 = Bᵣ ◪◩1 ◪◩0 ∧ ∀ i, Bₗ ◩i ◪0 = 0) :
    (MatrixSum3.fromBlockSummands Bₗ Bᵣ).Bₗ = Bₗ := by
  ext i j
  cases j with
  | inl jₗ => cases jₗ <;> cases i <;> tauto
  | inr jᵣ =>
    fin_cases jᵣ
    cases i with
    | inl iₗ => have := hBₗ.right.right iₗ; tauto
    | inr iᵣ => fin_cases iᵣ <;> tauto

/-- If the 3-sum is constructed from summands in block form, reconstructing the right summand yields the original one. -/
lemma MatrixSum3.fromBlockSummands_Bᵣ_eq {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F]
    (Bₗ : Matrix ((Xₗ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Fin 1) F)
    (Bᵣ : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ)) F)
    (hBᵣ : Bᵣ ◩0 ◩0 = Bₗ ◩◪0 ◩◪0 ∧ Bᵣ ◩0 ◩1 = Bₗ ◩◪0 ◩◪1 ∧ ∀ i, Bᵣ ◩0 ◪i = 0) :
    (MatrixSum3.fromBlockSummands Bₗ Bᵣ).Bᵣ = Bᵣ := by
  ext i j
  cases i with
  | inl iₗ =>
    fin_cases iₗ
    cases j with
    | inl jₗ => fin_cases jₗ <;> tauto
    | inr jᵣ => have := hBᵣ.right.right jᵣ; tauto
  | inr iᵣ => cases iᵣ <;> cases j <;> tauto

/-- The 3×3 submatrix of the reconstructed left summand in the intersection of the summands. -/
abbrev MatrixSum3.Sₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 3) (Fin 3) F :=
  S.Bₗ.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]

/-- The 3×3 submatrix of the reconstructed right summand in the intersection of the summands. -/
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

/-- Reconstructed left summand is totally unimodular. -/
abbrev MatrixSum3.HasTuBₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Bₗ.IsTotallyUnimodular

/-- Reconstructed right summand is totally unimodular. -/
abbrev MatrixSum3.HasTuBᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  S.Bᵣ.IsTotallyUnimodular


/-! ## Transposition -/

def MatrixSum3.transpose {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
  MatrixSum3 Yᵣ Xᵣ Yₗ Xₗ F where
  Aₗ  := S.Aᵣ.transpose.submatrix Sum.swap Sum.swap
  Dₗ  := S.Dᵣ.transpose
  D₀ₗ := S.D₀ᵣ.transpose
  D₀ᵣ := S.D₀ₗ.transpose
  Dᵣ  := S.Dₗ.transpose
  Aᵣ  := S.Aₗ.transpose.submatrix Sum.swap Sum.swap

private def backwards {α β γ δ : Type} : (α ⊕ β) ⊕ (γ ⊕ δ) ≃ (δ ⊕ γ) ⊕ (β ⊕ α) :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.sumComm γ δ) (Equiv.sumComm α β))

lemma MatrixSum3.transpose_matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F)
    (hS : S.D₀ₗ = S.D₀ᵣ) :
    S.transpose.matrix = S.matrix.transpose.submatrix backwards backwards := by
  ext (_|(_|_)) ((_|_)|_)
  all_goals try rfl
  all_goals simp [hS, backwards, MatrixSum3.transpose, MatrixSum3.matrix, Matrix.fromBlocks_transpose,
      Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
