import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


/-! # Matrix-level 3-sum -/

/-! ## Additional notation for convenience -/

/-!
  We create aliases for `Fin 1` and `Fin 2` and `Fin 3` used to represent different index sets.
-/

/-- Fin 1 representing `x₂`. -/
abbrev Fin1X := Fin 1

/-- Fin 1 representing `y₂`. -/
abbrev Fin1Y := Fin 1

/-- Fin 2 representing `x₀`, `x₁`. -/
abbrev Fin2X := Fin 2

/-- Fin 2 representing `y₀`, `y₁`. -/
abbrev Fin2Y := Fin 2

/-- Fin 3 representing `x₀`, `x₁`, `x₂`. -/
abbrev Fin3X := Fin 3

/-- Fin 3 representing `y₀`, `y₁`, `y₂`. -/
abbrev Fin3Y := Fin 3

/-!
  We provide canonical bijections between `Fin 1` or `Fin 2` and corresponding elements.
-/

abbrev equivFin1X {α : Type} {X : Set α} (x : X) : Fin1X ≃ Set.Elem {x.val} := Equiv.ofUnique Fin1X (Set.Elem {x.val})
abbrev equivFin1Y {α : Type} {Y : Set α} (y : Y) : Fin1Y ≃ Set.Elem {y.val} := Equiv.ofUnique Fin1Y (Set.Elem {y.val})

def equivFin2 {α : Type} [DecidableEq α] {Z : Set α} {z₀ z₁ : Z} (hzz : z₁ ≠ z₀) : Fin 2 ≃ Set.Elem {z₀.val, z₁.val} :=
⟨
  ![⟨z₀.val, Set.mem_insert z₀.val {z₁.val}⟩, ⟨z₁.val, Set.mem_insert_of_mem z₀.val rfl⟩],
  (if ·.val = z₀.val then 0 else 1),
  (if h0 : · = 0 then by simp [h0] else have := fin2_eq_1_of_ne_0 h0; by aesop),
  ↓(by aesop)
⟩

abbrev equivFin2X {α : Type} [DecidableEq α] {X : Set α} {x₀ x₁ : X} (hxx : x₁ ≠ x₀) : Fin2X ≃ Set.Elem {x₀.val, x₁.val} := equivFin2 hxx
abbrev equivFin2Y {α : Type} [DecidableEq α] {Y : Set α} {y₀ y₁ : Y} (hyy : y₁ ≠ y₀) : Fin2X ≃ Set.Elem {y₀.val, y₁.val} := equivFin2 hyy

/-!
  We define the unsigned and the signed version of the special cases of the 3×3 submatrix in the intersection of the summands.
-/

/-- Unsigned version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₀ (F : Type) [Zero F] [One F] :
    Matrix Fin3X Fin3Y F :=
  !![1, 0, 1; 0, 1, 1; 1, 1, 0]

/-- Unsigned version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3unsigned₁ (F : Type) [Zero F] [One F] :
    Matrix Fin3X Fin3Y F :=
  !![1, 1, 1; 0, 1, 1; 1, 1, 0]

/-- Signed version of the first special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₀ :
    Matrix Fin3X Fin3Y ℚ :=
  !![1, 0, 1; 0, -1, 1; 1, 1, 0]

/-- Signed version of the second special case of the 3×3 submatrix in the intersection of the summands. -/
@[simp]
abbrev matrix3x3signed₁ :
    Matrix Fin3X Fin3Y ℚ :=
  matrix3x3unsigned₁ ℚ


/-! ## Definition -/

/-- Structural data of 3-sum of matrices. -/
structure MatrixSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (F : Type) where
  Aₗ : Matrix (Xₗ ⊕ Fin1X) (Yₗ ⊕ Fin2Y) F
  Dₗ : Matrix Fin2X Yₗ F
  D₀ₗ : Matrix Fin2X Fin2Y F
  D₀ᵣ : Matrix Fin2X Fin2Y F
  Dᵣ : Matrix Xᵣ Fin2Y F
  Aᵣ : Matrix (Fin2X ⊕ Xᵣ) (Fin1Y ⊕ Yᵣ) F

/-- The bottom-left block of 3-sum. -/
noncomputable abbrev MatrixSum3.D {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin2X ⊕ Xᵣ) (Yₗ ⊕ Fin2Y) F :=
  ⊞ S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ

/-- The resulting matrix of 3-sum. -/
noncomputable def MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Field F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin1X) ⊕ (Fin2X ⊕ Xᵣ)) ((Yₗ ⊕ Fin2Y) ⊕ (Fin1Y ⊕ Yᵣ)) F :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ


/-! ## Re-construction of summands -/

/-- Reconstructed left summand. -/
abbrev MatrixSum3.Bₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix ((Xₗ ⊕ Fin1X) ⊕ Fin2X) ((Yₗ ⊕ Fin2Y) ⊕ Fin 1) F :=
  ⊞ S.Aₗ 0 (S.Dₗ ◫ S.D₀ₗ) !![1; 1]

/-- Reconstructed right summand. -/
abbrev MatrixSum3.Bᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix (Fin 1 ⊕ (Fin2X ⊕ Xᵣ)) (Fin2Y ⊕ (Fin1Y ⊕ Yᵣ)) F :=
  ⊞ !![1, 1] 0 (S.D₀ᵣ ⊟ S.Dᵣ) S.Aᵣ

/-- Reconstructed left summand's 3×3 submatrix in the intersection of the summands. -/
abbrev MatrixSum3.Sₗ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix Fin3X Fin3Y F :=
  S.Bₗ.submatrix ![◪0, ◪1, ◩◪0] ![◩◪0, ◩◪1, ◪0]

/-- Reconstructed right summand's 3×3 submatrix in the intersection of the summands. -/
abbrev MatrixSum3.Sᵣ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Zero F] [One F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Matrix Fin3X Fin3Y F :=
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
