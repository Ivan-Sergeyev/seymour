import Seymour.Results.HardDirection

/-! # Formally verified summary of the Seymour project -/

open scoped Matrix Set.Notation

/-! ## Preliminaries -/

-- what `Disjoint` means
recall Set.disjoint_iff_inter_eq_empty {α : Type _} (X Y : Set α) :
  Disjoint X Y ↔ X ∩ Y = ∅

-- what `Matrix.submatrix` means
example {X X' Y Y' R : Type*} (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) (i : X') (j : Y') :
  (A.submatrix f g) i j = A (f i) (g j) := rfl

-- what is vector matroid
recall Matrix.toMatroid_indep_iff {α R : Type*} {X Y : Set α} [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
  A.toMatroid.Indep I ↔ I ⊆ Y ∧ LinearIndepOn R Aᵀ (Y ↓∩ I)

-- how standard representation is defined
recall StandardRepr.X {α R : Type*} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.Y {α R : Type*} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.B {α R : Type*} [DecidableEq α] (S : StandardRepr α R) : Matrix S.X S.Y R
recall StandardRepr.hXY {α R : Type*} [DecidableEq α] (S : StandardRepr α R) : Disjoint S.X S.Y
recall StandardRepr.decmemX {α R : Type*} [DecidableEq α] (S : StandardRepr α R) : ∀ a, Decidable (a ∈ S.X)
recall StandardRepr.decmemY {α R : Type*} [DecidableEq α] (S : StandardRepr α R) : ∀ a, Decidable (a ∈ S.Y)
/--
info: StandardRepr.mk.{u_1, u_2} {α : Type u_1} {R : Type u_2} [DecidableEq α] (X Y : Set α) (hXY : X ⫗ Y)
  (B : Matrix (↑X) (↑Y) R) (decmemX : (a : α) → Decidable (a ∈ X)) (decmemY : (a : α) → Decidable (a ∈ Y)) :
  StandardRepr α R
-/
#guard_msgs in
#check StandardRepr.mk

-- what is the matroid constructed from given standard representation
recall StandardRepr.toMatroid_indep_iff {α : Type*} [DecidableEq α] {R : Type*} [DivisionRing R]
    (S : StandardRepr α R) (I : Set α) :
  S.toMatroid.Indep I ↔ I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((Matrix.fromCols 1 S.B).submatrix id Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I)

-- how total unimodularity is defined
recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ Set.range SignType.cast

-- how regular matroid is defined
recall Matroid.IsRegular {α : Type*} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ A.toMatroid = M

-- how an element of set union is converted to disjoint union
recall Subtype.toSum {α : Type*} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

-- how matrix indexed by disjoint unions is converted to a matrix indexed by set unions
recall Matrix.toMatrixUnionUnion {α R : Type*} {T₁ T₂ S₁ S₂ : Set α}
    [∀ a, Decidable (a ∈ T₁)] [∀ a, Decidable (a ∈ T₂)] [∀ a, Decidable (a ∈ S₁)] [∀ a, Decidable (a ∈ S₂)]
    (A : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) R) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem R :=
  A.submatrix Subtype.toSum Subtype.toSum

-- syntactic sugar for the field on 2 elements
recall Z2 := Fin 2


/-! ## The 1-sum -/

-- how 1-sum of matrices is defined
recall matrixSum1 {R : Type*} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 0 Aᵣ

-- how 1-sum of standard representations is defined
recall standardReprSum1 {α : Type*} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Disjoint Sₗ.X Sᵣ.Y) (hYX : Disjoint Sₗ.Y Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  open scoped Classical in if
    Disjoint Sₗ.X Sᵣ.X ∧ Disjoint Sₗ.Y Sᵣ.Y
  then
    some ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
         exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      (matrixSum1 Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance⟩
  else
    none

-- how 1-sum of binary matroids is defined
recall Matroid.IsSum1of {α : Type*} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ hXY : Disjoint Sₗ.X Sᵣ.Y,
  ∃ hYX : Disjoint Sₗ.Y Sᵣ.X,
  standardReprSum1 hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

-- [theorem] any 1-sum of regular matroids is a regular matroid
recall Matroid.IsSum1of.isRegular {α : Type*} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.IsSum1of Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular
/--
info: 'Matroid.IsSum1of.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.IsSum1of.isRegular


/-! ## The 2-sum -/

-- how 2-sum of matrices is defined
recall matrixSum2 {R : Type*} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 (fun i j => c i * r j) Aᵣ

-- how 2-sum of standard representations is defined
recall standardReprSum2 {α : Type*} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y}) (hXY : Disjoint Sₗ.X Sᵣ.Y) (hYX : Disjoint Sₗ.Y Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  let Aₗ : Matrix (Sₗ.X \ {x}).Elem Sₗ.Y.Elem Z2 := Sₗ.B.submatrix Set.diff_subset.elem id -- the top submatrix of `Bₗ`
  let Aᵣ : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {y}).Elem Z2 := Sᵣ.B.submatrix id Set.diff_subset.elem -- the right submatrix of `Bᵣ`
  let r : Sₗ.Y.Elem → Z2 := Sₗ.B ⟨x, Set.mem_of_mem_inter_left (by rw [hXX]; rfl)⟩         -- the bottom row of `Bₗ`
  let c : Sᵣ.X.Elem → Z2 := (Sᵣ.B · ⟨y, Set.mem_of_mem_inter_right (by rw [hYY]; rfl)⟩)    -- the left column of `Bᵣ`
  open scoped Classical in if
    r ≠ 0 ∧ c ≠ 0
  then
    some ⟨
      (Sₗ.X \ {x}) ∪ Sᵣ.X,
      Sₗ.Y ∪ (Sᵣ.Y \ {y}),
      by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
         exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right,
            Sᵣ.hXY.disjoint_sdiff_right⟩⟩,
      (matrixSum2 Aₗ r Aᵣ c).toMatrixUnionUnion,
      inferInstance,
      inferInstance⟩
  else
    none

-- how 2-sum of binary matroids is defined
recall Matroid.IsSum2of {α : Type*} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ x y : α,
  ∃ hXX : Sₗ.X ∩ Sᵣ.X = {x},
  ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = {y},
  ∃ hXY : Disjoint Sₗ.X Sᵣ.Y,
  ∃ hYX : Disjoint Sₗ.Y Sᵣ.X,
  standardReprSum2 hXX hYY hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

-- [theorem] any 2-sum of regular matroids is a regular matroid
recall Matroid.IsSum2of.isRegular {α : Type*} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.IsSum2of Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular
/--
info: 'Matroid.IsSum2of.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.IsSum2of.isRegular


/-! ## The 3-sum -/

-- how Mathlib handles invertibility
recall isUnit_iff_exists_and_exists {T : Type*} [Monoid T] {a : T} :
  IsUnit a ↔ (∃ b : T, a * b = 1) ∧ (∃ c : T, c * a = 1)

recall Set.drop1 {α : Type*} (Z : Set α) (z₀ : Z) : Set α :=
  Z \ {z₀.val}

recall Set.drop2 {α : Type*} (Z : Set α) (z₀ z₁ : Z) : Set α :=
  Z \ {z₀.val, z₁.val}

recall Set.drop3 {α : Type*} (Z : Set α) (z₀ z₁ z₂ : Z) : Set α :=
  Z \ {z₀.val, z₁.val, z₂.val}

recall undrop3 {α : Type*} {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : Z :=
  ⟨i.val, i.property.left⟩

recall MatrixSum3.Aₗ  {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Fin 2) R
recall MatrixSum3.Dₗ  {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix (Fin 2) Yₗ R
recall MatrixSum3.D₀ₗ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix (Fin 2) (Fin 2) R
recall MatrixSum3.D₀ᵣ {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix (Fin 2) (Fin 2) R
recall MatrixSum3.Dᵣ  {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix Xᵣ (Fin 2) R
recall MatrixSum3.Aᵣ  {Xₗ Yₗ Xᵣ Yᵣ R : Type*} : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R → Matrix (Fin 2 ⊕ Xᵣ) (Unit ⊕ Yᵣ) R
/--
info: MatrixSum3.mk.{u_1, u_2, u_3, u_4, u_5} {Xₗ : Type u_1} {Yₗ : Type u_2} {Xᵣ : Type u_3} {Yᵣ : Type u_4} {R : Type u_5}
  (Aₗ : Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Fin 2) R) (Dₗ : Matrix (Fin 2) Yₗ R) (D₀ₗ D₀ᵣ : Matrix (Fin 2) (Fin 2) R)
  (Dᵣ : Matrix Xᵣ (Fin 2) R) (Aᵣ : Matrix (Fin 2 ⊕ Xᵣ) (Unit ⊕ Yᵣ) R) : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R
-/
#guard_msgs in
#check MatrixSum3.mk

recall blocksToMatrixSum3 {Xₗ Yₗ Xᵣ Yᵣ R : Type*}
    (Bₗ : Matrix ((Xₗ ⊕ Unit) ⊕ Fin 2) ((Yₗ ⊕ Fin 2) ⊕ Unit) R)
    (Bᵣ : Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ)) (Fin 2 ⊕ (Unit ⊕ Yᵣ)) R) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R where
  Aₗ  := Bₗ.toBlocks₁₁
  Dₗ  := Bₗ.toBlocks₂₁.toCols₁
  D₀ₗ := Bₗ.toBlocks₂₁.toCols₂
  D₀ᵣ := Bᵣ.toBlocks₂₁.toRows₁
  Dᵣ  := Bᵣ.toBlocks₂₁.toRows₂
  Aᵣ  := Bᵣ.toBlocks₂₂

recall MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ R : Type*} [CommRing R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix ((Xₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ)) R :=
  Matrix.fromBlocks S.Aₗ 0 (Matrix.fromBlocks S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ) S.Aᵣ

recall Matrix.toBlockSummandₗ {α : Type*} {Xₗ Yₗ : Set α} {R : Type*} (Bₗ : Matrix Xₗ Yₗ R) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
    Matrix ((Xₗ.drop3 x₀ x₁ x₂ ⊕ Unit) ⊕ Fin 2) ((Yₗ.drop3 y₀ y₁ y₂ ⊕ Fin 2) ⊕ Unit) R :=
  Bₗ.submatrix (·.casesOn (·.casesOn undrop3 (fun _ => x₂)) ![x₀, x₁]) (·.casesOn (·.casesOn undrop3 ![y₀, y₁]) (fun _ => y₂))

recall Matrix.toBlockSummandᵣ {α : Type*} {Xᵣ Yᵣ : Set α} {R : Type*} (Bᵣ : Matrix Xᵣ Yᵣ R) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
    Matrix (Unit ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ x₁ x₂)) (Fin 2 ⊕ (Unit ⊕ Yᵣ.drop3 y₀ y₁ y₂)) R :=
  Bᵣ.submatrix (·.casesOn (fun _ => x₂) (·.casesOn ![x₀, x₁] undrop3)) (·.casesOn ![y₀, y₁] (·.casesOn (fun _ => y₂) undrop3))

-- specialized matrix conversion for 3-sum
recall Matrix.toMatrixDropUnionDrop {α : Type*} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type*}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A : Matrix
      ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
      ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
      R) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem R :=
  A.submatrix
    (fun i : (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem =>
      if hi₂ₗ : i.val = x₂ₗ then ◩◪0 else
      if hiXₗ : i.val ∈ Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ then ◩◩⟨i, hiXₗ⟩ else
      if hi₀ᵣ : i.val = x₀ᵣ then ◪◩0 else
      if hi₁ᵣ : i.val = x₁ᵣ then ◪◩1 else
      if hiXᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then ◪◪⟨i, hiXᵣ⟩ else
      False.elim (i.property.elim (by intro; simp_all) (by intro; simp_all)))
    (fun j : (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem =>
      if hj₀ₗ : j.val = y₀ₗ then ◩◪0 else
      if hj₁ₗ : j.val = y₁ₗ then ◩◪1 else
      if hjYₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then ◩◩⟨j, hjYₗ⟩ else
      if hj₂ᵣ : j.val = y₂ᵣ then ◪◩0 else
      if hjYᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then ◪◪⟨j, hjYᵣ⟩ else
      False.elim (j.property.elim (by intro; simp_all) (by intro; simp_all)))

-- how 3-sum of standard representations is defined
recall standardReprSum3 {α : Type*} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂})
    (hXY : Disjoint Sₗ.X Sᵣ.Y) (hYX : Disjoint Sₗ.Y Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  let x₀ₗ : Sₗ.X := ⟨x₀, hXX.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let x₁ₗ : Sₗ.X := ⟨x₁, hXX.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let x₂ₗ : Sₗ.X := ⟨x₂, hXX.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.symm.subset.trans Set.inter_subset_left (by simp)⟩
  let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.symm.subset.trans Set.inter_subset_right (by simp)⟩
  let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.symm.subset.trans Set.inter_subset_right (by simp)⟩
  let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.symm.subset.trans Set.inter_subset_right (by simp)⟩
  let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.symm.subset.trans Set.inter_subset_right (by simp)⟩
  let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.symm.subset.trans Set.inter_subset_right (by simp)⟩
  let y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.symm.subset.trans Set.inter_subset_right (by simp)⟩
  open scoped Classical in if
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    ∧ Sₗ.B.submatrix ![x₀ₗ, x₁ₗ] ![y₀ₗ, y₁ₗ] = Sᵣ.B.submatrix ![x₀ᵣ, x₁ᵣ] ![y₀ᵣ, y₁ᵣ]
    ∧ IsUnit (Sₗ.B.submatrix ![x₀ₗ, x₁ₗ] ![y₀ₗ, y₁ₗ])
    ∧ Sₗ.B x₀ₗ y₂ₗ = 1
    ∧ Sₗ.B x₁ₗ y₂ₗ = 1
    ∧ Sₗ.B x₂ₗ y₀ₗ = 1
    ∧ Sₗ.B x₂ₗ y₁ₗ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ y₂ₗ = 0)
    ∧ Sᵣ.B x₀ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₁ᵣ y₂ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₀ᵣ = 1
    ∧ Sᵣ.B x₂ᵣ y₁ᵣ = 1
    ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B x₂ᵣ ⟨y, hy⟩ = 0)
  then
    some ⟨
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (blocksToMatrixSum3
          (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ)
          (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)
        ).matrix.toMatrixDropUnionDrop,
      inferInstance,
      inferInstance⟩
  else
    none

-- how 3-sum of binary matroids is defined
recall Matroid.IsSum3of {α : Type*} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ x₀ x₁ x₂ y₀ y₁ y₂ : α,
  ∃ hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂},
  ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂},
  ∃ hXY : Disjoint Sₗ.X Sᵣ.Y,
  ∃ hYX : Disjoint Sₗ.Y Sᵣ.X,
  standardReprSum3 hXX hYY hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

-- [theorem] any 3-sum of regular matroids is a regular matroid
recall Matroid.IsSum3of.isRegular {α : Type*} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.IsSum3of Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular
/--
info: 'Matroid.IsSum3of.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.IsSum3of.isRegular
