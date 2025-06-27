import Seymour.HardDirection


/-! ## Formally verified summary of the Seymour project -/

open scoped Matrix Set.Notation


/-! ## Preliminaries -/
-- TODO reorder

-- what is vector matroid
recall Matrix.toMatroid_indep_iff {α R : Type} {X Y : Set α} [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
  A.toMatroid.Indep I ↔ I ⊆ Y ∧ LinearIndepOn R Aᵀ (Y ↓∩ I)

-- what `Matrix.submatrix` means
example {X X' Y Y' R : Type*} (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) (i : X') (j : Y') :
  (A.submatrix f g) i j = A (f i) (g j) := rfl

-- how total unimodularity is defined
recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ Set.range SignType.cast

-- how regular matroid is defined
recall Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ A.toMatroid = M

-- what `Disjoint` means
recall Set.disjoint_iff_inter_eq_empty {α : Type _} (X Y : Set α) :
  Disjoint X Y ↔ X ∩ Y = ∅

-- how standard representation is defined
recall StandardRepr.X {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.Y {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.B {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Matrix S.X S.Y R
recall StandardRepr.hXY {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Disjoint S.X S.Y
recall StandardRepr.decmemX {α R : Type} [DecidableEq α] (S : StandardRepr α R) : ∀ a, Decidable (a ∈ S.X)
recall StandardRepr.decmemY {α R : Type} [DecidableEq α] (S : StandardRepr α R) : ∀ a, Decidable (a ∈ S.Y)
/--
info: StandardRepr.mk {α R : Type} [DecidableEq α] (X Y : Set α) (hXY : X ⫗ Y) (B : Matrix (↑X) (↑Y) R)
  (decmemX : (a : α) → Decidable (a ∈ X)) (decmemY : (a : α) → Decidable (a ∈ Y)) : StandardRepr α R
-/
#guard_msgs in
#check StandardRepr.mk

-- what is the matroid constructed from given standard representation
recall StandardRepr.toMatroid_indep_iff {α : Type} [DecidableEq α] {R : Type} [DivisionRing R]
    (S : StandardRepr α R) (I : Set α) :
  S.toMatroid.Indep I ↔ I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((Matrix.fromCols 1 S.B).submatrix id Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I)

-- how an element of set union is converted to disjoint union
recall Subtype.toSum {α : Type} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

-- how matrix indexed by disjoint unions is converted to a matrix indexed by set unions
recall Matrix.toMatrixUnionUnion {α : Type} {T₁ T₂ S₁ S₂ : Set α} {β : Type}
    [∀ a, Decidable (a ∈ T₁)] [∀ a, Decidable (a ∈ T₂)] [∀ a, Decidable (a ∈ S₁)] [∀ a, Decidable (a ∈ S₂)]
    (A : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  A.submatrix Subtype.toSum Subtype.toSum

-- syntactic sugar for the field on 2 elements
recall Z2 := Fin 2


/-! ## The 1-sum -/

-- how 1-sum of matrices is defined
recall matrixSum1 {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 0 Aᵣ

-- how 1-sum of standard representations is defined
recall standardReprSum1 {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  open scoped Classical in if
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
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
recall Matroid.Is1sumOf {α : Type} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ hXY : Sₗ.X ⫗ Sᵣ.Y,
  ∃ hYX : Sₗ.Y ⫗ Sᵣ.X,
  standardReprSum1 hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

-- [theorem] any 1-sum of regular matroids is a regular matroid
recall Matroid.Is1sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.Is1sumOf Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular
/--
info: 'Matroid.Is1sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is1sumOf.isRegular


/-! ## The 2-sum -/

-- how 2-sum of matrices is defined
recall matrixSum2 {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (x : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (y : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 (fun i j => y i * x j) Aᵣ

-- how 2-sum of standard representations is defined
recall standardReprSum2 {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
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
recall Matroid.Is2sumOf {α : Type} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ x y : α,
  ∃ hXX : Sₗ.X ∩ Sᵣ.X = {x},
  ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = {y},
  ∃ hXY : Sₗ.X ⫗ Sᵣ.Y,
  ∃ hYX : Sₗ.Y ⫗ Sᵣ.X,
  standardReprSum2 hXX hYY hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ

-- [theorem] any 2-sum of regular matroids is a regular matroid
recall Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.Is2sumOf Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular
/--
info: 'Matroid.Is2sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is2sumOf.isRegular
