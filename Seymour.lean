import Seymour.HardDirection

open scoped Matrix Set.Notation


-- ## Summary of basic definitions

recall Z2 := Fin 2

recall VectorMatroid.X {α R : Type} : VectorMatroid α R → Set α
recall VectorMatroid.Y {α R : Type} : VectorMatroid α R → Set α
recall VectorMatroid.A {α R : Type} (M : VectorMatroid α R) : Matrix M.X M.Y R
/--
info: VectorMatroid.mk {α R : Type} (X Y : Set α) (A : Matrix (↑X) (↑Y) R) : VectorMatroid α R
-/
#guard_msgs in
#check VectorMatroid.mk

recall VectorMatroid.toMatroid_indep_iff {α R : Type} [DivisionRing R] (M : VectorMatroid α R) (I : Set α) :
  M.toMatroid.Indep I ↔ I ⊆ M.Y ∧ LinearIndepOn R M.Aᵀ (M.Y ↓∩ I)

example {X X' Y Y' R : Type*} (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) (i : X') (j : Y') :
    (A.submatrix f g) i j = A (f i) (g j) :=
  rfl

recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ Set.range SignType.cast

recall Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

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

recall StandardRepr.toMatroid_indep_iff {α : Type} [DecidableEq α] {R : Type} [DivisionRing R]
    (S : StandardRepr α R) (I : Set α) :
  S.toMatroid.Indep I ↔ I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((Matrix.fromCols 1 S.B).submatrix id Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I)

recall Subtype.toSum {α : Type} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

recall Matrix.toMatrixUnionUnion {α : Type} {T₁ T₂ S₁ S₂ : Set α} {β : Type}
    [∀ a, Decidable (a ∈ T₁)] [∀ a, Decidable (a ∈ T₂)] [∀ a, Decidable (a ∈ S₁)] [∀ a, Decidable (a ∈ S₂)]
    (A : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  A.submatrix Subtype.toSum Subtype.toSum


-- ## Summary of 1-sum

recall matrix1sumComposition {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 0 Aᵣ

recall standardRepr1sumComposition {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Disjoint Sₗ.X Sᵣ.Y) (hYX : Disjoint Sₗ.Y Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      (matrix1sumComposition Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    Disjoint Sₗ.X Sᵣ.X ∧ Disjoint Sₗ.Y Sᵣ.Y
  ⟩

private theorem Matroid_Is1sumOf_isRegular {α : Type} [DecidableEq α] (Sₗ Sᵣ S : StandardRepr α Z2)
    [Finite Sₗ.X] [Finite Sᵣ.X] (hXY : Disjoint Sₗ.X Sᵣ.Y) (hYX : Disjoint Sₗ.Y Sᵣ.X)
    (hS : S = (standardRepr1sumComposition hXY hYX).fst) (hSₗ : Sₗ.toMatroid.IsRegular) (hSᵣ : Sᵣ.toMatroid.IsRegular) :
    S.toMatroid.IsRegular := by
  have : Finite S.X := hS ▸ Finite.Set.finite_union Sₗ.X Sᵣ.X
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hSₗ hSᵣ ⊢
  exact hS ▸ standardRepr1sumComposition_hasTuSigning hXY hYX hSₗ hSᵣ

/--
info: '_private.Seymour.0.Matroid_Is1sumOf_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid_Is1sumOf_isRegular


-- ## Summary of 2-sum

recall matrix2sumComposition {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (x : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (y : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  Matrix.fromBlocks Aₗ 0 (fun i j => y i * x j) Aᵣ

recall standardRepr2sumComposition {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Disjoint Sᵣ.X Sₗ.Y) :
    StandardRepr α Z2 × Prop :=
  let Aₗ : Matrix (Sₗ.X \ {a}).Elem Sₗ.Y.Elem Z2 := Sₗ.B.submatrix Set.diff_subset.elem id -- the top submatrix of `Bₗ`
  let Aᵣ : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {a}).Elem Z2 := Sᵣ.B.submatrix id Set.diff_subset.elem -- the right submatrix of `Bᵣ`
  let x : Sₗ.Y.Elem → Z2 := Sₗ.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `Bₗ`
  let y : Sᵣ.X.Elem → Z2 := (Sᵣ.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `Bᵣ`
  ⟨
    ⟨
      (Sₗ.X \ {a}) ∪ Sᵣ.X,
      Sₗ.Y ∪ (Sᵣ.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_sdiff_singleton ha, Sᵣ.hXY.disjoint_sdiff_right⟩⟩,
      (matrix2sumComposition Aₗ x Aᵣ y).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (Disjoint Sₗ.X Sᵣ.X ∧ Disjoint Sₗ.Y Sᵣ.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

private theorem Matroid_Is2sumOf_isRegular {α : Type} [DecidableEq α] (Sₗ Sᵣ S : StandardRepr α Z2) (a : α)
    [Finite Sₗ.X] [Finite Sᵣ.X] (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Disjoint Sᵣ.X Sₗ.Y)
    (hS : S = (standardRepr2sumComposition ha hXY).fst) (hSₗ : Sₗ.toMatroid.IsRegular) (hSᵣ : Sᵣ.toMatroid.IsRegular) :
    S.toMatroid.IsRegular := by
  have : Finite S.X := hS ▸ Finite.Set.finite_union (Sₗ.X \ {a}) Sᵣ.X
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hSₗ hSᵣ ⊢
  exact hS ▸ standardRepr2sumComposition_hasTuSigning ha hXY hSₗ hSᵣ

/--
info: '_private.Seymour.0.Matroid_Is2sumOf_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid_Is2sumOf_isRegular
