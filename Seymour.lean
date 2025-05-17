import Seymour.HardDirection

open scoped Matrix Set.Notation


-- ## Summary of basic definitions

recall Z2 := Fin 2

recall VectorMatroid.X {α R : Type} : VectorMatroid α R → Set α
recall VectorMatroid.Y {α R : Type} : VectorMatroid α R → Set α
recall VectorMatroid.A {α R : Type} (M : VectorMatroid α R) : Matrix M.X M.Y R

recall VectorMatroid.toMatroid_indep_iff {α R : Type} [DivisionRing R] (M : VectorMatroid α R) (I : Set α) :
  M.toMatroid.Indep I ↔ I ⊆ M.Y ∧ LinearIndepOn R M.Aᵀ (M.Y ↓∩ I)

recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

recall Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

recall StandardRepr.X {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.Y {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.B {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Matrix S.X S.Y R
recall StandardRepr.hXY {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Disjoint S.X S.Y

recall StandardRepr.toMatroid_indep_iff {α : Type} [DecidableEq α] {R : Type} [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
  S.toMatroid.Indep I ↔ I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((Matrix.fromCols 1 S.B).submatrix id Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I)

recall Subtype.toSum {α : Type} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]
    (i : (X ∪ Y).Elem) :
    X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then ◩⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then ◪⟨i, hiY⟩ else
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

recall Matroid.Is1sumOf.S  {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is1sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is1sumOf.Sₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is1sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is1sumOf.Sᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is1sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is1sumOf.hSₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : Finite hM.Sₗ.X
recall Matroid.Is1sumOf.hSᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : Finite hM.Sᵣ.X
recall Matroid.Is1sumOf.hM  {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : hM.S.toMatroid = M
recall Matroid.Is1sumOf.hMₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : hM.Sₗ.toMatroid = Mₗ
recall Matroid.Is1sumOf.hMᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : hM.Sᵣ.toMatroid = Mᵣ
recall Matroid.Is1sumOf.hXY {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : Disjoint hM.Sₗ.X hM.Sᵣ.Y
recall Matroid.Is1sumOf.hYX {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : Disjoint hM.Sₗ.Y hM.Sᵣ.X
recall Matroid.Is1sumOf.IsSum {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : (standardRepr1sumComposition hM.hXY hM.hYX).fst = hM.S
recall Matroid.Is1sumOf.IsValid {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is1sumOf Mₗ Mᵣ) : (standardRepr1sumComposition hM.hXY hM.hYX).snd

recall Matroid.Is1sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.Is1sumOf Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular

/--
info: 'Matroid.Is1sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is1sumOf.isRegular


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

recall Matroid.Is2sumOf.S  {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is2sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is2sumOf.Sₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is2sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is2sumOf.Sᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is2sumOf Mₗ Mᵣ → StandardRepr α Z2
recall Matroid.Is2sumOf.a  {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : M.Is2sumOf Mₗ Mᵣ → α
recall Matroid.Is2sumOf.hSₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : Finite hM.Sₗ.X
recall Matroid.Is2sumOf.hSᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : Finite hM.Sᵣ.X
recall Matroid.Is2sumOf.hM  {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : hM.S.toMatroid = M
recall Matroid.Is2sumOf.hMₗ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : hM.Sₗ.toMatroid = Mₗ
recall Matroid.Is2sumOf.hMᵣ {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : hM.Sᵣ.toMatroid = Mᵣ
recall Matroid.Is2sumOf.ha {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : hM.Sₗ.X ∩ hM.Sᵣ.Y = {hM.a}
recall Matroid.Is2sumOf.hXY {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : Disjoint hM.Sᵣ.X hM.Sₗ.Y
recall Matroid.Is2sumOf.IsSum {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : (standardRepr2sumComposition hM.ha hM.hXY).fst = hM.S
recall Matroid.Is2sumOf.IsValid {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hM : M.Is2sumOf Mₗ Mᵣ) : (standardRepr2sumComposition hM.ha hM.hXY).snd

recall Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} :
  M.Is2sumOf Mₗ Mᵣ → Mₗ.IsRegular → Mᵣ.IsRegular → M.IsRegular

/--
info: 'Matroid.Is2sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is2sumOf.isRegular
