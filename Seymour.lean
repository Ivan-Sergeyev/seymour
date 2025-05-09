import Seymour.HardDirection -- the final file
import Seymour.Matrix.OfLinearMaps -- currently not used


-- ## Summary of basic definitions

recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

recall Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) : Prop :=
  A.IsTotallyUnimodular ∧ ∀ i j, |A i j| = (U i j).val

recall Matrix.HasTuSigning {X Y : Type} (U : Matrix X Y Z2) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U

recall StandardRepr.X {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.Y {α R : Type} [DecidableEq α] : StandardRepr α R → Set α
recall StandardRepr.B {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Matrix S.X S.Y R
recall StandardRepr.hXY {α R : Type} [DecidableEq α] (S : StandardRepr α R) : Disjoint S.X S.Y

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

recall matrix1sumComposition {β : Type} [Zero β] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ β) (Aᵣ : Matrix Xᵣ Yᵣ β) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) β :=
  Matrix.fromBlocks Aₗ 0 0 Aᵣ

recall standardRepr1sumComposition {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
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
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  ⟩

recall standardRepr1sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Sₗ.B.HasTuSigning → Sᵣ.B.HasTuSigning → (standardRepr1sumComposition hXY hYX).fst.B.HasTuSigning

#print axioms standardRepr1sumComposition_hasTuSigning


-- ## Summary of 2-sum

recall matrix2sumComposition {β : Type} [Semiring β] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ β) (x : Yₗ → β) (Aᵣ : Matrix Xᵣ Yᵣ β) (y : Xᵣ → β) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) β :=
  Matrix.fromBlocks Aₗ 0 (fun i j => y i * x j) Aᵣ

recall standardRepr2sumComposition {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) :
    StandardRepr α Z2 × Prop :=
  let Aₗ : Matrix (Sₗ.X \ {a}).Elem Sₗ.Y.Elem Z2 := Sₗ.B ∘ Set.diff_subset.elem -- the top submatrix of `Bₗ`
  let Aᵣ : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {a}).Elem Z2 := (Sᵣ.B · ∘ Set.diff_subset.elem) -- the right submatrix of `Bᵣ`
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
    (Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

recall standardRepr2sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {a : α}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) :
    Sₗ.B.HasTuSigning → Sᵣ.B.HasTuSigning → (standardRepr2sumComposition ha hXY).fst.B.HasTuSigning

#print axioms standardRepr2sumComposition_hasTuSigning
