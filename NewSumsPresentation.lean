import Seymour.HardDirection

open scoped Matrix Set.Notation

/-! # Summary of all results -/

/-! ## Basic definitions -/

recall Z2 := Fin 2

recall Matrix.toMatroid_indep_iff {α R : Type} {X Y : Set α} [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
  A.toMatroid.Indep I ↔ I ⊆ Y ∧ LinearIndepOn R Aᵀ (Y ↓∩ I)

example {X X' Y Y' R : Type*} (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) (i : X') (j : Y') :
    (A.submatrix f g) i j = A (f i) (g j) :=
  rfl

recall Matrix.IsTotallyUnimodular {X Y R : Type*} [CommRing R] (A : Matrix X Y R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ Set.range SignType.cast

recall Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ A.toMatroid = M

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


/-! ## 1-sum -/

/-recall-/ noncomputable def standardReprSum1 {α : Type} [DecidableEq α] (Sₗ Sᵣ : StandardRepr α Z2) :
    Option (StandardRepr α Z2) :=
  have : Decidable (Disjoint (Sₗ.X ∪ Sᵣ.X) (Sₗ.Y ∪ Sᵣ.Y)) := by
    apply Classical.propDecidable -- todo: this is cheeks
  if IsCorrect : Disjoint (Sₗ.X ∪ Sᵣ.X) (Sₗ.Y ∪ Sᵣ.Y) then
    some ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      IsCorrect,
      (Matrix.fromBlocks Sₗ.B 0 0 Sᵣ.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩
  else
    none

private theorem Matroid_isSum1of_isRegular {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2}
    [Finite Sₗ.X] [Finite Sᵣ.X] -- todo: try to get rid of this
    (hS : (standardReprSum1 Sₗ Sᵣ) = some S) (hSₗ : Sₗ.toMatroid.IsRegular) (hSᵣ : Sᵣ.toMatroid.IsRegular) :
    S.toMatroid.IsRegular := by
  sorry -- todo: adapt old proof
  -- have : Finite S.X := hS ▸ Finite.Set.finite_union Sₗ.X Sᵣ.X
  -- rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hSₗ hSᵣ ⊢
  -- exact hS ▸ standardRepr1sumComposition_hasTuSigning hXY hYX hSₗ hSᵣ

/--
info: '_private.Seymour.0.Matroid_Is1sumOf_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid_isSum1of_isRegular


/-! ## 2-sum -/

/-recall-/ noncomputable def standardReprSum2 {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
    (hx : Sₗ.X ∩ Sᵣ.X = {x}) (hy : Sₗ.Y ∩ Sᵣ.Y = {y}) :
    Option (StandardRepr α Z2) :=
  let Aₗ : Matrix (Sₗ.X \ {x}).Elem Sₗ.Y.Elem Z2 := Sₗ.B.submatrix Set.diff_subset.elem id -- the top submatrix of `Bₗ`
  let Aᵣ : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {y}).Elem Z2 := Sᵣ.B.submatrix id Set.diff_subset.elem -- the right submatrix of `Bᵣ`
  let r : Sₗ.Y.Elem → Z2 := Sₗ.B ⟨x, Set.mem_of_mem_inter_left (by rw [hx]; rfl)⟩ -- the bottom row of `Bₗ`
  let c : Sᵣ.X.Elem → Z2 := (Sᵣ.B · ⟨y, Set.mem_of_mem_inter_right (by rw [hy]; rfl)⟩) -- the left column of `Bᵣ`
  have : Decidable ((Disjoint ((Sₗ.X \ {x}) ∪ Sᵣ.X) (Sₗ.Y ∪ (Sᵣ.Y \ {y}))) ∧ (r ≠ 0 ∧ c ≠ 0)) := by
    apply Classical.propDecidable -- todo: this is cheeks
  if IsCorrect : (Disjoint ((Sₗ.X \ {x}) ∪ Sᵣ.X) (Sₗ.Y ∪ (Sᵣ.Y \ {y}))) ∧ (r ≠ 0 ∧ c ≠ 0) then
    some ⟨
      (Sₗ.X \ {x}) ∪ Sᵣ.X,
      Sₗ.Y ∪ (Sᵣ.Y \ {y}),
      IsCorrect.left,
      (Matrix.fromBlocks Aₗ 0 (fun i j => c i * r j) Aᵣ).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩
  else
    none

private theorem Matroid_isSum2of_isRegular {α : Type} [DecidableEq α] {S Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
    [Finite Sₗ.X] [Finite Sᵣ.X] -- todo: try to get rid of these
    (hx : Sₗ.X ∩ Sᵣ.X = {x}) (hy : Sₗ.Y ∩ Sᵣ.Y = {y})
    (hS : standardReprSum2 hx hy = some S) (hSₗ : Sₗ.toMatroid.IsRegular) (hSᵣ : Sᵣ.toMatroid.IsRegular) :
    S.toMatroid.IsRegular := by
  sorry -- todo: reduce to results proved in working version

  -- old proof:
  -- have : Finite S.X := hS ▸ Finite.Set.finite_union (Sₗ.X \ {a}) Sᵣ.X
  -- rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hSₗ hSᵣ ⊢
  -- exact hS ▸ standardRepr2sumComposition_hasTuSigning ha hXY hSₗ hSᵣ

/--
info: '_private.Seymour.0.Matroid_Is2sumOf_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid_isSum2of_isRegular


/-! ## 3-sum -/

/-recall-/ noncomputable def standardReprSum3 {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂})
    :
    Option (StandardRepr α Z2) :=
  -- row membership
  let x₀ₗ : Sₗ.X := ⟨x₀, sorry⟩
  let x₁ₗ : Sₗ.X := ⟨x₁, sorry⟩
  let x₂ₗ : Sₗ.X := ⟨x₂, sorry⟩
  let x₀ᵣ : Sᵣ.X := ⟨x₀, sorry⟩
  let x₁ᵣ : Sᵣ.X := ⟨x₁, sorry⟩
  let x₂ᵣ : Sᵣ.X := ⟨x₂, sorry⟩
  -- col membership
  let y₀ₗ : Sₗ.Y := ⟨y₀, sorry⟩
  let y₁ₗ : Sₗ.Y := ⟨y₁, sorry⟩
  let y₂ₗ : Sₗ.Y := ⟨y₂, sorry⟩
  let y₀ᵣ : Sᵣ.Y := ⟨y₀, sorry⟩
  let y₁ᵣ : Sᵣ.Y := ⟨y₁, sorry⟩
  let y₂ᵣ : Sᵣ.Y := ⟨y₂, sorry⟩
  -- re-indexed blocks of summands
  let Aₗ  : Matrix ((Sₗ.X \ {x₀ₗ.val, x₁ₗ.val, x₂ₗ.val}).Elem ⊕ Fin 1) ((Sₗ.Y \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem ⊕ Fin 2) Z2 :=
    sorry -- todo: take appropriate submatrix
  let Dₗ  : Matrix (Fin 2) (Sₗ.Y \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem Z2 :=
    sorry -- todo: take appropriate submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) Z2 :=
    sorry -- todo: take appropriate submatrix
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) Z2 :=
    sorry -- todo: take appropriate submatrix
  let Dᵣ  : Matrix (Sᵣ.X \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem (Fin 2) Z2 :=
    sorry -- todo: take appropriate submatrix
  let Aᵣ  : Matrix (Fin 2 ⊕ (Sᵣ.X \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem) (Fin 1 ⊕ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val, y₂ᵣ.val}).Elem) Z2 :=
    sorry -- todo: take appropriate submatrix
  -- most bottom-left block
  let D : Matrix (Fin 2 ⊕ (Sᵣ.X \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem) ((Sₗ.Y \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem ⊕ Fin 2) Z2 :=
    Matrix.fromBlocks Dₗ D₀ₗ (Dᵣ * D₀ₗ⁻¹ * Dₗ) Dᵣ
  -- 3-sum on matrix level (before reindexing)
  let Res : Matrix
      (((Sₗ.X \ {x₀ₗ.val, x₁ₗ.val, x₂ₗ.val}).Elem ⊕ Fin 1) ⊕ (Fin 2 ⊕ (Sᵣ.X \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem))
      (((Sₗ.Y \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem ⊕ Fin 2) ⊕ (Fin 1 ⊕ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val, y₂ᵣ.val}).Elem)) Z2 :=
    Matrix.fromBlocks Aₗ 0 D Aᵣ
  -- final matrix 3-sum after reindexing
  let Res' : Matrix
      ((Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val})).Elem
      ((Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val})).Elem Z2 :=
    sorry -- todo: take unions of everything
  have : Decidable (
    -- resulting matrix dimensions are disjoint
      (Disjoint ((Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val})) ((Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val})))
      -- `D₀` is the same
      ∧ !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ]
      -- `D₀` is invertible
      ∧ IsUnit !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ]
      -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
      ∧ Sₗ.B x₀ₗ y₂ₗ = 1
      ∧ Sₗ.B x₁ₗ y₂ₗ = 1
      ∧ Sₗ.B x₂ₗ y₀ₗ = 1
      ∧ Sₗ.B x₂ₗ y₁ₗ = 1
      ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ y₂ₗ = 0)
      -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
      ∧ Sᵣ.B x₀ᵣ y₂ᵣ = 1
      ∧ Sᵣ.B x₁ᵣ y₂ᵣ = 1
      ∧ Sᵣ.B x₂ᵣ y₀ᵣ = 1
      ∧ Sᵣ.B x₂ᵣ y₁ᵣ = 1
      ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B x₂ᵣ ⟨y, hy⟩ = 0)
  ) := by apply Classical.propDecidable -- todo: this is cheeks
  if IsCorrect :
      -- resulting matrix dimensions are disjoint
      (Disjoint ((Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val})) ((Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val})))
      -- `D₀` is the same
      ∧ !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ]
      -- `D₀` is invertible
      ∧ IsUnit !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ]
      -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
      ∧ Sₗ.B x₀ₗ y₂ₗ = 1
      ∧ Sₗ.B x₁ₗ y₂ₗ = 1
      ∧ Sₗ.B x₂ₗ y₀ₗ = 1
      ∧ Sₗ.B x₂ₗ y₁ₗ = 1
      ∧ (∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ y₂ₗ = 0)
      -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
      ∧ Sᵣ.B x₀ᵣ y₂ᵣ = 1
      ∧ Sᵣ.B x₁ᵣ y₂ᵣ = 1
      ∧ Sᵣ.B x₂ᵣ y₀ᵣ = 1
      ∧ Sᵣ.B x₂ᵣ y₁ᵣ = 1
      ∧ (∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B x₂ᵣ ⟨y, hy⟩ = 0)
  then
    some ⟨
      (Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val}),
      (Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val}),
      IsCorrect.left,
      Res',
      inferInstance,
      inferInstance,
    ⟩
  else
    none

private theorem Matroid_isSum3of_isRegular {α : Type} [DecidableEq α] {S Sₗ Sᵣ : StandardRepr α Z2}
    {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [Finite Sₗ.X] [Finite Sᵣ.X] -- todo: try to get rid of these
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂})
    (hS : standardReprSum3 hXX hYY = some S) (hSₗ : Sₗ.toMatroid.IsRegular) (hSᵣ : Sᵣ.toMatroid.IsRegular) :
    S.toMatroid.IsRegular := by
  sorry -- todo: reduce to results proved in working version

/--
info: '_private.Seymour.0.Matroid_Is2sumOf_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid_isSum3of_isRegular
