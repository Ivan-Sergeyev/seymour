import Seymour.Basic.Basic

/-!
# Conversion between set-based notions and type-based notions

These conversions are frequently used throughout the project.
-/

variable {α : Type} {X Y : Set α}

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
@[simp low]
def HasSubset.Subset.elem (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

lemma HasSubset.Subset.elem_injective (hXY : X ⊆ Y) : hXY.elem.Injective := by
  intro x y hxy
  ext
  simpa using hxy

lemma HasSubset.Subset.elem_range (hXY : X ⊆ Y) : hXY.elem.range = { a : Y.Elem | a.val ∈ X } := by
  aesop

/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then ◩⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then ◪⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

@[app_unexpander Subtype.toSum]
def Subtype.toSum_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $i) => `($(i).$(Lean.mkIdent `toSum))
  | _ => throw ()

@[simp]
lemma toSum_left [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {i : (X ∪ Y).Elem} (hi : i.val ∈ X) :
    i.toSum = ◩⟨i.val, hi⟩ := by
  simp [Subtype.toSum, hi]

@[simp]
lemma toSum_right [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {i : (X ∪ Y).Elem}
    (hiX : i.val ∉ X) (hiY : i.val ∈ Y) :
    i.toSum = ◪⟨i.val, hiY⟩ := by
  simp [Subtype.toSum, hiY, hiX]

/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem

@[simp]
lemma toUnion_left (x : X.Elem) : @Sum.toUnion α X Y ◩x = ⟨x.val, Set.subset_union_left x.property⟩ :=
  rfl

@[simp]
lemma toUnion_right (y : Y.Elem) : @Sum.toUnion α X Y ◪y = ⟨y.val, Set.subset_union_right y.property⟩ :=
  rfl

variable [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
@[simp]
lemma toSum_toUnion (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp [hiX]
  else if hiY : i.val ∈ Y then
    simp [hiX, hiY]
  else
    exfalso
    exact i.property.elim hiX hiY

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
    `X` and `Y` are disjoint. -/
@[simp]
lemma toUnion_toSum (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [hXY]

/-- Equivalence between `X.Elem ⊕ Y.Elem` and `(X ∪ Y).Elem` (i.e., a bundled bijection). -/
def Disjoint.equivSumUnion (hXY : X ⫗ Y) : X.Elem ⊕ Y.Elem ≃ (X ∪ Y).Elem :=
  ⟨Sum.toUnion, Subtype.toSum, toUnion_toSum hXY, toSum_toUnion⟩
