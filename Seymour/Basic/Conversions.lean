import Seymour.Basic.Basic

/-!
# Conversion between set-based notions and type-based notions

These conversions are frequently used throughout the project.
-/

variable {α : Type*} {X Y : Set α}

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
@[simp low]
def HasSubset.Subset.elem (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

lemma HasSubset.Subset.elem_injective (hXY : X ⊆ Y) : hXY.elem.Injective := by
  intro x y hxy
  ext
  simpa using hxy

/-- Given `X ⊆ Y` provide an embedding (i.e., bundled injective function) from `X` into `Y`. -/
abbrev HasSubset.Subset.embed (hXY : X ⊆ Y) : X.Elem ↪ Y.Elem :=
  ⟨hXY.elem, hXY.elem_injective⟩

lemma HasSubset.Subset.elem_range (hXY : X ⊆ Y) : hXY.elem.range = { a : Y.Elem | a.val ∈ X } := by
  aesop

lemma HasSubset.Subset.embed_range (hXY : X ⊆ Y) : hXY.embed.toFun.range = { a : Y.Elem | a.val ∈ X } :=
  hXY.elem_range

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
lemma toSum_left [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {x : (X ∪ Y).Elem}
    (hx : x.val ∈ X) :
    x.toSum = ◩⟨x.val, hx⟩ := by
  simp [Subtype.toSum, hx]

@[simp]
lemma toSum_right [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] {y : (X ∪ Y).Elem}
    (hyX : y.val ∉ X) (hyY : y.val ∈ Y) :
    y.toSum = ◪⟨y.val, hyY⟩ := by
  simp [Subtype.toSum, hyY, hyX]

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

@[simp]
lemma equivSumUnion_apply_left (hXY : X ⫗ Y) (x : X.Elem) :
    hXY.equivSumUnion ◩x = ⟨x.val, Set.subset_union_left x.property⟩ :=
  rfl

@[simp]
lemma equivSumUnion_apply_right (hXY : X ⫗ Y) (y : Y.Elem) :
    hXY.equivSumUnion ◪y = ⟨y.val, Set.subset_union_right y.property⟩ :=
  rfl

@[simp]
lemma equivSumUnion_symm_apply_left (hXY : X ⫗ Y) {x : (X ∪ Y).Elem} (hx : x.val ∈ X) :
    hXY.equivSumUnion.symm x = ◩⟨x.val, hx⟩ :=
  toSum_left hx

@[simp]
lemma equivSumUnion_symm_apply_right (hXY : X ⫗ Y) {y : (X ∪ Y).Elem} (hy : y.val ∈ Y) :
    hXY.equivSumUnion.symm y = ◪⟨y.val, hy⟩ :=
  toSum_right (hXY.symm.not_mem_of_mem_left hy) hy
