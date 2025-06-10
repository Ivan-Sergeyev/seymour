import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic
import Linters

/-!
# Basics

This is the stem file (imported by every other file in this project).
This file provides notation used throughout the project, some very basic lemmas, and a little bit of configuration.
-/

/-! ## Notation -/

/-- The finite field on 2 elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2

/-- The finite field on 3 elements; write `Z3` for "value" type but `Fin 3` for "indexing" type. -/
abbrev Z3 : Type := ZMod 3

/-- Roughly speaking `a ᕃ A` is `A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert

/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr

/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)

/-- We denote the cardinality of a `Fintype` the same way the cardinality of a `Finset` is denoted. -/
prefix:max "#" => Fintype.card

/-- Canonical bijection between subtypes corresponding to equal sets. -/
postfix:max ".≃" => Equiv.setCongr

/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl

/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr

/-- Glue rows of two matrices. -/
infixl:63 " ⊟ " => Matrix.fromRows

/-- Glue cols of two matrices. -/
infixl:63 " ◫ " => Matrix.fromCols

/-- Glue four matrices into one block matrix. -/
notation:62 "⊞ " A:max B:max C:max D:max => Matrix.fromBlocks A B C D

/-- Convert vector to a single-row matrix. -/
notation:64 "▬"r:81 => Matrix.replicateRow Unit r

/-- Convert vector to a single-col matrix. -/
notation:64 "▮"c:81 => Matrix.replicateCol Unit c

/-- Outer product of two vectors (the column vector comes on left; the row vector comes on right). -/
infix:67 " ⊗ " => fun {X Y α : Type} [Mul α] =>
  (fun c : X → α => fun r : Y → α => Matrix.of (fun i : X => fun j : Y => c i * r j))

/-- Element-wise product of two matrices (rarely used). -/
infixr:66 " ⊡ " => fun {X Y α β : Type} [SMul α β] =>
  (fun A : Matrix X Y α => fun B : Matrix X Y β => Matrix.of (fun i : X => fun j : Y => A i j • B i j))

/-- The set of possible outputs of a function. -/
abbrev Function.range {α ι : Type} (f : ι → α) : Set α := Set.range f

@[app_unexpander Function.range]
def Function.range_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `($(f).$(Lean.mkIdent `range))
  | _ => throw ()

@[app_unexpander Function.support]
def Function.support_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `($(f).$(Lean.mkIdent `support))
  | _ => throw ()


/-! ## Basic lemmas -/

lemma and_congr_l {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : P₁ ∧ Q ↔ P₂ ∧ Q :=
  and_congr_left ↓hP

lemma and_congr_r {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : Q ∧ P₁ ↔ Q ∧ P₂ :=
  and_congr_right ↓hP

lemma Int.neg_one_ne_zero : -1 ≠ 0 := by
  norm_num

lemma exists_minimal_nat_le_of_exists {n : ℕ} (P : { a : ℕ | a ≤ n } → Prop) (hP : P ⟨n, le_refl n⟩) :
    ∃ n : { a : ℕ | a ≤ n }, Minimal P n := by
  obtain ⟨b, -, hb⟩ := Finite.exists_minimal_le hP
  exact ⟨b, hb⟩

lemma exists_minimal_nat_of_exists {P : ℕ → Prop} (hP : ∃ n : ℕ, P n) : ∃ n : ℕ, Minimal P n := by
  obtain ⟨n, hn⟩ := hP
  obtain ⟨c, hc⟩ := exists_minimal_nat_le_of_exists (P ·.val) hn
  exact ⟨c.val, hc.left, fun m hPm hmc => @hc.right ⟨m, hmc.trans c.property⟩ hPm hmc⟩

variable {α : Type}

lemma dite_of_true {P : Prop} [Decidable P] (p : P) {f : P → α} {a : α} : (if hp : P then f hp else a) = f p := by
  simp [p]

lemma dite_of_false {P : Prop} [Decidable P] (p : ¬P) {f : P → α} {a : α} : (if hp : P then f hp else a) = a := by
  simp [p]

lemma Function.range_eq {ι : Type} (f : ι → α) : f.range = { a : α | ∃ i : ι, f i = a } :=
  rfl

lemma Sum.swap_inj {β : Type} : (@Sum.swap α β).Injective := by
  intro
  aesop

lemma Finset.sum_of_single_nonzero {ι : Type} (s : Finset ι) [AddCommMonoid α] (f : ι → α) (a : ι) (ha : a ∈ s)
    (hf : ∀ i ∈ s, i ≠ a → f i = 0) :
    s.sum f = f a := by
  rw [←Finset.sum_subset (s.singleton_subset_iff.← ha)]
  · simp
  intro x hxs hxa
  apply hf x hxs
  rwa [Finset.not_mem_singleton] at hxa

lemma fintype_sum_of_single_nonzero {ι : Type} [Fintype ι] [AddCommMonoid α] (f : ι → α) (a : ι)
    (hf : ∀ i : ι, i ≠ a → f i = 0) :
    Finset.univ.sum f = f a :=
  Finset.univ.sum_of_single_nonzero f a (Finset.mem_univ a) (by simpa using hf)

lemma sum_elem_of_single_nonzero {ι : Type} [AddCommMonoid α] {f : ι → α} {S : Set ι} [Fintype S] {a : ι} (haS : a ∈ S)
    (hf : ∀ i : ι, i ≠ a → f i = 0) :
    ∑ i : S.Elem, f i = f a := by
  apply fintype_sum_of_single_nonzero (fun s : S.Elem => f s.val) ⟨a, haS⟩
  intro i hi
  apply hf
  intro contr
  apply hi
  ext
  exact contr

lemma sum_insert_elem {ι : Type} [DecidableEq ι] [AddCommMonoid α] {S : Set ι} [Fintype S] {a : ι} (ha : a ∉ S) (f : ι → α) :
    ∑ i : (a ᕃ S).Elem, f i = f a + ∑ i : S.Elem, f i := by
  simp_all [Finset.sum_set_coe]

lemma finset_toSet_sum {ι : Type} [AddCommMonoid α] {s : Finset ι} {S : Set ι} [Fintype S] (hsS : s.toSet = S) (f : ι → α) :
    ∑ i : s.toSet, f i = ∑ i : S, f i := by
  apply Finset.sum_bij (fun a => ↓⟨a.val, hsS ▸ a.coe_prop⟩)
  · simp
  · simp
  · aesop
  · simp

lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  apply fintype_sum_of_single_nonzero
  exact hf


/-! ## Conversion between set-based notions and type-based notions -/

variable {X Y : Set α}

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

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
@[simp]
lemma toSum_toUnion [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
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
lemma toUnion_toSum [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [hXY]


/-! ## Aesop modifiers -/

attribute [aesop apply safe] Classical.choose_spec

/-- Nonterminal `aesop` (dangerous). -/
macro "aesopnt" : tactic => `(tactic| aesop (config := {warnOnNonterminal := false}))
