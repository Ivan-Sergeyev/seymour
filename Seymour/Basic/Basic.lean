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

/-- The trivial bijection (identity). -/
notation "=.≃" => Equiv.refl _

/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl

/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr

/-- Glue rows of two matrices. -/
infixl:63 " ⊟ " => Matrix.fromRows

/-- Glue cols of two matrices. -/
infixl:63 " ◫ " => Matrix.fromCols

/-- Glue four matrices into one block matrix. -/
notation "⊞ " => Matrix.fromBlocks

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


/-! ## Basic stuff -/

variable {α : Type}

lemma Function.range_eq {ι : Type} (f : ι → α) : f.range = { a : α | ∃ i : ι, f i = a } :=
  rfl

lemma dite_of_true {P : Prop} [Decidable P] (p : P) {f : P → α} {a : α} : (if hp : P then f hp else a) = f p := by
  simp [p]

lemma dite_of_false {P : Prop} [Decidable P] (p : ¬P) {f : P → α} {a : α} : (if hp : P then f hp else a) = a := by
  simp [p]

abbrev Equiv.leftCongr {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) : ι₁ ⊕ α ≃ ι₂ ⊕ α :=
  Equiv.sumCongr e (Equiv.refl α)

abbrev Equiv.rightCongr {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) : α ⊕ ι₁ ≃ α ⊕ ι₂ :=
  Equiv.sumCongr (Equiv.refl α) e

@[simp]
lemma Equiv.image_symm_apply {β : Type} {X : Set α} (e : α ≃ β) (x : X) : (e.image X).symm ⟨e x.val, by simp⟩ = x :=
  (e.image X).symm_apply_eq.← rfl

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

lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  apply fintype_sum_of_single_nonzero
  exact hf


/-! ## Aesop modifiers -/

attribute [aesop apply safe] Classical.choose_spec

/-- Nonterminal `aesop` (dangerous). -/
macro "aesopnt" : tactic => `(tactic| aesop (config := {warnOnNonterminal := false}))
