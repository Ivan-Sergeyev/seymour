import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular


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

/-- We denote the cardinality of a `Fintype` the same way the cardinality of a `Finset` is denoted. -/
prefix:max "#" => Fintype.card

/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl

/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr


lemma Fin2_eq_1_of_ne_0 {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  omega

lemma Fin2_eq_0_of_ne_1 {a : Fin 2} (ha : a ≠ 1) : a = 0 := by
  omega

lemma Fin3_eq_2_of_ne_0_1 {a : Fin 3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 := by
  omega

lemma Z2val_toRat_mul_Z2val_toRat (a b : Z2) : (a.val : ℚ) * (b.val : ℚ) = ((a*b).val : ℚ) := by
  fin_cases a <;> fin_cases b <;> simp
  apply one_mul

variable {α : Type}

@[simp]
abbrev Function.range {ι : Type} (f : ι → α) : Set α := Set.range f

@[simp low]
abbrev Matrix.prependId [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) : Matrix m (m ⊕ n) α :=
  Matrix.fromCols 1 A

@[simp low]
abbrev Matrix.uppendId [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) : Matrix (n ⊕ m) n α :=
  Matrix.fromRows 1 A

@[simp]
lemma Matrix.prependId_transpose [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) :
    A.prependId.transpose = A.transpose.uppendId := by
  ext i j
  cases i with
  | inr => rfl
  | inl i' =>
    if hi' : i' = j then
      simp [Matrix.one_apply_eq, hi']
    else
      simp [Matrix.one_apply_ne, hi', Ne.symm hi']

@[simp]
lemma Matrix.uppendId_transpose [Zero α] [One α] {m n : Type} [DecidableEq m] [DecidableEq n] (A : Matrix m n α) :
    A.uppendId.transpose = A.transpose.prependId := by
  rw [←Matrix.transpose_transpose A.transpose.prependId, Matrix.prependId_transpose, Matrix.transpose_transpose]

lemma Matrix.ext_col {m n : Type} {A B : Matrix m n α} (hAB : ∀ i : m, A i = B i) : A = B :=
  Matrix.ext (congr_fun <| hAB ·)

lemma Matrix.det_coe [DecidableEq α] [Fintype α] (A : Matrix α α ℤ) (F : Type) [Field F] :
    ((A.det : ℤ) : F) = ((A.map Int.cast).det : F) := by
  simp [Matrix.det_apply]
  congr
  ext p
  if h1 : Equiv.Perm.sign p = 1 then
    simp [h1]
  else
    simp [Int.units_ne_iff_eq_neg.→ h1]

lemma IsUnit.linearIndependent_matrix [DecidableEq α] [Fintype α] {R : Type} [CommRing R] {A : Matrix α α R} (hA : IsUnit A) :
    LinearIndependent R A :=
  A.linearIndependent_rows_of_isUnit hA

lemma Sum.swap_inj {β : Type} : (@Sum.swap α β).Injective := by
  intro
  aesop

lemma finset_of_cardinality_between {β : Type} [Fintype α] [Fintype β] {n : ℕ}
    (hα : #α < n) (hn : n ≤ #α + #β) :
    ∃ b : Finset β, #(α ⊕ b) = n ∧ Nonempty b := by
  have beta : n - #α ≤ #β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - #α :=
    (Finset.exists_subset_card_eq beta).imp (by simp)
  use s
  rw [Fintype.card_sum, Fintype.card_coe, hs]
  constructor
  · omega
  · by_contra ifempty
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at ifempty
      exact Finset.eq_empty_of_forall_not_mem ifempty
    omega

lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  rw [←Finset.sum_subset (Finset.subset_univ {0})]
  · simp
  intro x _ hx
  apply hf
  simpa using hx

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
@[simp low]
def HasSubset.Subset.elem {X Y : Set α} (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

lemma HasSubset.Subset.elem_injective {X Y : Set α} (hXY : X ⊆ Y) : hXY.elem.Injective := by
  intro x y hxy
  ext
  simpa using hxy

lemma HasSubset.Subset.elem_range {X Y : Set α} (hXY : X ⊆ Y) : hXY.elem.range = { a : Y.Elem | a.val ∈ X } := by
  aesop

/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then ◩⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then ◪⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion {X Y : Set α} (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
lemma toSum_toUnion {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp [Subtype.toSum, Sum.toUnion, *]
  else if hiY : i.val ∈ Y then
    simp [Subtype.toSum, Sum.toUnion, *]
  else
    exfalso
    exact i.property.elim hiX hiY

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
`X` and `Y` are disjoint. -/
lemma toUnion_toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [Subtype.toSum, Sum.toUnion, hXY]

variable {T₁ T₂ S₁ S₂ : Set α} {β : Type}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (C : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((C ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- Convert a matrix over set unions to a block matrix. -/
def Matrix.toMatrixSumSum (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β :=
  ((C ∘ Sum.toUnion) · ∘ Sum.toUnion)

/-- Converting a block matrix to a matrix over set unions and back to a block matrix gives the original matrix, assuming that
both said unions are disjoint. -/
lemma toMatrixUnionUnion_toMatrixSumSum (hT : T₁ ⫗ T₂) (hS : S₁ ⫗ S₂) (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    C.toMatrixUnionUnion.toMatrixSumSum = C := by
  ext
  simp [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toUnion_toSum, *]

/-- Converting a matrix over set unions to a block matrix and back to a matrix over set unions gives the original matrix. -/
lemma toMatrixSumSum_toMatrixUnionUnion (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    C.toMatrixSumSum.toMatrixUnionUnion = C := by
  ext
  simp [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toSum_toUnion]

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.IsTotallyUnimodular.toMatrixUnionUnion [CommRing β] {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β}
    (hC : C.IsTotallyUnimodular) :
    C.toMatrixUnionUnion.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hC ⊢
  intros
  apply hC
