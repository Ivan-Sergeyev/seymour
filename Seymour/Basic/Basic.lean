import Mathlib.Tactic


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
prefix:1000 "#" => Fintype.card

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

lemma Fin3_eq_1_of_ne_0_2 {a : Fin 3} (ha0 : a ≠ 0) (ha2 : a ≠ 2) : a = 1 := by
  omega

lemma Fin3_eq_0_of_ne_1_2 {a : Fin 3} (ha1 : a ≠ 1) (ha2 : a ≠ 2) : a = 0 := by
  omega

lemma Z2val_toRat_mul_Z2val_toRat (a b : Z2) : (a.val : ℚ) * (b.val : ℚ) = ((a*b).val : ℚ) := by
  fin_cases a <;> fin_cases b <;> simp
  apply one_mul

lemma and_congr_l {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : P₁ ∧ Q ↔ P₂ ∧ Q :=
  and_congr_left (fun _ => hP)

lemma and_congr_r {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : Q ∧ P₁ ↔ Q ∧ P₂ :=
  and_congr_right (fun _ => hP)

lemma Int.neg_one_ne_zero : -1 ≠ 0 := by
  norm_num

-- The following lemma could be private:
lemma exists_minimal_nat_le_of_exists {n : ℕ} (P : { a : ℕ | a ≤ n } → Prop) (hP : P ⟨n, le_refl n⟩) :
    ∃ n : { a : ℕ | a ≤ n }, Minimal P n := by
  obtain ⟨b, -, hb⟩ := Finite.exists_minimal_le hP
  exact ⟨b, hb⟩

lemma exists_minimal_nat_of_exists {P : ℕ → Prop} (hP : ∃ n : ℕ, P n) : ∃ n : ℕ, Minimal P n := by
  obtain ⟨n, hn⟩ := hP
  obtain ⟨c, hc⟩ := exists_minimal_nat_le_of_exists (P ·.val) hn
  exact ⟨c.val, hc.left, fun m hPm hmc => @hc.right ⟨m, hmc.trans c.property⟩ hPm hmc⟩

variable {α : Type}

@[simp]
abbrev Function.range {ι : Type} (f : ι → α) : Set α := Set.range f

@[app_unexpander Function.range]
def Function.range_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `range))
  | _ => throw ()

lemma Sum.swap_inj {β : Type} : (@Sum.swap α β).Injective := by
  intro
  aesop

lemma finset_of_cardinality_between {β : Type} [Fintype α] [Fintype β] {n : ℕ}
    (hα : #α < n) (hn : n ≤ #α + #β) :
    ∃ b : Finset β, #(α ⊕ b) = n ∧ Nonempty b := by
  have beta : n - #α ≤ #β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - #α := (Finset.exists_subset_card_eq beta).imp (by simp)
  use s
  constructor
  · rw [Fintype.card_sum, Fintype.card_coe, hs]
    omega
  · by_contra hs'
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at hs'
      exact Finset.eq_empty_of_forall_not_mem hs'
    omega

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

lemma sum_insert_elem {ι : Type} [DecidableEq ι] [AddCommMonoid α] {s : Set ι} [Fintype s] {a : ι} (ha : a ∉ s) (f : ι → α) :
    ∑ i : (a ᕃ s).Elem, f i = f a + ∑ i : s.Elem, f i := by
  simp_all [Finset.sum_set_coe]

lemma finset_toSet_sum {ι : Type} [AddCommMonoid α] {S : Finset ι} {s : Set ι} [Fintype s] (hSs : S.toSet = s) (f : ι → α) :
    ∑ i : S.toSet, f i = ∑ i : s, f i := by
  apply Finset.sum_bij (fun a _ => ⟨a.val, hSs ▸ a.coe_prop⟩)
  · simp
  · simp
  · aesop
  · simp

lemma sum_over_fin_succ_of_only_zeroth_nonzero {n : ℕ} [AddCommMonoid α] {f : Fin n.succ → α}
    (hf : ∀ i : Fin n.succ, i ≠ 0 → f i = 0) :
    Finset.univ.sum f = f 0 := by
  apply fintype_sum_of_single_nonzero
  exact hf

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
  | `($_ $x) => `($(x).$(Lean.mkIdent `toSum))
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
