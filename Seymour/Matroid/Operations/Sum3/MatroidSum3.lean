import Seymour.Matroid.Operations.Sum3.MatrixLikeSum3


/-! # Matroid-level 3-sum -/

/-! ## Additional notation for convenience -/

/-! ### Removing bundled elements from sets -/

variable {α : Type}

/-- Remove one bundled element from a set. -/
@[simp]
private abbrev Set.drop1 (X : Set α) (x₀ : X) : Set α := X \ {x₀.val}

@[app_unexpander Set.drop1]
private def Set.drop1_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop1))
  | _ => throw ()

/-- Remove two bundled elements from a set. -/
@[simp]
private abbrev Set.drop2 (X : Set α) (x₀ x₁ : X) : Set α := X \ {x₀.val, x₁.val}

@[app_unexpander Set.drop2]
private def Set.drop2_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop2))
  | _ => throw ()

/-- Remove three bundled elements from a set. -/
@[simp]
private abbrev Set.drop3 (X : Set α) (x₀ x₁ x₂ : X) : Set α := X \ {x₀.val, x₁.val, x₂.val}

@[app_unexpander Set.drop3]
private def Set.drop3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop3))
  | _ => throw ()

@[simp]
private abbrev undrop1 {X : Set α} {x₀ : X} (i : X.drop1 x₀) : X :=
  ⟨i.val, i.property.left⟩

@[simp]
private abbrev undrop2 {X : Set α} {x₀ x₁ : X} (i : X.drop2 x₀ x₁) : X :=
  ⟨i.val, i.property.left⟩

@[simp]
private abbrev undrop3 {X : Set α} {x₀ x₁ x₂ : X} (i : X.drop3 x₀ x₁ x₂) : X :=
  ⟨i.val, i.property.left⟩

private lemma drop3_union_pair {X : Set α} {x₀ x₁ x₂ : X} (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) :
    X.drop3 x₀ x₁ x₂ ∪ {x₀.val, x₁.val} = X.drop1 x₂ := by
  ext a
  rw [←Subtype.coe_ne_coe] at hx₀ hx₁
  by_cases a = x₀ <;> by_cases a = x₁ <;> simp [*]

private lemma pair_union_drop3 {X : Set α} {x₀ x₁ x₂ : X} (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) :
    {x₀.val, x₁.val} ∪ X.drop3 x₀ x₁ x₂ = X.drop1 x₂ := by
  rw [Set.union_comm]
  exact drop3_union_pair hx₀ hx₁

private lemma drop3_union_elem {X : Set α} {x₀ x₁ x₂ : X} (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) :
    X.drop3 x₀ x₁ x₂ ∪ {x₂.val} = X.drop2 x₀ x₁ := by
  ext a
  rw [←Subtype.coe_ne_coe] at hx₀ hx₁
  have := hx₀.symm
  have := hx₁.symm
  by_cases a = x₂ <;> simp [*]

private lemma elem_union_drop3 {X : Set α} {x₀ x₁ x₂ : X} (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) :
    {x₂.val} ∪ X.drop3 x₀ x₁ x₂ = X.drop2 x₀ x₁ := by
  rw [Set.union_comm]
  exact drop3_union_elem hx₀ hx₁


/-! ### Re-typing elements of the triplet intersection -/

section triplets
variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

private lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ₗ]
private def Eq.mem3₀ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ₗ))
  | _ => throw ()

private lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ₗ]
private def Eq.mem3₁ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ₗ))
  | _ => throw ()

private lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

@[app_unexpander Eq.mem3₂ₗ]
private def Eq.mem3₂ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ₗ))
  | _ => throw ()

private lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ᵣ]
private def Eq.mem3₀ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ᵣ))
  | _ => throw ()

private lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ᵣ]
private def Eq.mem3₁ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ᵣ))
  | _ => throw ()

private lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

@[app_unexpander Eq.mem3₂ᵣ]
private def Eq.mem3₂ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ᵣ))
  | _ => throw ()

@[simp]
private def Eq.interAll3 (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : (Zₗ × Zₗ × Zₗ) × (Zᵣ × Zᵣ × Zᵣ) :=
  ⟨⟨⟨a₀, hZZ.mem3₀ₗ⟩, ⟨a₁, hZZ.mem3₁ₗ⟩, ⟨a₂, hZZ.mem3₂ₗ⟩⟩, ⟨⟨a₀, hZZ.mem3₀ᵣ⟩, ⟨a₁, hZZ.mem3₁ᵣ⟩, ⟨a₂, hZZ.mem3₂ᵣ⟩⟩⟩

@[app_unexpander Eq.interAll3]
private def Eq.interAll3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `inter3all))
  | _ => throw ()

end triplets


/-! ## New approach to conversion from union form to block form and vice versa -/

def Matrix.toBlockSummandₗ {Xₗ Yₗ : Set α} {F : Type} (Bₗ : Matrix Xₗ Yₗ F) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
    Matrix ((Xₗ.drop3 x₀ x₁ x₂ ⊕ Fin 1) ⊕ Fin 2) ((Yₗ.drop3 y₀ y₁ y₂ ⊕ Fin 2) ⊕ Fin 1) F :=
  Bₗ.submatrix (·.casesOn (·.casesOn undrop3 ![x₂]) ![x₀, x₁]) (·.casesOn (·.casesOn undrop3 ![y₀, y₁]) ![y₂])

def Matrix.toBlockSummandᵣ {Xᵣ Yᵣ : Set α} {F : Type} (Bᵣ : Matrix Xᵣ Yᵣ F) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
    Matrix (Fin 1 ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ x₁ x₂)) (Fin 2 ⊕ (Fin 1 ⊕ Yᵣ.drop3 y₀ y₁ y₂)) F :=
  Bᵣ.submatrix (·.casesOn ![x₂] (·.casesOn ![x₀, x₁] undrop3)) (·.casesOn ![y₀, y₁] (·.casesOn ![y₂] undrop3))

variable [DecidableEq α]

def Matrix.toSumUnion {Xₗ Yₗ Xᵣ Yᵣ : Set α} {F : Type}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A : Matrix ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Fin 1) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
                ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Fin 1 ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ)) F) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem F :=
  A.submatrix
    (fun i : (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem =>
      if hi₂ₗ : i.val = x₂ₗ then ◩◪0 else
      if hiₗ : i.val ∈ Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ then ◩◩⟨i, hiₗ⟩ else
      if hi₀ᵣ : i.val = x₀ᵣ then ◪◩0 else
      if hi₁ᵣ : i.val = x₁ᵣ then ◪◩1 else
      if hiᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then ◪◪⟨i, hiᵣ⟩ else
      False.elim (i.property.elim ↓(by simp_all) ↓(by simp_all)))
    (fun j : (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem =>
      if hj₀ₗ : j.val = y₀ₗ then ◩◪0 else
      if hj₁ₗ : j.val = y₁ₗ then ◩◪1 else
      if hjₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then ◩◩⟨j, hjₗ⟩ else
      if hj₂ᵣ : j.val = y₂ᵣ then ◪◩0 else
      if hjᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then ◪◪⟨j, hjᵣ⟩ else
      False.elim (j.property.elim ↓(by simp_all) ↓(by simp_all)))

def standardReprMatrixSum3 (Sₗ Sᵣ : StandardRepr α Z2)
    (x₀ₗ x₁ₗ x₂ₗ : Sₗ.X) (y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y) (x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X) (y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y) :
    MatrixSum3 (Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ) (Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) Z2 :=
  MatrixSum3.fromBlockSummands (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)

noncomputable def standardRepr3sumComposition {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.interAll3
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.interAll3
  ⟨
    ⟨
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (standardReprMatrixSum3 Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix.toSumUnion,
      inferInstance,
      inferInstance,
    ⟩,
     -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ]
    -- `D₀` has the correct form
    ∧ (!![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = 1 ∨
       !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![1, 1; 0, 1])
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
  ⟩


/-! ## The 3-sum of standard representations -/

/-- Convert `(X₁₁.Elem ⊕ X₁₂.Elem) ⊕ (X₂₁.Elem ⊕ X₂₂.Elem)` to `((X₁₁ ∪ X₁₂) ∪ (X₂₁ ∪ X₂₂)).Elem`. -/
@[deprecated Matrix.toSumUnion (since := "2025-06-06")]
def Sum.toUnionUnionUnion {X₁₁ X₁₂ X₂₁ X₂₂ : Set α} (i : (X₁₁.Elem ⊕ X₁₂.Elem) ⊕ (X₂₁.Elem ⊕ X₂₂.Elem)) :
    ((X₁₁ ∪ X₁₂) ∪ (X₂₁ ∪ X₂₂)).Elem :=
  i.casesOn (Set.subset_union_left.elem ·.toUnion) (Set.subset_union_right.elem ·.toUnion)

/-- Convert `((X₁₁ ∪ X₁₂) ∪ (X₂₁ ∪ X₂₂)).Elem` to `(X₁₁.Elem ⊕ X₁₂.Elem) ⊕ (X₂₁.Elem ⊕ X₂₂.Elem)`. -/
@[deprecated Matrix.toSumUnion (since := "2025-06-06")]
def Subtype.toSumSumSum {X₁₁ X₁₂ X₂₁ X₂₂ : Set α}
    [∀ a, Decidable (a ∈ X₁₁)] [∀ a, Decidable (a ∈ X₁₂)] [∀ a, Decidable (a ∈ X₂₁)] [∀ a, Decidable (a ∈ X₂₂)]
    (i : ((X₁₁ ∪ X₁₂) ∪ (X₂₁ ∪ X₂₂)).Elem) :
    (X₁₁.Elem ⊕ X₁₂.Elem) ⊕ (X₂₁.Elem ⊕ X₂₂.Elem) :=
  if hiX₁₁ : i.val ∈ X₁₁ then ◩◩⟨i, hiX₁₁⟩ else
  if hiX₁₂ : i.val ∈ X₁₂ then ◩◪⟨i, hiX₁₂⟩ else
  if hiX₂₁ : i.val ∈ X₂₁ then ◪◩⟨i, hiX₂₁⟩ else
  if hiX₂₂ : i.val ∈ X₂₂ then ◪◪⟨i, hiX₂₂⟩ else
  (i.property.elim (·.elim hiX₁₁ hiX₁₂) (·.elim hiX₂₁ hiX₂₂)).elim

/-- Convert a nested block matrix to a matrix over nested set unions. -/
@[deprecated Matrix.toSumUnion (since := "2025-06-06")]
def Matrix.toMatrixUnionNested {X₁₁ X₁₂ X₂₁ X₂₂ Y₁₁ Y₁₂ Y₂₁ Y₂₂ : Set α} {R : Type}
    [∀ a, Decidable (a ∈ X₁₁)] [∀ a, Decidable (a ∈ X₁₂)] [∀ a, Decidable (a ∈ X₂₁)] [∀ a, Decidable (a ∈ X₂₂)]
    [∀ a, Decidable (a ∈ Y₁₁)] [∀ a, Decidable (a ∈ Y₁₂)] [∀ a, Decidable (a ∈ Y₂₁)] [∀ a, Decidable (a ∈ Y₂₂)]
    (A : Matrix ((X₁₁.Elem ⊕ X₁₂.Elem) ⊕ (X₂₁.Elem ⊕ X₂₂.Elem)) ((Y₁₁.Elem ⊕ Y₁₂.Elem) ⊕ (Y₂₁.Elem ⊕ Y₂₂.Elem)) R) :
    Matrix ((X₁₁ ∪ X₁₂) ∪ (X₂₁ ∪ X₂₂)).Elem ((Y₁₁ ∪ Y₁₂) ∪ (Y₂₁ ∪ Y₂₂)).Elem R :=
  ((A ∘ Subtype.toSumSumSum) · ∘ Subtype.toSumSumSum)

@[deprecated standardReprMatrixSum3 (since := "2025-06-06")]
def standardReprMatrixSum3' (Sₗ Sᵣ : StandardRepr α Z2)
    (x₀ₗ x₁ₗ x₂ₗ : Sₗ.X) (y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y) (x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X) (y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y) :
    MatrixSum3 (Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ) (Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) Z2 where
  Aₗ := Sₗ.B.submatrix (·.casesOn undrop3 ↓x₂ₗ) (·.casesOn undrop3 ![y₀ₗ, y₁ₗ])
  Dₗ := ![Sₗ.B x₀ₗ ∘ Set.diff_subset.elem, Sₗ.B x₁ₗ ∘ Set.diff_subset.elem]
  D₀ₗ := !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ]
  D₀ᵣ := !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ]
  Dᵣ := Matrix.of (fun i => ![Sᵣ.B (Set.diff_subset.elem i) y₀ᵣ, Sᵣ.B (Set.diff_subset.elem i) y₁ᵣ])
  Aᵣ := Sᵣ.B.submatrix (·.casesOn ![x₀ᵣ, x₁ᵣ] undrop3) (·.casesOn ↓y₂ᵣ undrop3)

@[deprecated standardRepr3sumComposition (since := "2025-06-06")]
noncomputable def standardRepr3sumComposition_B' (Sₗ Sᵣ : StandardRepr α Z2)
    {x₀ₗ x₁ₗ x₂ₗ : Sₗ.X} {y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y} {x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X} {y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y}
    (hx₀ₗ : x₁ₗ ≠ x₂ₗ) (hx₁ₗ : x₀ₗ ≠ x₂ₗ) (hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ) (hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ) (hx₂ᵣ : x₁ᵣ ≠ x₀ᵣ)
    (hy₀ₗ : y₁ₗ ≠ y₂ₗ) (hy₁ₗ : y₀ₗ ≠ y₂ₗ) (hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ) (hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ) (hy₂ᵣ : y₁ₗ ≠ y₀ₗ) :
    Matrix (Sₗ.X.drop2 x₀ₗ x₁ₗ ∪ Sᵣ.X.drop1 x₂ᵣ).Elem (Sₗ.Y.drop1 y₂ₗ ∪ Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ).Elem Z2 :=
  drop3_union_elem hx₀ₗ hx₁ₗ ▸ drop3_union_pair hy₀ₗ hy₁ₗ ▸
  elem_union_drop3 hy₀ᵣ hy₁ᵣ ▸ pair_union_drop3 hx₀ᵣ hx₁ᵣ ▸
  ((standardReprMatrixSum3 Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix.reindex
    (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) (equivFin1 x₂ₗ)) (Equiv.sumCongr (equivFin2 hx₂ᵣ) (Equiv.refl _)))
    (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) (equivFin2 hy₂ᵣ)) (Equiv.sumCongr (equivFin1 y₂ᵣ) (Equiv.refl _)))
  ).toMatrixUnionNested

@[deprecated standardRepr3sumComposition (since := "2025-06-06")]
noncomputable def standardRepr3sumComposition' {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  -- row membership
  let x₀ₗ : Sₗ.X := ⟨x₀, hXX.mem3₀ₗ⟩
  let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.mem3₀ᵣ⟩
  let x₁ₗ : Sₗ.X := ⟨x₁, hXX.mem3₁ₗ⟩
  let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.mem3₁ᵣ⟩
  let x₂ₗ : Sₗ.X := ⟨x₂, hXX.mem3₂ₗ⟩
  let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.mem3₂ᵣ⟩
  -- col membership
  let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.mem3₀ₗ⟩
  let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.mem3₀ᵣ⟩
  let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.mem3₁ₗ⟩
  let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.mem3₁ᵣ⟩
  let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.mem3₂ₗ⟩
  let y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.mem3₂ᵣ⟩
  -- inequalities but bundled
  have hx₁ₗ : x₀ₗ ≠ x₂ₗ := hx₁ ∘ congr_arg Subtype.val
  have hx₀ₗ : x₁ₗ ≠ x₂ₗ := hx₀ ∘ congr_arg Subtype.val
  have hx₁ᵣ : x₀ᵣ ≠ x₂ᵣ := hx₁ ∘ congr_arg Subtype.val
  have hx₀ᵣ : x₁ᵣ ≠ x₂ᵣ := hx₀ ∘ congr_arg Subtype.val
  have hx₂ᵣ : x₁ᵣ ≠ x₀ᵣ := hx₂ ∘ congr_arg Subtype.val
  have hy₁ₗ : y₀ₗ ≠ y₂ₗ := hy₁ ∘ congr_arg Subtype.val
  have hy₀ₗ : y₁ₗ ≠ y₂ₗ := hy₀ ∘ congr_arg Subtype.val
  have hy₁ᵣ : y₀ᵣ ≠ y₂ᵣ := hy₁ ∘ congr_arg Subtype.val
  have hy₀ᵣ : y₁ᵣ ≠ y₂ᵣ := hy₀ ∘ congr_arg Subtype.val
  have hy₂ₗ : y₁ₗ ≠ y₀ₗ := hy₂ ∘ congr_arg Subtype.val
  ⟨
    ⟨
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      standardRepr3sumComposition_B' Sₗ Sᵣ hx₀ₗ hx₁ₗ hx₀ᵣ hx₁ᵣ hx₂ᵣ hy₀ₗ hy₁ₗ hy₀ᵣ hy₁ᵣ hy₂ₗ,
      inferInstance,
      inferInstance,
    ⟩,
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ]
    -- `D₀` has the correct form
    ∧ (!![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = 1 ∨
       !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ] = !![1, 1; 0, 1])
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
  ⟩

lemma standardRepr3sumComposition_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).fst.X = Sₗ.X ∪ Sᵣ.X := by
  ext a
  if hax₂ : a = x₂ then
    simp [standardRepr3sumComposition', *, hXX.mem3₂ₗ, Ne.symm hx₀, Ne.symm hx₁]
  else if hax₀ : a = x₀ then
    simp [standardRepr3sumComposition', *, hXX.mem3₀ᵣ]
  else if hax₁ : a = x₁ then
    simp [standardRepr3sumComposition', *, hXX.mem3₁ᵣ]
  else
    simp [standardRepr3sumComposition', *]

lemma standardRepr3sumComposition_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).fst.Y = Sₗ.Y ∪ Sᵣ.Y := by
  ext a
  if hay₂ : a = y₂ then
    simp [standardRepr3sumComposition', *, hYY.mem3₂ᵣ, Ne.symm hy₀, Ne.symm hy₁]
  else if hay₀ : a = y₀ then
    simp [standardRepr3sumComposition', *, hYY.mem3₀ₗ]
  else if hay₁ : a = y₁ then
    simp [standardRepr3sumComposition', *, hYY.mem3₁ₗ]
  else
    simp [standardRepr3sumComposition', *]

lemma standardRepr3sumComposition_Bₗ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSS : (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).snd) :
    Sₗ.B ⟨x₀, hXX.mem3₀ₗ⟩ ⟨y₀, hYY.mem3₀ₗ⟩ = 1 :=
  hSS.right.left.casesOn (congr_fun₂ · 0 0) (congr_fun₂ · 0 0)

lemma standardRepr3sumComposition_Bᵣ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSS : (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).snd) :
    Sᵣ.B ⟨x₀, hXX.mem3₀ᵣ⟩ ⟨y₀, hYY.mem3₀ᵣ⟩ = 1 := by
  rw [←standardRepr3sumComposition_Bₗ₀₀ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX hSS]
  exact congr_fun₂ hSS.left.symm 0 0

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂) (hx₂ : x₁ ≠ x₀) (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂) (hy₂ : y₁ ≠ y₀)
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hSS : (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).snd) :
    (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).fst.B.HasTuSigning := by
  sorry


/-! ## The 3-sum of matroids -/

/-- Matroid `M` is a result of 3-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop`, but treat it as a predicate. -/
structure Matroid.Is3sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  (x₀ x₁ x₂ y₀ y₁ y₂ : α)
  hx₀ : x₁ ≠ x₂
  hx₁ : x₀ ≠ x₂
  hx₂ : x₁ ≠ x₀
  hy₀ : y₁ ≠ y₂
  hy₁ : y₀ ≠ y₂
  hy₂ : y₁ ≠ y₀
  hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition' hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

/-- 3-sum of two regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _,_, _, _, _, _, _, _, _, rfl, hMMM⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
  · exact hMMM
