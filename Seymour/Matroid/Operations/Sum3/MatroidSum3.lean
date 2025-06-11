import Seymour.Matroid.Operations.Sum3.MatrixLikeSum3


/-! # Matroid-level 3-sum -/

/-! ## Additional notation for convenience -/

/-! ### Removing bundled elements from sets -/

variable {α : Type}

/-- Remove one bundled element from a set. -/
private abbrev Set.drop1 (Z : Set α) (z₀ : Z) : Set α := Z \ {z₀.val}

@[app_unexpander Set.drop1]
private def Set.drop1_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop1))
  | _ => throw ()

/-- Remove two bundled elements from a set. -/
private abbrev Set.drop2 (Z : Set α) (z₀ z₁ : Z) : Set α := Z \ {z₀.val, z₁.val}

@[app_unexpander Set.drop2]
private def Set.drop2_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop2))
  | _ => throw ()

/-- Remove three bundled elements from a set. -/
private abbrev Set.drop3 (Z : Set α) (z₀ z₁ z₂ : Z) : Set α := Z \ {z₀.val, z₁.val, z₂.val}

@[app_unexpander Set.drop3]
private def Set.drop3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop3))
  | _ => throw ()

private def undrop3 {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : Z :=
  ⟨i.val, i.property.left⟩

private lemma drop3_ne_fst {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : i.val ≠ z₀.val := by
  have hi := i.property.right
  simp at hi
  exact hi.left

private lemma drop3_ne_snd {Z : Set α} {z₀ z₁ z₂ : Z} (i : Z.drop3 z₀ z₁ z₂) : i.val ≠ z₁.val := by
  have hi := i.property.right
  simp at hi
  exact hi.right.left


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

private lemma Matrix.IsSigningOf.toBlockSummandₗ {Xₗ Yₗ : Set α} {F : Type} [LinearOrderedRing F]
    {Bₗ : Matrix Xₗ Yₗ F} {n : ℕ} {Aₗ : Matrix Xₗ Yₗ (ZMod n)}
    (hBAₗ : Bₗ.IsSigningOf Aₗ) (x₀ x₁ x₂ : Xₗ) (y₀ y₁ y₂ : Yₗ) :
    (Bₗ.toBlockSummandₗ x₀ x₁ x₂ y₀ y₁ y₂).IsSigningOf (Aₗ.toBlockSummandₗ x₀ x₁ x₂ y₀ y₁ y₂) :=
  hBAₗ.submatrix _ _

private lemma Matrix.IsSigningOf.toBlockSummandᵣ {Xᵣ Yᵣ : Set α} {F : Type} [LinearOrderedRing F]
    {Bᵣ : Matrix Xᵣ Yᵣ F} {n : ℕ} {Aᵣ : Matrix Xᵣ Yᵣ (ZMod n)}
    (hBAᵣ : Bᵣ.IsSigningOf Aᵣ) (x₀ x₁ x₂ : Xᵣ) (y₀ y₁ y₂ : Yᵣ) :
    (Bᵣ.toBlockSummandᵣ x₀ x₁ x₂ y₀ y₁ y₂).IsSigningOf (Aᵣ.toBlockSummandᵣ x₀ x₁ x₂ y₀ y₁ y₂) :=
  hBAᵣ.submatrix _ _

variable [DecidableEq α]

def standardReprMatrixSum3 (Sₗ Sᵣ : StandardRepr α Z2)
    (x₀ₗ x₁ₗ x₂ₗ : Sₗ.X) (y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y) (x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X) (y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y) :
    MatrixSum3 (Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ) (Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) Z2 :=
  MatrixSum3.fromBlockSummands (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)

def Matrix.toDropUnionDrop {Xₗ Yₗ Xᵣ Yᵣ : Set α} {F : Type}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A :
      Matrix
        ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Fin 1) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
        ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Fin 1 ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
        F
    ) :
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


/-! ## The 3-sum of standard representations -/

noncomputable def standardRepr3sumComposition {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  -- Elements of the intersection as elements of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.interAll3
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.interAll3
  ⟨
    -- Construction
    ⟨
      -- row indices
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      -- col indices
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      -- row and col indices are disjoint
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      -- the standard representation matrix
      (standardReprMatrixSum3 Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).matrix.toDropUnionDrop,
      -- decidability of row indices
      inferInstance,
      -- decidability of col indices
      inferInstance,
    ⟩,
    -- Correctness
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

lemma standardRepr3sumComposition_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α} (hx₀ : x₁ ≠ x₂) (hx₁ : x₀ ≠ x₂)
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X} :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = Sₗ.X ∪ Sᵣ.X := by
  ext a
  if hax₂ : a = x₂ then
    simp [standardRepr3sumComposition, *, hXX.mem3₂ₗ, Ne.symm hx₀, Ne.symm hx₁]
  else if hax₀ : a = x₀ then
    simp [standardRepr3sumComposition, *, hXX.mem3₀ᵣ]
  else if hax₁ : a = x₁ then
    simp [standardRepr3sumComposition, *, hXX.mem3₁ᵣ]
  else
    simp [standardRepr3sumComposition, *]

lemma standardRepr3sumComposition_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α} (hy₀ : y₁ ≠ y₂) (hy₁ : y₀ ≠ y₂)
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X} :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = Sₗ.Y ∪ Sᵣ.Y := by
  ext a
  if hay₂ : a = y₂ then
    simp [standardRepr3sumComposition, *, hYY.mem3₂ᵣ, Ne.symm hy₀, Ne.symm hy₁]
  else if hay₀ : a = y₀ then
    simp [standardRepr3sumComposition, *, hYY.mem3₀ₗ]
  else if hay₁ : a = y₁ then
    simp [standardRepr3sumComposition, *, hYY.mem3₁ₗ]
  else
    simp [standardRepr3sumComposition, *]

lemma standardRepr3sumComposition_Bₗ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sₗ.B ⟨x₀, hXX.mem3₀ₗ⟩ ⟨y₀, hYY.mem3₀ₗ⟩ = 1 :=
  hSS.right.right.left.casesOn (congr_fun₂ · 0 0) (congr_fun₂ · 0 0)

lemma standardRepr3sumComposition_Bᵣ₀₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sᵣ.B ⟨x₀, hXX.mem3₀ᵣ⟩ ⟨y₀, hYY.mem3₀ᵣ⟩ = 1 :=
  standardRepr3sumComposition_Bₗ₀₀ hSS ▸ congr_fun₂ hSS.right.left.symm 0 0

lemma standardRepr3sumComposition_Bₗ₁₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sₗ.B ⟨x₁, hXX.mem3₁ₗ⟩ ⟨y₀, hYY.mem3₀ₗ⟩ = 0 :=
  hSS.right.right.left.casesOn (congr_fun₂ · 1 0) (congr_fun₂ · 1 0)

lemma standardRepr3sumComposition_Bᵣ₁₀ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sᵣ.B ⟨x₁, hXX.mem3₁ᵣ⟩ ⟨y₀, hYY.mem3₀ᵣ⟩ = 0 :=
  standardRepr3sumComposition_Bₗ₁₀ hSS ▸ congr_fun₂ hSS.right.left.symm 1 0

lemma standardRepr3sumComposition_Bₗ₁₁ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sₗ.B ⟨x₁, hXX.mem3₁ₗ⟩ ⟨y₁, hYY.mem3₁ₗ⟩ = 1 :=
  hSS.right.right.left.casesOn (congr_fun₂ · 1 1) (congr_fun₂ · 1 1)

lemma standardRepr3sumComposition_Bᵣ₁₁ {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    {hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}} {hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    Sᵣ.B ⟨x₁, hXX.mem3₁ᵣ⟩ ⟨y₁, hYY.mem3₁ᵣ⟩ = 1 :=
  standardRepr3sumComposition_Bₗ₁₁ hSS ▸ congr_fun₂ hSS.right.left.symm 1 1

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B.HasTuSigning := by
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
  -- signing witnesses
  obtain ⟨Bₗ, hBₗ, hSBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hSBᵣ⟩ := hSᵣ
  -- signing of the entire thing
  let M := standardReprMatrixSum3 Sₗ Sᵣ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
  have hM : M.HasCanonicalSigning
  · constructor
    · simp only [standardRepr3sumComposition, and_imp] at hSS
      constructor
      · use Bₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ, hBₗ.submatrix _ _
        convert hSBₗ.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
        conv_rhs => rw [←(Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ).fromBlocks_toBlocks]
        simp only [M, standardReprMatrixSum3, MatrixSum3.Bₗ, MatrixSum3.fromBlockSummands,
          Matrix.fromCols_toCols, Matrix.fromBlocks_inj, true_and]
        constructor
        · ext i j
          fin_cases j
          simp [Matrix.toBlockSummandₗ, Matrix.toBlocks₁₂]
          cases i with
          | inl x => exact (hSS.right.right.right.right.right.right.right.left x.val x.property.left (drop3_ne_fst x) (drop3_ne_snd x)).symm
          | inr => exact (hSS.right.right.right.right.right.right.right.left x₂ hXX.mem3₂ₗ (by tauto) (by tauto)).symm
        · ext i j
          fin_cases j
          fin_cases i <;> tauto
      · use Bᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ, hBᵣ.submatrix _ _
        convert hSBᵣ.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
        conv_rhs => rw [←(Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ).fromBlocks_toBlocks]
        simp only [M, standardReprMatrixSum3, MatrixSum3.Bᵣ, MatrixSum3.fromBlockSummands,
          Matrix.fromRows_toRows, Matrix.fromBlocks_inj, and_true]
        constructor
        · ext i j
          fin_cases i
          fin_cases j <;> tauto
        · ext i j
          fin_cases i
          simp [Matrix.toBlockSummandᵣ, Matrix.toBlocks₁₂]
          cases j with
          | inl => exact (hSS.right.right.right.right.right.right.right.right.right.right.right.right y₂ hYY.mem3₂ᵣ (by tauto) (by tauto)).symm
          | inr y => exact (hSS.right.right.right.right.right.right.right.right.right.right.right.right y.val y.property.left (drop3_ne_fst y) (drop3_ne_snd y)).symm
    · cases hSS.right.right.left with
      | inl h1001 =>
        left
        constructor
        · ext i j
          fin_cases i <;> fin_cases j
          · exact standardRepr3sumComposition_Bₗ₀₀ hSS
          · exact congr_fun₂ h1001 0 1
          · rfl
          · exact standardRepr3sumComposition_Bₗ₁₀ hSS
          · exact standardRepr3sumComposition_Bₗ₁₁ hSS
          · rfl
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · rfl
        · ext i j
          fin_cases i <;> fin_cases j
          · exact standardRepr3sumComposition_Bᵣ₀₀ hSS
          · convert congr_fun₂ hSS.right.left.symm 0 1 ▸ congr_fun₂ h1001 0 1
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · exact standardRepr3sumComposition_Bᵣ₁₀ hSS
          · exact standardRepr3sumComposition_Bᵣ₁₁ hSS
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · rfl
          · rfl
          · rfl
      | inr h1101 =>
        right
        constructor
        · ext i j
          fin_cases i <;> fin_cases j
          · exact standardRepr3sumComposition_Bₗ₀₀ hSS
          · exact congr_fun₂ h1101 0 1
          · rfl
          · exact standardRepr3sumComposition_Bₗ₁₀ hSS
          · exact standardRepr3sumComposition_Bₗ₁₁ hSS
          · rfl
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · rfl
        · ext i j
          fin_cases i <;> fin_cases j
          · exact standardRepr3sumComposition_Bᵣ₀₀ hSS
          · convert congr_fun₂ hSS.right.left.symm 0 1 ▸ congr_fun₂ h1101 0 1
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · exact standardRepr3sumComposition_Bᵣ₁₀ hSS
          · exact standardRepr3sumComposition_Bᵣ₁₁ hSS
          · simp only [standardRepr3sumComposition] at hSS; tauto
          · rfl
          · rfl
          · rfl
  -- direct application of existing lemmas
  obtain ⟨B, hB, hBM⟩ := hM.HasTuSigning
  use B.toDropUnionDrop
  constructor
  · apply hB.submatrix
  · apply hBM.submatrix


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
  hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr3sumComposition hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

/-- 3-sum of two regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _,_, _, rfl, hMMM⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
  · exact hMMM
