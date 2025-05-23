import Seymour.Matroid.Constructors.StandardRepresentation


variable {α : Type}

section members_of_intersection

variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

private lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ₗ]
def Eq.mem3₀ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ₗ))
  | _ => throw ()

private lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ₗ]
def Eq.mem3₁ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ₗ))
  | _ => throw ()

private lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

@[app_unexpander Eq.mem3₂ₗ]
def Eq.mem3₂ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ₗ))
  | _ => throw ()

private lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ᵣ]
def Eq.mem3₀ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ᵣ))
  | _ => throw ()

private lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ᵣ]
def Eq.mem3₁ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ᵣ))
  | _ => throw ()

private lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

@[app_unexpander Eq.mem3₂ᵣ]
def Eq.mem3₂ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ᵣ))
  | _ => throw ()

private def Eq.inter3all (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : (Zₗ × Zₗ × Zₗ) × (Zᵣ × Zᵣ × Zᵣ) :=
  ⟨⟨⟨a₀, hZZ.mem3₀ₗ⟩, ⟨a₁, hZZ.mem3₁ₗ⟩, ⟨a₂, hZZ.mem3₂ₗ⟩⟩, ⟨⟨a₀, hZZ.mem3₀ᵣ⟩, ⟨a₁, hZZ.mem3₁ᵣ⟩, ⟨a₂, hZZ.mem3₂ᵣ⟩⟩⟩

@[app_unexpander Eq.inter3all]
def Eq.inter3all_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `inter3all))
  | _ => throw ()

end members_of_intersection


section Current

@[simp]
private abbrev Matrix.D₀ {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Fin 2) F :=
  !![B x₀ y₀, B x₀ y₁; B x₁ y₀, B x₁ y₁]

@[app_unexpander Matrix.D₀]
def Matrix.D₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `D₀))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dₗ {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (a₀ a₁ a₂ : α) :
    Matrix (Fin 2) (Y \ {a₀, a₁, a₂}).Elem F :=
  ![B x₀ ∘ Set.diff_subset.elem, B x₁ ∘ Set.diff_subset.elem]

@[app_unexpander Matrix.Dₗ]
def Matrix.Dₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Dₗ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dᵣ {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ x₂ : α) (y₀ y₁ : Y) :
    Matrix (X \ {x₀, x₁, x₂}).Elem (Fin 2) F :=
  Matrix.of (fun i => ![B (Set.diff_subset.elem i) y₀, B (Set.diff_subset.elem i) y₁])

@[app_unexpander Matrix.Dᵣ]
def Matrix.Dᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Dᵣ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aₗ {X Y : Set α} {F : Type} (B : Matrix X Y F) (a₀ a₁ a' : α) :
    Matrix (X \ {a₀, a₁}).Elem (Y \ {a'}).Elem F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aₗ]
def Matrix.Aₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Aₗ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aᵣ {X Y : Set α} {F : Type} (B : Matrix X Y F) (a' a₀ a₁ : α) :
    Matrix (X \ {a'}).Elem (Y \ {a₀, a₁}).Elem F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aᵣ]
def Matrix.Aᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Aᵣ))
  | _ => throw ()

@[simp]
private abbrev mapX [DecidableEq α] {X : Set α} {a₀ a₁ a' : α} [∀ x, Decidable (x ∈ X)] (i : (X \ {a'}).Elem) :
    Fin 2 ⊕ (X \ {a₀, a₁, a'}).Elem :=
  if hi₀ : i.val = a₀ then ◩0 else
  if hi₁ : i.val = a₁ then ◩1 else
  if hi : i.val ∈ X \ {a₀, a₁, a'} then ◪⟨i, hi⟩ else
  (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim

@[simp]
private abbrev mapY [DecidableEq α] {Y : Set α} {a₀ a₁ a' : α} [∀ x, Decidable (x ∈ Y)] (j : (Y \ {a'}).Elem) :
    (Y \ {a₀, a₁, a'}).Elem ⊕ Fin 2 :=
  if hj₀ : j.val = a₀ then ◪0 else
  if hj₁ : j.val = a₁ then ◪1 else
  if hj : j.val ∈ Y \ {a₀, a₁, a'} then ◩⟨j, hj⟩ else
  (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim

/-- The 3-sum composition of two matrices. -/
noncomputable def matrix3sumComposition_curr [DecidableEq α] {F : Type} [Field F]
    {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (Bₗ : Matrix Xₗ Yₗ F) (Bᵣ : Matrix Xᵣ Yᵣ F) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x₂}).Elem) ((Yₗ \ {y₂}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) F :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, _x₂ₗ⟩, ⟨_x₀ᵣ, _x₁ᵣ, _x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, _y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _y₂ᵣ⟩⟩ := hYY.inter3all
  -- pieces of the bottom left submatrix
  let D₀ₗ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  -- let D₀ᵣ := Bᵣ.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
  let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ y₁ y₂
  let Dᵣ := Bᵣ.Dᵣ x₀ x₁ x₂ y₀ᵣ y₁ᵣ
  -- the actual definition: 3-sum defined as a block matrix
  ⊞ (Bₗ.Aₗ x₀ x₁ y₂) 0 ((⊞ Dₗ D₀ₗ (Dᵣ * D₀ₗ⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) (Bᵣ.Aᵣ x₂ y₀ y₁)

noncomputable def standardRepr3sumComposition_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 :=
  ⟨
    (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x₂}),
    (Sₗ.Y \ {y₂}) ∪ (Sᵣ.Y \ {y₀, y₁}),
    by
      rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
      exact
        ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
        ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
    (matrix3sumComposition_curr Sₗ.B Sᵣ.B hXX hYY).toMatrixUnionUnion,
    inferInstance,
    inferInstance,
  ⟩

/-!
  This is the definition we are currently using. It generates a lot of boilerplate on the matrix level.
  Below we try several alternative definitions.
  The goal is to simplify implementation on the matrix level while preserving definitional equality at least on the matroid
  (standard representation) level.
-/

end Current


section Alt1

@[simp]
private abbrev mapX_alt1 [DecidableEq α] {X : Set α} {a₀ a₁ a' : X} [∀ x, Decidable (x ∈ X)] (i : (X \ {a'.val}).Elem) :
    Fin 2 ⊕ (X \ {a₀.val, a₁.val, a'.val}).Elem :=
  if hi₀ : i.val = a₀ then ◩0 else
  if hi₁ : i.val = a₁ then ◩1 else
  if hi : i.val ∈ X \ {a₀.val, a₁.val, a'.val} then ◪⟨i, hi⟩ else
  (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim

@[simp]
private abbrev mapY_alt1 [DecidableEq α] {Y : Set α} {a₀ a₁ a' : Y} [∀ x, Decidable (x ∈ Y)] (j : (Y \ {a'.val}).Elem) :
    (Y \ {a₀.val, a₁.val, a'.val}).Elem ⊕ Fin 2 :=
  if hj₀ : j.val = a₀ then ◪0 else
  if hj₁ : j.val = a₁ then ◪1 else
  if hj : j.val ∈ Y \ {a₀.val, a₁.val, a'.val} then ◩⟨j, hj⟩ else
  (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim

noncomputable def matrix3sumComposition_alt1 [DecidableEq α] {F : Type} [Field F]
    {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (x₀ₗ x₁ₗ : Xₗ) (y₀ₗ y₁ₗ y₂ₗ : Yₗ)
    (x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ) (y₀ᵣ y₁ᵣ : Yᵣ)
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (Bₗ : Matrix Xₗ Yₗ F) (Bᵣ : Matrix Xᵣ Yᵣ F) :
    Matrix ((Xₗ \ {x₀ₗ.val, x₁ₗ.val}).Elem ⊕ (Xᵣ \ {x₂ᵣ.val}).Elem) ((Yₗ \ {y₂ₗ.val}).Elem ⊕ (Yᵣ \ {y₀ᵣ.val, y₁ᵣ.val}).Elem) F :=
  -- pieces of the bottom left submatrix
  let D₀ₗ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  -- the actual definition: 3-sum defined as a block matrix
  ⊞ (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ) 0 ((⊞ Dₗ D₀ₗ (Dᵣ * D₀ₗ⁻¹ * Dₗ) Dᵣ).submatrix mapX_alt1 mapY_alt1) (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ)

lemma matrix3sumComposition_alt1_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Sₗ.X := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Sₗ.X := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.mem3₁ᵣ⟩
    let _x₂ₗ : Sₗ.X := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.mem3₂ₗ⟩
    let _y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.mem3₂ᵣ⟩
    (matrix3sumComposition_alt1 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Sₗ.B Sᵣ.B) =
    (matrix3sumComposition_curr Sₗ.B Sᵣ.B hXX hYY) := by
  rfl

noncomputable def standardRepr3sumComposition_alt1 [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 :=
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  ⟨
    (Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val}),
    (Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val}),
    by
      rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
      exact
        ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
        ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
    (matrix3sumComposition_alt1 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Sₗ.B Sᵣ.B).toMatrixUnionUnion,
    inferInstance,
    inferInstance,
  ⟩

lemma standardRepr3sumComposition_alt1_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    standardRepr3sumComposition_alt1 hXX hYY hXY hYX = standardRepr3sumComposition_curr hXX hYY hXY hYX := by
  rfl

/-!
  This definition re-types the special row and column indices asap: e.g., from `x₀ ∈ Sₗ.X ∩ Sᵣ.X` to `x₀ₗ : Xₗ` and `x₀ᵣ : Xᵣ`.
  This could lead to simplifications on the matrix level related to the type conversion of the special row and column indices.
  Still, the boilerplate related to breaking the input matrices into submatrices will remain.
-/

end Alt1


section Alt2

noncomputable def matrix3sumComposition_alt2 {F : Type} [Field F]
    {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ F)
    (Aₗ' : Matrix Xₗ (Fin 2) F)
    (Dₗ : Matrix (Fin 2) Yₗ F)
    (D₀ : Matrix (Fin 2) (Fin 2) F)
    (Dᵣ : Matrix Xᵣ (Fin 2) F)
    (Aᵣ' : Matrix (Fin 2) Yᵣ F)
    (Aᵣ : Matrix Xᵣ Yᵣ F) :
    Matrix (Xₗ ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ Yᵣ) F :=
  ⊞ (Aₗ ◫ Aₗ') 0 (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ) (Aᵣ' ⊟ Aᵣ)

@[simp]
private abbrev Matrix.Aₗ_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ y₂ : Y) :
    Matrix (X \ {x₀.val, x₁.val}).Elem (Y \ {y₀.val, y₁.val, y₂.val}).Elem F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[simp]
private abbrev Matrix.Aₗ'_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (X \ {x₀.val, x₁.val}).Elem (Fin 2) F :=
  B.submatrix Set.diff_subset.elem ![y₀, y₁]

@[simp]
private abbrev Matrix.Dₗ_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 2) (Y \ {y₀.val, y₁.val, y₂.val}).Elem F :=
  B.submatrix ![x₀, x₁] Set.diff_subset.elem

@[simp]
private abbrev Matrix.D₀_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Fin 2) F :=
  B.submatrix ![x₀, x₁] ![y₀, y₁]

@[simp]
private abbrev Matrix.Dᵣ_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ x₂ : X) (y₀ y₁ : Y) :
    Matrix (X \ {x₀.val, x₁.val, x₂.val}).Elem (Fin 2) F :=
  B.submatrix Set.diff_subset.elem ![y₀, y₁]

@[simp]
private abbrev Matrix.Aᵣ'_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Y \ {y₀.val, y₁.val}).Elem F :=
  B.submatrix ![x₀, x₁] Set.diff_subset.elem

@[simp]
private abbrev Matrix.Aᵣ_alt2 {X Y : Set α} {F : Type} (B : Matrix X Y F) (x₀ x₁ x₂ : X) (y₀ y₁ : Y) :
    Matrix (X \ {x₀.val, x₁.val, x₂.val}).Elem (Y \ {y₀.val, y₁.val}).Elem F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[simp]
private abbrev matrix3sumComposition_alt2_mapped' [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ x, Decidable (x ∈ Yₗ)] [∀ x, Decidable (x ∈ Yᵣ)]
    {x₀ₗ x₁ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ : Yᵣ}
    (S : Matrix ((Xₗ \ {x₀ₗ.val, x₁ₗ.val}).Elem ⊕ (Fin 2 ⊕ (Xᵣ \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem))
                (((Yₗ \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem ⊕ Fin 2) ⊕ (Yᵣ \ {y₀ᵣ.val, y₁ᵣ.val}).Elem) Z2) :
    Matrix ((Xₗ \ {x₀ₗ.val, x₁ₗ.val}).Elem ⊕ (Xᵣ \ {x₂ᵣ.val}).Elem)
           (((Yₗ \ {y₂ₗ.val}).Elem) ⊕ (Yᵣ \ {y₀ᵣ.val, y₁ᵣ.val}).Elem) Z2 :=
  S.submatrix (fun i => i.casesOn Sum.inl (Sum.inr ∘ mapX)) (fun j => j.casesOn (Sum.inl ∘ mapY) Sum.inr)

@[simp]
private abbrev matrix3sumComposition_alt2_mapped [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ x, Decidable (x ∈ Yₗ)] [∀ x, Decidable (x ∈ Yᵣ)]
    {x₀ₗ x₁ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ : Yᵣ}
    (S : Matrix ((Xₗ \ {x₀ₗ.val, x₁ₗ.val}).Elem ⊕ (Fin 2 ⊕ (Xᵣ \ {x₀ᵣ.val, x₁ᵣ.val, x₂ᵣ.val}).Elem))
                (((Yₗ \ {y₀ₗ.val, y₁ₗ.val, y₂ₗ.val}).Elem ⊕ Fin 2) ⊕ (Yᵣ \ {y₀ᵣ.val, y₁ᵣ.val}).Elem) Z2) :
    Matrix ((Xₗ \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Xᵣ \ {x₂ᵣ.val})).Elem
           ((Yₗ \ {y₂ₗ.val}) ∪ (Yᵣ \ {y₀ᵣ.val, y₁ᵣ.val})).Elem Z2 :=
  (S.submatrix (fun i => i.casesOn Sum.inl (Sum.inr ∘ mapX)) (fun j => j.casesOn (Sum.inl ∘ mapY) Sum.inr)).toMatrixUnionUnion

lemma matrix3sumComposition_alt2_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Sₗ.X := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Sₗ.X := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.mem3₁ᵣ⟩
    let _x₂ₗ : Sₗ.X := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.mem3₂ₗ⟩
    let _y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- break `Sₗ.B` and `Sᵣ.B` into submatrices
    let Aₗ := Sₗ.B.Aₗ_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Aₗ' := Sₗ.B.Aₗ'_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Sₗ.B.Dₗ_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ := Sₗ.B.D₀_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Sᵣ.B.Dᵣ_alt2 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ' := Sᵣ.B.Aᵣ'_alt2 x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Sᵣ.B.Aᵣ_alt2 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let S := matrix3sumComposition_alt2 Aₗ Aₗ' Dₗ D₀ Dᵣ Aᵣ' Aᵣ
    (matrix3sumComposition_alt2_mapped' S) = (matrix3sumComposition_curr Sₗ.B Sᵣ.B hXX hYY) := by
  sorry
  -- rfl -- fails

noncomputable def standardRepr3sumComposition_alt2 [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 :=
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  let Aₗ := Sₗ.B.Aₗ_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let Aₗ' := Sₗ.B.Aₗ'_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dₗ := Sₗ.B.Dₗ_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let D₀ := Sₗ.B.D₀_alt2 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dᵣ := Sᵣ.B.Dᵣ_alt2 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  let Aᵣ' := Sᵣ.B.Aᵣ'_alt2 x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
  let Aᵣ := Sᵣ.B.Aᵣ_alt2 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  let S := matrix3sumComposition_alt2 Aₗ Aₗ' Dₗ D₀ Dᵣ Aᵣ' Aᵣ
  ⟨
    (Sₗ.X \ {x₀ₗ.val, x₁ₗ.val}) ∪ (Sᵣ.X \ {x₂ᵣ.val}),
    (Sₗ.Y \ {y₂ₗ.val}) ∪ (Sᵣ.Y \ {y₀ᵣ.val, y₁ᵣ.val}),
    by
      rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
      exact
        ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
        ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
    matrix3sumComposition_alt2_mapped S,
    inferInstance,
    inferInstance,
  ⟩

lemma standardRepr3sumComposition_alt2_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    standardRepr3sumComposition_alt2 hXX hYY hXY hYX = standardRepr3sumComposition_curr hXX hYY hXY hYX := by
  sorry
  -- rfl -- fails

/-!
  This definition attempts to delegate the extraction of submatrices to the matroid (standard representation) level.
  However, definitional equality is preserved neither on the matrix nor on the matroid level.
  The issue is likely due to breaking `Aₗ` and `Aᵣ` into parts and re-gluing them.
  This stems from the handling of the sub-blocks of `D`.
-/

end Alt2


section Alt3

@[simp] private abbrev Set.drop1 (X : Set α) (x₀ : X) : Set α := X \ {x₀.val}
@[simp] private abbrev Set.drop2 (X : Set α) (x₀ x₁ : X) : Set α := X \ {x₀.val, x₁.val}
@[simp] private abbrev Set.drop3 (X : Set α) (x₀ x₁ x₂ : X) : Set α := X \ {x₀.val, x₁.val, x₂.val}

@[simp]
private abbrev mapX_alt3 [DecidableEq α] {X : Set α} {x₀ x₁ x₂ : X} [∀ x, Decidable (x ∈ X)] (i : X.drop1 x₂) :
    Fin 2 ⊕ (X.drop3 x₀ x₁ x₂) :=
  if hi₀ : i.val = x₀ then ◩0 else
  if hi₁ : i.val = x₁ then ◩1 else
  if hi : i.val ∈ X.drop3 x₀ x₁ x₂ then ◪⟨i, hi⟩ else
  (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim

@[simp]
private abbrev mapY_alt3 [DecidableEq α] {Y : Set α} {y₀ y₁ y₂ : Y} [∀ x, Decidable (x ∈ Y)] (j : Y.drop1 y₂) :
    (Y.drop3 y₀ y₁ y₂) ⊕ Fin 2 :=
  if hj₀ : j.val = y₀ then ◪0 else
  if hj₁ : j.val = y₁ then ◪1 else
  if hj : j.val ∈ Y.drop3 y₀ y₁ y₂ then ◩⟨j, hj⟩ else
  (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim

noncomputable def matrix3sumComposition_alt3 {F : Type} [Field F]
    [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (x₀ₗ x₁ₗ : Xₗ) (y₀ₗ y₁ₗ y₂ₗ : Yₗ)
    (x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ) (y₀ᵣ y₁ᵣ : Yᵣ)
    (Aₗ : Matrix (Xₗ.drop2 x₀ₗ x₁ₗ) (Yₗ.drop1 y₂ₗ) F)
    (Dₗ : Matrix (Fin 2) (Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ) F)
    (D₀ : Matrix (Fin 2) (Fin 2) F)
    (Dᵣ : Matrix (Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Fin 2) F)
    (Aᵣ : Matrix (Xᵣ.drop1 x₂ᵣ) (Yᵣ.drop2 y₀ᵣ y₁ᵣ) F) :
    Matrix ((Xₗ.drop2 x₀ₗ x₁ₗ) ⊕ (Xᵣ.drop1 x₂ᵣ))
           ((Yₗ.drop1 y₂ₗ) ⊕ (Yᵣ.drop2 y₀ᵣ y₁ᵣ)) F :=
  ⊞ Aₗ 0 ((⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX_alt3 mapY_alt3) Aᵣ

@[simp]
private abbrev Matrix.D₀_alt3 {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Fin 2) F :=
  !![B x₀ y₀, B x₀ y₁; B x₁ y₀, B x₁ y₁]

@[app_unexpander Matrix.D₀_alt3]
def Matrix.D₀_alt3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `D₀_alt3))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dₗ_alt3 {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 2) (Y.drop3 y₀ y₁ y₂).Elem F :=
  ![B x₀ ∘ Set.diff_subset.elem, B x₁ ∘ Set.diff_subset.elem]

@[app_unexpander Matrix.Dₗ_alt3]
def Matrix.Dₗ_alt3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Dₗ_alt3))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dᵣ_alt3 {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop3 x₀ x₁ x₂) (Fin 2) F :=
  Matrix.of (fun i => ![B (Set.diff_subset.elem i) y₀, B (Set.diff_subset.elem i) y₁])

@[app_unexpander Matrix.Dᵣ_alt3]
def Matrix.Dᵣ_alt3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Dᵣ_alt3))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aₗ_alt3 {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₂ : Y) :
    Matrix (X.drop2 x₀ x₁) (Y.drop1 y₂) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aₗ_alt3]
def Matrix.Aₗ_alt3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Aₗ_alt3))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aᵣ_alt3 {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop1 x₂) (Y.drop2 y₀ y₁) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aᵣ_alt3]
def Matrix.Aᵣ_alt3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `Aᵣ_alt3))
  | _ => throw ()

lemma matrix3sumComposition_alt3_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
    -- row membership
    let x₀ₗ : Sₗ.X := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₁ₗ : Sₗ.X := ⟨x₁, hXX.mem3₁ₗ⟩
    let _x₂ₗ : Sₗ.X := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₀ᵣ : Sᵣ.X := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ᵣ : Sᵣ.X := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ᵣ : Sᵣ.X := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Sₗ.Y := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₁ₗ : Sₗ.Y := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₂ₗ : Sₗ.Y := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₀ᵣ : Sᵣ.Y := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ᵣ : Sᵣ.Y := ⟨y₁, hYY.mem3₁ᵣ⟩
    let _y₂ᵣ : Sᵣ.Y := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- -- note: using `inter3all` to re-type row and column indices causes matrix dimensions to not get recognized as equal
    -- -- it seems that the issue stems from re-typed indices forgetting their assigned values, as the failing test below shows
    -- -- respective `x`s and `y`s as members of respective sets
    -- let ⟨⟨x₀ₗ, x₁ₗ, _x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    -- let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _y₂ᵣ⟩⟩ := hYY.inter3all
    -- -- have : x₀ₗ = ⟨x₀, hXX.mem3₀ₗ⟩ := by rfl -- fails
    -- extract submatrices
    let Aₗ := Sₗ.B.Aₗ_alt3 x₀ₗ x₁ₗ y₂ₗ
    let Dₗ := Sₗ.B.Dₗ_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ₗ := Sₗ.B.D₀_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Sᵣ.B.Dᵣ_alt3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Sᵣ.B.Aᵣ_alt3 x₂ᵣ y₀ᵣ y₁ᵣ
    (matrix3sumComposition_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ₗ Dᵣ Aᵣ) =
    (matrix3sumComposition_curr Sₗ.B Sᵣ.B hXX hYY) := by
  rfl

noncomputable def standardRepr3sumComposition_alt3 [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 :=
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, _x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _y₂ᵣ⟩⟩ := hYY.inter3all
    -- extract submatrices
    let Aₗ := Sₗ.B.Aₗ_alt3 x₀ₗ x₁ₗ y₂ₗ
    let Dₗ := Sₗ.B.Dₗ_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ₗ := Sₗ.B.D₀_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Sᵣ.B.Dᵣ_alt3 x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Sᵣ.B.Aᵣ_alt3 x₂ᵣ y₀ᵣ y₁ᵣ
  ⟨
    (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
    (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
    by
      rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
      exact
        ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
        ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
    (matrix3sumComposition_alt3 x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ₗ Dᵣ Aᵣ).toMatrixUnionUnion,
    inferInstance,
    inferInstance,
  ⟩

lemma standardRepr3sumComposition_alt3_eq_curr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    standardRepr3sumComposition_alt3 hXX hYY hXY hYX = standardRepr3sumComposition_curr hXX hYY hXY hYX := by
  rfl

/-!
  This definition delegates the extraction of submatrices to the matroid (standard representation) level.
  It gives definitionally equal constructions, and it should reduce the boilerplate in the implementation on the matrix level.
-/

end Alt3
