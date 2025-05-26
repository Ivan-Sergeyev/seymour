import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


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

@[simp]
private def Eq.inter3all (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : (Zₗ × Zₗ × Zₗ) × (Zᵣ × Zᵣ × Zᵣ) :=
  ⟨⟨⟨a₀, hZZ.mem3₀ₗ⟩, ⟨a₁, hZZ.mem3₁ₗ⟩, ⟨a₂, hZZ.mem3₂ₗ⟩⟩, ⟨⟨a₀, hZZ.mem3₀ᵣ⟩, ⟨a₁, hZZ.mem3₁ᵣ⟩, ⟨a₂, hZZ.mem3₂ᵣ⟩⟩⟩

@[app_unexpander Eq.inter3all]
def Eq.inter3all_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `inter3all))
  | _ => throw ()

end members_of_intersection


-- ## Internal API

/-- Remove a bundled element from a set. -/
@[simp]
private abbrev Set.drop1 (X : Set α) (x₀ : X) : Set α := X \ {x₀.val}

@[app_unexpander Set.drop1]
def Set.drop1_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop1))
  | _ => throw ()

/-- Remove two bundled elements from a set. -/
@[simp]
private abbrev Set.drop2 (X : Set α) (x₀ x₁ : X) : Set α := X \ {x₀.val, x₁.val}

@[app_unexpander Set.drop2]
def Set.drop2_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop2))
  | _ => throw ()

/-- Remove three bundled elements from a set. -/
@[simp]
private abbrev Set.drop3 (X : Set α) (x₀ x₁ x₂ : X) : Set α := X \ {x₀.val, x₁.val, x₂.val}

@[app_unexpander Set.drop3]
def Set.drop3_unexpand : Lean.PrettyPrinter.Unexpander
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

@[simp]
private abbrev mapX [DecidableEq α] {X : Set α} {x₀ x₁ x₂ : X} [∀ x, Decidable (x ∈ X)] (i : X.drop1 x₂) :
    Fin 2 ⊕ (X.drop3 x₀ x₁ x₂) :=
  if hi₀ : i.val = x₀ then ◩0 else
  if hi₁ : i.val = x₁ then ◩1 else
  if hi : i.val ∈ X.drop3 x₀ x₁ x₂ then ◪⟨i, hi⟩ else
  (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim

@[simp]
private abbrev mapY [DecidableEq α] {Y : Set α} {y₀ y₁ y₂ : Y} [∀ x, Decidable (x ∈ Y)] (j : Y.drop1 y₂) :
    (Y.drop3 y₀ y₁ y₂) ⊕ Fin 2 :=
  if hj₀ : j.val = y₀ then ◪0 else
  if hj₁ : j.val = y₁ then ◪1 else
  if hj : j.val ∈ Y.drop3 y₀ y₁ y₂ then ◩⟨j, hj⟩ else
  (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim


-- ## The 3-sum of matrices

/-- The 3-sum composition of matrices. -/
noncomputable def matrix3sumComposition [DecidableEq α] {F : Type} [Field F]
    {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (x₀ₗ x₁ₗ : Xₗ) (y₀ₗ y₁ₗ y₂ₗ : Yₗ)
    (x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ) (y₀ᵣ y₁ᵣ : Yᵣ)
    (Aₗ : Matrix (Xₗ.drop2 x₀ₗ x₁ₗ) (Yₗ.drop1 y₂ₗ) F)
    (Dₗ : Matrix (Fin 2) (Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ) F)
    (D₀ : Matrix (Fin 2) (Fin 2) F)
    (Dᵣ : Matrix (Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Fin 2) F)
    (Aᵣ : Matrix (Xᵣ.drop1 x₂ᵣ) (Yᵣ.drop2 y₀ᵣ y₁ᵣ) F) :
    Matrix ((Xₗ.drop2 x₀ₗ x₁ₗ) ⊕ (Xᵣ.drop1 x₂ᵣ)) ((Yₗ.drop1 y₂ₗ) ⊕ (Yᵣ.drop2 y₀ᵣ y₁ᵣ)) F :=
  ⊞ Aₗ 0 ((⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) Aᵣ

@[simp]
private abbrev Matrix.D₀ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Fin 2) F :=
  !![B x₀ y₀, B x₀ y₁; B x₁ y₀, B x₁ y₁]

@[app_unexpander Matrix.D₀]
def Matrix.D₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `D₀))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dₗ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 2) (Y.drop3 y₀ y₁ y₂).Elem F :=
  ![B x₀ ∘ Set.diff_subset.elem, B x₁ ∘ Set.diff_subset.elem]

@[app_unexpander Matrix.Dₗ]
def Matrix.Dₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Dₗ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Dᵣ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop3 x₀ x₁ x₂) (Fin 2) F :=
  Matrix.of (fun i => ![B (Set.diff_subset.elem i) y₀, B (Set.diff_subset.elem i) y₁])

@[app_unexpander Matrix.Dᵣ]
def Matrix.Dᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Dᵣ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aₗ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₂ : Y) :
    Matrix (X.drop2 x₀ x₁) (Y.drop1 y₂) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aₗ]
def Matrix.Aₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Aₗ))
  | _ => throw ()

@[simp]
private abbrev Matrix.Aᵣ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop1 x₂) (Y.drop2 y₀ y₁) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aᵣ]
def Matrix.Aᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Aᵣ))
  | _ => throw ()

noncomputable def standardRepr3sumComposition [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  -- extract submatrices
  let Aₗ := Sₗ.B.Aₗ x₀ₗ x₁ₗ y₂ₗ
  let Dₗ := Sₗ.B.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let D₀ := Sₗ.B.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dᵣ := Sᵣ.B.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  let Aᵣ := Sᵣ.B.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  ⟨
    ⟨
      (Sₗ.X.drop2 x₀ₗ x₁ₗ) ∪ (Sᵣ.X.drop1 x₂ᵣ),
      (Sₗ.Y.drop1 y₂ₗ) ∪ (Sᵣ.Y.drop2 y₀ᵣ y₁ᵣ),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      -- the standard representation matrix
      (matrix3sumComposition x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y₂ ∧ y₁ ≠ y₂))
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ D₀ = Sᵣ.B.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    -- `D₀` has the correct form
    ∧ (D₀ = 1 ∨ D₀ = !![1, 1; 0, 1])
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


-- ## Lemmas

@[simp] private abbrev matrix3x3unsigned₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
@[simp] private abbrev matrix3x3unsigned₁ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[simp] private abbrev matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, -1, 1; 1, 1, 0]
@[simp] private abbrev matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ := matrix3x3unsigned₁

@[simp]
private abbrev Matrix.submatrix3x3 {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q x₀ y₀, Q x₀ y₁, Q x₀ y₂;
    Q x₁ y₀, Q x₁ y₁, Q x₁ y₂;
    Q x₂ y₀, Q x₂ y₁, Q x₂ y₂]

@[app_unexpander Matrix.submatrix3x3]
def Matrix.submatrix3x3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `submatrix3x3))
  | _ => throw ()

private lemma submatrix3x3signed₀_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀) :
    |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₀ :=
  hQ ▸ |matrix3x3signed₀|.eta_fin_three

private lemma submatrix3x3signed₁_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁) :
    |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₁ :=
  hQ ▸ |matrix3x3signed₁|.eta_fin_three

private lemma Matrix.submatrix3x3_eq {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ =
    Q.submatrix
      (match · with
        | 0 => x₀
        | 1 => x₁
        | 2 => x₂)
      (match · with
        | 0 => y₀
        | 1 => y₁
        | 2 => y₂) := by
  ext
  rw [Matrix.submatrix_apply]
  split <;> split <;> rfl

private lemma Matrix.IsTotallyUnimodular.submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    (Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂).IsTotallyUnimodular := by
  rw [Matrix.submatrix3x3_eq]
  apply hQ.submatrix

-- we might need this, but later
private def Matrix.submatrix3x3mems {X Y : Set α} (Q : Matrix X Y ℚ)
    {x₀ x₁ x₂ y₀ y₁ y₂ : α} (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q ⟨x₀, hx₀⟩ ⟨y₂, hy₂⟩;
    Q ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q ⟨x₁, hx₁⟩ ⟨y₂, hy₂⟩;
    Q ⟨x₂, hx₂⟩ ⟨y₀, hy₀⟩, Q ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩, Q ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩]

@[app_unexpander Matrix.submatrix3x3mems]
def Matrix.submatrix3x3mems_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `submatrix3x3mems))
  | _ => throw ()

private lemma Matrix.submatrix3x3mems_eq {X Y : Set α} (Q : Matrix X Y ℚ)
    {x₀ x₁ x₂ y₀ y₁ y₂ : α} (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) :
    Q.submatrix3x3mems hx₀ hx₁ hx₂ hy₀ hy₁ hy₂ =
    Q.submatrix3x3 ⟨x₀, hx₀⟩ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₀, hy₀⟩ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ :=
  rfl


variable [DecidableEq α]

-- ## Canonical signing

/-- Proposition that `Q` is a TU canonical signing with `0` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀

/-- Proposition that `Q` is a TU canonical signing with `1` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
private def Matrix.IsTuCanonicallySignable₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₀

@[app_unexpander Matrix.IsTuCanonicallySignable₀]
def Matrix.IsTuCanonicallySignable₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicallySignable₀))
  | _ => throw ()

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
private def Matrix.IsTuCanonicallySignable₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x₂ ≠ x₀ ∧ x₂ ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y₂ ≠ y₀ ∧ y₂ ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₁

@[app_unexpander Matrix.IsTuCanonicallySignable₁]
def Matrix.IsTuCanonicallySignable₁_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `IsTuCanonicallySignable₁))
  | _ => throw ()

/-- Converts a matrix to the form of canonical TU signing, does not check assumptions. -/
@[simp]
private def Matrix.toCanonicalSigning {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix X Y ℚ :=
  let u : X → ℚ := (fun i : X =>
    if i = x₀ then Q x₀ y₀ * Q x₂ y₀ else
    if i = x₁ then Q x₀ y₀ * Q x₀ y₂ * Q x₁ y₂ * Q x₂ y₀ else
    if i = x₂ then 1 else
    1)
  let v : Y → ℚ := (fun j : Y =>
    if j = y₀ then Q x₂ y₀ else
    if j = y₁ then Q x₂ y₁ else
    if j = y₂ then Q x₀ y₀ * Q x₀ y₂ * Q x₂ y₀ else
    1)
  Q ⊡ u ⊗ v

@[app_unexpander Matrix.toCanonicalSigning]
def Matrix.toCanonicalSigning_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `toCanonicalSigning))
  | _ => throw ()

/-- Canonical signing of a TU matrix is TU. -/
private lemma Matrix.IsTotallyUnimodular.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTotallyUnimodular := by
  have hu : ∀ i : X,
    (fun i : X =>
      if i = x₀ then Q x₀ y₀ * Q x₂ y₀ else
      if i = x₁ then Q x₀ y₀ * Q x₀ y₂ * Q x₁ y₂ * Q x₂ y₀ else
      if i = x₂ then 1 else
      1) i ∈ SignType.cast.range
  · intro i
    if hix₀ : i = x₀ then
      simp_rw [hix₀, ite_true]
      apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix₁ : i = x₁ then
      simp_rw [hix₀, ite_false, hix₁, ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix₂ : i = x₂ then
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix₂, ite_true]
      exact one_in_signTypeCastRange
    else
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix₂, ite_false]
      exact one_in_signTypeCastRange
  have hv : ∀ j : Y,
    (fun j : Y =>
      if j = y₀ then Q x₂ y₀ else
      if j = y₁ then Q x₂ y₁ else
      if j = y₂ then Q x₀ y₀ * Q x₀ y₂ * Q x₂ y₀ else
      1) j ∈ SignType.cast.range
  · intro j
    if hjy₀ : j = y₀ then
      simp_rw [hjy₀, ite_true]
      apply hQ.apply
    else if hjy₁ : j = y₁ then
      simp_rw [hjy₀, ite_false, hjy₁, ite_true]
      apply hQ.apply
    else if hjy₂ : j = y₂ then
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy₂, ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy₂, ite_false]
      exact one_in_signTypeCastRange
  unfold Matrix.toCanonicalSigning
  exact Q.entryProd_outerProd_eq_mul_col_mul_row _ _ ▸ (hQ.mul_rows hu).mul_cols hv

private lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₀] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₀,
        hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hQ₀₁, hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d, hd⟩ := hQ3x3tu 3 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_three] at hd
  clear hQtu hQ3x3tu hQxy hQ₀₁ hQ₁₀ hQ₂₂ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
  cases hQ₀₀ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd

private lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y} (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁ := by
  obtain ⟨hQtu, ⟨hx₂, hx₁, hx₀⟩, ⟨hy₂, hy₁, hy₀⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₁] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₁, matrix3x3unsigned₁,
        hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d₁, hd₁⟩ := (hQ3x3tu.submatrix ![0, 2] ![0, 1]) 2 id id Function.injective_id Function.injective_id
  obtain ⟨d₂, hd₂⟩ := (hQ3x3tu.submatrix ![0, 1] ![1, 2]) 2 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_two] at hd₁ hd₂
  clear hQtu hQ3x3tu hQxy hQ₁₀ hQ₂₂ hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
  cases hQ₀₀ <;> cases hQ₀₁ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd₁ hd₂

private lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₀ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

private lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x₂ y₀ y₁ y₂) :
    (Q.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂).IsTuCanonicalSigning₁ x₀ x₁ x₂ y₀ y₁ y₂ :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂, hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

/-- `c₀` or `c₁` -/
@[simp] private abbrev Matrix._col {X Y : Set α} {a : α} (B : Matrix X Y ℚ) (y : Y) (i : (X \ {a}).Elem) : ℚ :=
  B (Set.diff_subset.elem i) y

@[app_unexpander Matrix._col]
def Matrix._col_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_col))
  | _ => throw ()

/-- `d₀` or `d₁` -/
@[simp] private abbrev Matrix._row {X Y : Set α} {a : α} (B : Matrix X Y ℚ) (x : X) (j : (Y \ {a}).Elem) : ℚ :=
  B x (Set.diff_subset.elem j)

@[app_unexpander Matrix._row]
def Matrix._row_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_row))
  | _ => throw ()

/-- `r₀` and `r₁` and `r₂` -/
private abbrev Matrix._rrr {X Y : Set α} (B' : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    let D₀ := |B'.submatrix3x3mems x₀.property x₁.property x₂.property y₀.property y₁.property y₂.property|
    (D₀ = matrix3x3unsigned₀ ∨ D₀ = matrix3x3unsigned₁) →
      (((Y \ {y₂.val}).Elem → ℚ) × ((Y \ {y₂.val}).Elem → ℚ) × ((Y \ {y₂.val}).Elem → ℚ)) :=
  fun hB' =>
    let B := B'.toCanonicalSigning x₀ x₁ x₂ y₀ y₁ y₂
    let d₀ : (Y \ {y₂.val}).Elem → ℚ := B._row x₀
    let d₁ : (Y \ {y₂.val}).Elem → ℚ := B._row x₁
    let D₀ := |B'.submatrix3x3mems x₀.property x₁.property x₂.property y₀.property y₁.property y₂.property|
    if hD₀₀ : D₀ = matrix3x3unsigned₀ then ⟨d₀, d₁, d₀ - d₁⟩ else
    if hD₀₁ : D₀ = matrix3x3unsigned₁ then ⟨d₀ - d₁, d₁, d₀⟩ else
    (False.elim (by
      simp only [D₀, hD₀₀, hD₀₁] at hB'
      exact hB'.casesOn id id))

@[app_unexpander Matrix._rrr]
def Matrix._rrr_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $B) => `($(B).$(Lean.mkIdent `_rrr))
  | _ => throw ()

-- lemma 15.a
set_option maxHeartbeats 300000 in
private lemma Matrix.IsTotallyUnimodular.signing_expansion₀ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B : Matrix X Y ℚ := Q.shortTableauPivot x₂ y₀
  let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₀) ↓y₁),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◩◪() else if hy₁ : y = y₁ then ◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).submatrix id e.symm
  · ext i j
    have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
    have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
    if hjy₀ : j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀]
    else if hjy₁ : j = y₁ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
      have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₀]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) (-1))
  have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 15.b
set_option maxHeartbeats 300000 in
private lemma Matrix.IsTotallyUnimodular.signing_expansion₁ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B := Q.shortTableauPivot x₂ y₁
  let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₁) ↓y₀),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◪() else if hy₁ : y = y₁ then ◩◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).submatrix id e.symm
  · ext i j
    have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
    have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
    if hjy₀ : j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else if hjy₁ : j = y₁ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
      have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₁]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
  have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 16.1
omit [DecidableEq α] in
private lemma Matrix.IsTotallyUnimodular.special_form_cols {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x₂ : X} {y₀ y₁ : Y} (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    ∀ i : X.drop1 x₂, ![c₀ i, c₁ i] ≠ ![1, -1] ∧ ![c₀ i, c₁ i] ≠ ![-1, 1] := by
  intro c₀ c₁ i
  constructor <;>
  · intro contr
    simp only [c₀, c₁] at contr
    have := congr_fun contr 0
    have := congr_fun contr 1
    have := hQ.det ![x₂, Set.diff_subset.elem i] ![y₀, y₁]
    simp_all [Matrix.det_fin_two]

-- lemma 16.2
private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_weak {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  sorry

private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_aux {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intros
  convert (hQ.signing_expansion_cols_weak hyy hQy₀ hQy₁ hQy).comp_cols
    (fun j : ((((((Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (◩◩◩·) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) ↓◪()) ↓◪()))
  aesop

private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
    let c₀ := Q._col y₀
    let c₁ := Q._col y₁
    let Q' := Q.Aᵣ x₂ y₀ y₁
    (Q' ◫ ▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ ▮0).IsTotallyUnimodular := by
  intros
  convert ((hQ.signing_expansion_cols_aux hyy hQy₀ hQy₁ hQy).mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 1) (-1)) 1) (-1)) 1) (-1)) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).fromCols_zero Unit
  aesop

-- Lemma 18.2's corollary
private lemma Matrix.IsTotallyUnimodular.signing_expansion_rows {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) {x₀ x₁ : X} {y₂ : Y} (hxx : x₀ ≠ x₁) (hQx₀ : Q x₀ y₂ = 1) (hQx₁ : Q x₁ y₂ = 1)
    (hQx : ∀ x : X, x.val ≠ x₀ ∧ x.val ≠ x₁ → Q x y₂ = 0) :
    let d₀ := Q._row x₀
    let d₁ := Q._row x₁
    let Q' := Q.Aₗ x₀ x₁ y₂
    (Q' ⊟ ▬d₀ ⊟ ▬(-d₀) ⊟ ▬d₁ ⊟ ▬(-d₁) ⊟ ▬(d₀ - d₁) ⊟ ▬(d₁ - d₀) ⊟ ▬0).IsTotallyUnimodular := by
  intros
  convert (hQ.transpose.signing_expansion_cols hxx hQx₀ hQx₁ hQx).transpose
  aesop

/-- Canonical signing of 3-sum constructed from TU signings of summands. -/
@[simp]
private noncomputable def matrix3sumCompositionCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    (Bₗ' : Matrix Xₗ Yₗ ℚ) (Bᵣ' : Matrix Xᵣ Yᵣ ℚ) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) :
    let ⟨⟨x₀ₗ, x₁ₗ, _⟩, ⟨_, _, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨_, _, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, _⟩⟩ := hYY.inter3all
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ⊕ Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ ⊕ Yᵣ.drop2 y₀ᵣ y₁ᵣ) ℚ :=
  -- respective `x`s and `y`s as members of respective sets
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  -- convert summands to canonical form
  let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
  let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
  -- pieces of the bottom left submatrix
  let D₀ₗ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
  let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
  let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
  -- the actual definition
  ⊞ (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ) 0 ((⊞ Dₗ D₀ₗ (Dᵣ * D₀ₗ⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ)

-- lemma 19.1
private lemma matrix3sumCompositionCanonicalSigning_D_eq {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- two just-constructed rows
    let ⟨r₀, r₁, _⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    ((⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY) = c₀ ⊗ r₀ + c₁ ⊗ r₁ :=
  sorry

-- lemma 19.2
private lemma matrix3sumCompositionCanonicalSigning_D_rows {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY
    -- three just-constructed rows
    let ⟨r₀, r₁, r₂⟩ := Bₗ'._rrr x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ hBₗ'
    -- the actual statement
    ∀ i, D i = r₀ ∨ D i = -r₀ ∨ D i = r₁ ∨ D i = -r₁ ∨ D i = r₂ ∨ D i = -r₂ ∨ D i = 0 :=
  sorry

-- lemma 19.3
private lemma matrix3sumCompositionCanonicalSigning_D_cols {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x₂ₗ : Xₗ := ⟨x₂, hXX.mem3₂ₗ⟩
    let x₂ᵣ : Xᵣ := ⟨x₂, hXX.mem3₂ᵣ⟩
    -- col membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y₂ₗ : Yₗ := ⟨y₂, hYY.mem3₂ₗ⟩
    let y₂ᵣ : Yᵣ := ⟨y₂, hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- final bottom left submatrix
    let D : Matrix (Xᵣ.drop1 x₂ᵣ) (Yₗ.drop1 y₂ₗ) ℚ := (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY
    -- special columns
    let c₀ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₀ᵣ
    let c₁ : (Xᵣ \ {x₂}).Elem → ℚ := Bᵣ._col y₁ᵣ
    -- the actual statement
    ∀ j, (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀ ∨ (D · j) = 0 :=
  sorry

-- lemma 19.5
private lemma matrix3sumCompositionCanonicalSigning_Aᵣ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bᵣ.D₀ x₀ᵣ x₁ᵣ y₀ᵣ y₁ᵣ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- the actual statement
    (Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ ◫ (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY).IsTotallyUnimodular :=
  sorry

-- lemma 19.7
private lemma matrix3sumCompositionCanonicalSigning_Aₗ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ
    -- pieces of the bottom left submatrix
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- the actual statement
    (Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ ⊟ (⊞ Dₗ D₀ (Dᵣ * D₀⁻¹ * Dₗ) Dᵣ).submatrix mapX mapY).IsTotallyUnimodular := by
  sorry


-- ## The 3-sum of matroids

lemma standardRepr3sumComposition_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x₂}) :=
  rfl

lemma standardRepr3sumComposition_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y₂}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
  rfl

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `Mₗ` and `Mᵣ`. -/
structure Matroid.Is3sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : Sₗ.X ∩ Sᵣ.X = {x₁, x₂, x₃}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₁, y₂, y₃}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr3sumComposition hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_X]
  apply Finite.Set.finite_union

@[simp]
lemma cast_1_from_Z2_to_Rat : ZMod.cast (1 : Z2) = (1 : ℚ) := by
  decide

@[simp]
lemma cast_Z2_nonneg (a : Z2) : (0 : ℚ) ≤ ZMod.cast a := by
  fin_cases a <;> decide

lemma matrix3sumComposition_hasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    [∀ x, Decidable (x ∈ Xₗ)] [∀ x, Decidable (x ∈ Xᵣ)] [∀ y, Decidable (y ∈ Yₗ)] [∀ y, Decidable (y ∈ Yᵣ)]
    {Bₗ : Matrix Xₗ Yₗ Z2} {Bᵣ : Matrix Xᵣ Yᵣ Z2}
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y₂}) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ)
    (hBₗ : Bₗ.HasTuSigning) (hBᵣ : Bᵣ.HasTuSigning) :
    -- respective `x`s and `y`s as members of respective sets
    let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
    let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
    -- extract submatrices
    let Aₗ := Bₗ.Aₗ x₀ₗ x₁ₗ y₂ₗ
    let Dₗ := Bₗ.Dₗ x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ
    let D₀ := Bₗ.D₀ x₀ₗ x₁ₗ y₀ₗ y₁ₗ
    let Dᵣ := Bᵣ.Dᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    let Aᵣ := Bᵣ.Aᵣ x₂ᵣ y₀ᵣ y₁ᵣ
    -- (matrix3sumComposition Bₗ Bᵣ hXX hYY).snd →
    -- TODO propagate the necessary assumption from `standardRepr3sumComposition.snd`
    (matrix3sumComposition x₀ₗ x₁ₗ y₀ₗ y₁ₗ y₂ₗ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ Aₗ Dₗ D₀ Dᵣ Aᵣ).HasTuSigning := by
  obtain ⟨Aₗ, hAₗ, hABₗ⟩ := hBₗ
  obtain ⟨Aᵣ, hAᵣ, hABᵣ⟩ := hBᵣ
  sorry

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) (hSS : (standardRepr3sumComposition hXX hYY hXY hYX).snd) :
    (standardRepr3sumComposition hXX hYY hXY hYX).fst.B.HasTuSigning := by
  -- TODO extract assumptions from `hSS` and plug them below
  obtain ⟨B, hB, hBBB⟩ := matrix3sumComposition_hasTuSigning hXX hYY hXY hYX hSₗ hSᵣ --hSS
  refine ⟨B.toMatrixUnionUnion, hB.toMatrixUnionUnion, fun i j => ?_⟩
  cases hi : i.toSum with
  | inl iₗ =>
    specialize hBBB ◩iₗ
    cases hj : j.toSum with
    | inl jₗ =>
      specialize hBBB ◩jₗ
      rwa [←hi, ←hj] at hBBB
    | inr jᵣ =>
      specialize hBBB ◪jᵣ
      rwa [←hi, ←hj] at hBBB
  | inr iᵣ =>
    specialize hBBB ◪iᵣ
    cases hj : j.toSum with
    | inl jₗ =>
      specialize hBBB ◩jₗ
      rwa [←hi, ←hj] at hBBB
    | inr jᵣ =>
      specialize hBBB ◪jᵣ
      rwa [←hi, ←hj] at hBBB

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, hMMM⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
  · exact hMMM
