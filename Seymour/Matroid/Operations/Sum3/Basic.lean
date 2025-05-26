-- Do not shake the imports here!
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


variable {α : Type}

-- ## Interface between set theory and type theory

/-- Remove a bundled element from a set. -/
@[simp]
/-private-/ abbrev Set.drop1 (X : Set α) (x₀ : X) : Set α := X \ {x₀.val}

@[app_unexpander Set.drop1]
/-private-/ def Set.drop1_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop1))
  | _ => throw ()

/-- Remove two bundled elements from a set. -/
@[simp]
/-private-/ abbrev Set.drop2 (X : Set α) (x₀ x₁ : X) : Set α := X \ {x₀.val, x₁.val}

@[app_unexpander Set.drop2]
/-private-/ def Set.drop2_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop2))
  | _ => throw ()

/-- Remove three bundled elements from a set. -/
@[simp]
/-private-/ abbrev Set.drop3 (X : Set α) (x₀ x₁ x₂ : X) : Set α := X \ {x₀.val, x₁.val, x₂.val}

@[app_unexpander Set.drop3]
/-private-/ def Set.drop3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `drop3))
  | _ => throw ()

@[simp]
/-private-/ abbrev undrop1 {X : Set α} {x₀ : X} (i : X.drop1 x₀) : X :=
  ⟨i.val, i.property.left⟩

@[simp]
/-private-/ abbrev undrop2 {X : Set α} {x₀ x₁ : X} (i : X.drop2 x₀ x₁) : X :=
  ⟨i.val, i.property.left⟩

@[simp]
/-private-/ abbrev undrop3 {X : Set α} {x₀ x₁ x₂ : X} (i : X.drop3 x₀ x₁ x₂) : X :=
  ⟨i.val, i.property.left⟩

@[simp]
/-private-/ abbrev mapX [DecidableEq α] {X : Set α} {x₀ x₁ x₂ : X} [∀ x, Decidable (x ∈ X)] (i : X.drop1 x₂) :
    Fin 2 ⊕ X.drop3 x₀ x₁ x₂ :=
  if hi₀ : i.val = x₀ then ◩0 else
  if hi₁ : i.val = x₁ then ◩1 else
  if hi : i.val ∈ X.drop3 x₀ x₁ x₂ then ◪⟨i, hi⟩ else
  (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim

@[simp]
/-private-/ abbrev mapY [DecidableEq α] {Y : Set α} {y₀ y₁ y₂ : Y} [∀ x, Decidable (x ∈ Y)] (j : Y.drop1 y₂) :
    Y.drop3 y₀ y₁ y₂ ⊕ Fin 2 :=
  if hj₀ : j.val = y₀ then ◪0 else
  if hj₁ : j.val = y₁ then ◪1 else
  if hj : j.val ∈ Y.drop3 y₀ y₁ y₂ then ◩⟨j, hj⟩ else
  (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim


-- ## Specific 3×3 matrices

@[simp] /-private-/ abbrev matrix3x3unsigned₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
@[simp] /-private-/ abbrev matrix3x3unsigned₁ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[simp] /-private-/ abbrev matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, -1, 1; 1, 1, 0]
@[simp] /-private-/ abbrev matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ := matrix3x3unsigned₁

@[simp]
/-private-/ abbrev Matrix.submatrix3x3 {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q x₀ y₀, Q x₀ y₁, Q x₀ y₂;
    Q x₁ y₀, Q x₁ y₁, Q x₁ y₂;
    Q x₂ y₀, Q x₂ y₁, Q x₂ y₂]

@[app_unexpander Matrix.submatrix3x3]
/-private-/ def Matrix.submatrix3x3_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Q) => `($(Q).$(Lean.mkIdent `submatrix3x3))
  | _ => throw ()

/-private-/ lemma submatrix3x3signed₀_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₀) :
    |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₀ :=
  hQ ▸ |matrix3x3signed₀|.eta_fin_three

/-private-/ lemma submatrix3x3signed₁_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂ = matrix3x3signed₁) :
    |Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂| = matrix3x3unsigned₁ :=
  hQ ▸ |matrix3x3signed₁|.eta_fin_three

/-private-/ lemma Matrix.submatrix3x3_eq {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
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

/-private-/ lemma Matrix.IsTotallyUnimodular.submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    (Q.submatrix3x3 x₀ x₁ x₂ y₀ y₁ y₂).IsTotallyUnimodular := by
  rw [Matrix.submatrix3x3_eq]
  apply hQ.submatrix


-- ## Main definition

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


-- ## Parts of the two matrices

@[simp]
/-private-/ abbrev Matrix.D₀ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ : Y) :
    Matrix (Fin 2) (Fin 2) F :=
  !![B x₀ y₀, B x₀ y₁; B x₁ y₀, B x₁ y₁]

@[app_unexpander Matrix.D₀]
/-private-/ def Matrix.D₀_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `D₀))
  | _ => throw ()

@[simp]
/-private-/ abbrev Matrix.Dₗ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 2) (Y.drop3 y₀ y₁ y₂).Elem F :=
  ![B x₀ ∘ Set.diff_subset.elem, B x₁ ∘ Set.diff_subset.elem]

@[app_unexpander Matrix.Dₗ]
/-private-/ def Matrix.Dₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Dₗ))
  | _ => throw ()

@[simp]
/-private-/ abbrev Matrix.Dᵣ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop3 x₀ x₁ x₂) (Fin 2) F :=
  Matrix.of (fun i => ![B (Set.diff_subset.elem i) y₀, B (Set.diff_subset.elem i) y₁])

@[app_unexpander Matrix.Dᵣ]
/-private-/ def Matrix.Dᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Dᵣ))
  | _ => throw ()

@[simp]
/-private-/ abbrev Matrix.Aₗ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₀ x₁ : X) (y₂ : Y) :
    Matrix (X.drop2 x₀ x₁) (Y.drop1 y₂) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aₗ]
/-private-/ def Matrix.Aₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Aₗ))
  | _ => throw ()

@[simp]
/-private-/ abbrev Matrix.Aᵣ {F : Type} {X Y : Set α} (B : Matrix X Y F) (x₂ : X) (y₀ y₁ : Y) :
    Matrix (X.drop1 x₂) (Y.drop2 y₀ y₁) F :=
  B.submatrix Set.diff_subset.elem Set.diff_subset.elem

@[app_unexpander Matrix.Aᵣ]
/-private-/ def Matrix.Aᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `Aᵣ))
  | _ => throw ()


-- ## Elements of the triplet intersection as elements of respective types

variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

/-private-/ lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ₗ]
/-private-/ def Eq.mem3₀ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ₗ))
  | _ => throw ()

/-private-/ lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ₗ]
/-private-/ def Eq.mem3₁ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ₗ))
  | _ => throw ()

/-private-/ lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

@[app_unexpander Eq.mem3₂ₗ]
/-private-/ def Eq.mem3₂ₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ₗ))
  | _ => throw ()

/-private-/ lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

@[app_unexpander Eq.mem3₀ᵣ]
/-private-/ def Eq.mem3₀ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₀ᵣ))
  | _ => throw ()

/-private-/ lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

@[app_unexpander Eq.mem3₁ᵣ]
/-private-/ def Eq.mem3₁ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₁ᵣ))
  | _ => throw ()

/-private-/ lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

@[app_unexpander Eq.mem3₂ᵣ]
/-private-/ def Eq.mem3₂ᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `mem3₂ᵣ))
  | _ => throw ()

@[simp]
/-private-/ def Eq.inter3all (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : (Zₗ × Zₗ × Zₗ) × (Zᵣ × Zᵣ × Zᵣ) :=
  ⟨⟨⟨a₀, hZZ.mem3₀ₗ⟩, ⟨a₁, hZZ.mem3₁ₗ⟩, ⟨a₂, hZZ.mem3₂ₗ⟩⟩, ⟨⟨a₀, hZZ.mem3₀ᵣ⟩, ⟨a₁, hZZ.mem3₁ᵣ⟩, ⟨a₂, hZZ.mem3₂ᵣ⟩⟩⟩

@[app_unexpander Eq.inter3all]
/-private-/ def Eq.inter3all_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `($(e).$(Lean.mkIdent `inter3all))
  | _ => throw ()
