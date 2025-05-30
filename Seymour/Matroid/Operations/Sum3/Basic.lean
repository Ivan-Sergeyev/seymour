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

@[simp] /-private-/ abbrev matrix3x3unsignedZ2₀ : Matrix (Fin 3) (Fin 3) Z2 := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
@[simp] /-private-/ abbrev matrix3x3unsignedZ2₁ : Matrix (Fin 3) (Fin 3) Z2 := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[simp] /-private-/ abbrev matrix3x3unsigned₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
@[simp] /-private-/ abbrev matrix3x3unsigned₁ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[simp] /-private-/ abbrev matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, -1, 1; 1, 1, 0]
@[simp] /-private-/ abbrev matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ := matrix3x3unsigned₁

@[simp]
/-private-/ abbrev Matrix.submatrix3x3 {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x₂ : X) (y₀ y₁ y₂ : Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![Q x₀ y₀, Q x₀ y₁, Q x₀ y₂;
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

-- # Experimental

structure matrix3sum (α : Type) [DecidableEq α] (F : Type) [Field F] where
    (Xₗ Yₗ Xᵣ Yᵣ : Set α)
    decmemXₗ : ∀ x, Decidable (x ∈ Xₗ)
    decmemXᵣ : ∀ x, Decidable (x ∈ Xᵣ)
    decmemYₗ : ∀ y, Decidable (y ∈ Yₗ)
    decmemYᵣ : ∀ y, Decidable (y ∈ Yᵣ)
    (x₀ₗ x₁ₗ x₂ₗ : Xₗ) (x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ)
    (y₀ₗ y₁ₗ y₂ₗ : Yₗ) (y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ)
    x₂ₗₗ : Xₗ.drop2 x₀ₗ x₁ₗ
    y₀ₗₗ : Yₗ.drop1 y₂ₗ
    y₁ₗₗ : Yₗ.drop1 y₂ₗ
    x₀ᵣᵣ : Xᵣ.drop1 x₂ᵣ
    x₁ᵣᵣ : Xᵣ.drop1 x₂ᵣ
    y₂ᵣᵣ : Yᵣ.drop2 y₀ᵣ y₁ᵣ
    Aₗ : Matrix (Xₗ.drop2 x₀ₗ x₁ₗ) (Yₗ.drop1 y₂ₗ) F
    Dₗ : Matrix (Fin 2) (Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ) F  -- Fin 2 represents x₀ₗ, x₁ₗ
    D₀ₗ : Matrix (Fin 2) (Fin 2) F  -- first Fin 2 represents x₀ₗ, x₁ₗ; second Fin 2 represents y₀ₗ, y₁ₗ
    D₀ᵣ : Matrix (Fin 2) (Fin 2) F  -- first Fin 2 represents x₀ᵣ, x₁ᵣ; second Fin 2 represents y₀ᵣ, y₁ᵣ
    Dᵣ : Matrix (Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Fin 2) F -- Fin 2 represents y₀ᵣ, y₁ᵣ
    Aᵣ : Matrix (Xᵣ.drop1 x₂ᵣ) (Yᵣ.drop2 y₀ᵣ y₁ᵣ) F

attribute [instance] matrix3sum.decmemXₗ
attribute [instance] matrix3sum.decmemYₗ
attribute [instance] matrix3sum.decmemXᵣ
attribute [instance] matrix3sum.decmemYᵣ

abbrev matrix3sum.XAₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Xₗ.drop2 S.x₀ₗ S.x₁ₗ
abbrev matrix3sum.YAₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Yₗ.drop1 S.y₂ₗ
abbrev matrix3sum.YDₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Yₗ.drop3 S.y₀ₗ S.y₁ₗ S.y₂ₗ
abbrev matrix3sum.XDᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Xᵣ.drop3 S.x₀ᵣ S.x₁ᵣ S.x₂ᵣ
abbrev matrix3sum.XAᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Xᵣ.drop1 S.x₂ᵣ
abbrev matrix3sum.YAᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Set α := S.Yᵣ.drop2 S.y₀ᵣ S.y₁ᵣ

abbrev matrix3sum.D₀ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (Fin 2) (Fin 2) F :=
  S.D₀ₗ

abbrev matrix3sum.Sₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (Fin 3) (Fin 3) F :=  -- first Fin 3 represents x₀ₗ, x₁ₗ, x₂ₗ; second Fin 3 represents y₀ₗ, y₁ₗ, y₂ₗ
  !![S.D₀ₗ 0 0, S.D₀ₗ 0 1, 1;
     S.D₀ₗ 1 0, S.D₀ₗ 1 1, 1;
     S.Aₗ S.x₂ₗₗ S.y₀ₗₗ, S.Aₗ S.x₂ₗₗ S.y₁ₗₗ, 0]

abbrev matrix3sum.Sᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (Fin 3) (Fin 3) F :=  -- first Fin 3 represents x₀ᵣ, x₁ᵣ, x₂ᵣ; second Fin 3 represents y₀ᵣ, y₁ᵣ, y₂ᵣ
  !![S.D₀ᵣ 0 0, S.D₀ᵣ 0 1, S.Aᵣ S.x₀ᵣᵣ S.y₂ᵣᵣ;
     S.D₀ᵣ 1 0, S.D₀ᵣ 1 1, S.Aᵣ S.x₁ᵣᵣ S.y₂ᵣᵣ;
     1, 1, 0]

abbrev matrix3sum.Dₗ₀ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (Fin 2) (S.Yₗ.drop1 S.y₂ₗ) F :=
  Matrix.of (fun i j =>
    if hj₀ : j.val = S.y₀ₗ then S.D₀ i 0
    else if hj₁ : j.val = S.y₁ₗ then S.D₀ i 1
    else if hj : j.val ∈ S.Yₗ.drop3 S.y₀ₗ S.y₁ₗ S.y₂ₗ then S.Dₗ i ⟨j, hj⟩
    else (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)

abbrev matrix3sum.Bₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :=
  ⊞ S.Aₗ 0 S.Dₗ₀ !![1; 1]

abbrev matrix3sum.Dᵣ₀ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (S.Xᵣ.drop1 S.x₂ᵣ) (Fin 2) F :=
  Matrix.of (fun i j =>
    if hi₀ : i.val = S.x₀ᵣ then S.D₀ 0 j
    else if hi₁ : i.val = S.x₁ᵣ then S.D₀ 1 j
    else if hi : i.val ∈ S.Xᵣ.drop3 S.x₀ᵣ S.x₁ᵣ S.x₂ᵣ then S.Dᵣ ⟨i, hi⟩ j
    else (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)

abbrev matrix3sum.Bᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :=
  ⊞ ![1, 1] 0 S.Dᵣ₀ S.Aᵣ

noncomputable abbrev matrix3sum.D [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix S.XAᵣ S.YAₗ F :=
  (⊞ S.Dₗ S.D₀ (S.Dᵣ * S.D₀⁻¹ * S.Dₗ) S.Dᵣ).submatrix mapX mapY

noncomputable def matrix3sum.Composition [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) :
    Matrix (S.XAₗ ⊕ S.XAᵣ) (S.YAₗ ⊕ S.YAᵣ) F :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ

def matrix3sum.fromStandardRepr [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) :
    matrix3sum α Z2 :=
  let ⟨⟨x₀ₗ, x₁ₗ, x₂ₗ⟩, ⟨x₀ᵣ, x₁ᵣ, x₂ᵣ⟩⟩ := hXX.inter3all
  let ⟨⟨y₀ₗ, y₁ₗ, y₂ₗ⟩, ⟨y₀ᵣ, y₁ᵣ, y₂ᵣ⟩⟩ := hYY.inter3all
  ⟨
    Sₗ.X, Sₗ.Y, Sᵣ.X, Sᵣ.Y,
    inferInstance,
    inferInstance,
    inferInstance,
    inferInstance,
    x₀ₗ, x₁ₗ, x₂ₗ, x₀ᵣ, x₁ᵣ, x₂ᵣ,
    y₀ₗ, y₁ₗ, y₂ₗ, y₀ᵣ, y₁ᵣ, y₂ᵣ,
    ⟨x₂, by sorry⟩,  -- todo: use that x₀ x₁ x₂ are distinct
    ⟨y₀, by sorry⟩,  -- todo: use that y₀ y₁ y₂ are distinct
    ⟨y₁, by sorry⟩,  -- todo: use that y₀ y₁ y₂ are distinct
    ⟨x₀, by sorry⟩,  -- todo: use that x₀ x₁ x₂ are distinct
    ⟨x₁, by sorry⟩,  -- todo: use that x₀ x₁ x₂ are distinct
    ⟨y₂, by sorry⟩,  -- todo: use that y₀ y₁ y₂ are distinct
    Sₗ.B.submatrix Set.diff_subset.elem Set.diff_subset.elem,
    ![Sₗ.B x₀ₗ ∘ Set.diff_subset.elem, Sₗ.B x₁ₗ ∘ Set.diff_subset.elem],
    !![Sₗ.B x₀ₗ y₀ₗ, Sₗ.B x₀ₗ y₁ₗ; Sₗ.B x₁ₗ y₀ₗ, Sₗ.B x₁ₗ y₁ₗ],
    !![Sᵣ.B x₀ᵣ y₀ᵣ, Sᵣ.B x₀ᵣ y₁ᵣ; Sᵣ.B x₁ᵣ y₀ᵣ, Sᵣ.B x₁ᵣ y₁ᵣ],
    Matrix.of (fun i => ![Sᵣ.B (Set.diff_subset.elem i) y₀ᵣ, Sᵣ.B (Set.diff_subset.elem i) y₁ᵣ]),
    Sᵣ.B.submatrix Set.diff_subset.elem Set.diff_subset.elem,
  ⟩

abbrev matrix3sum.HasTuSummandₗ [DecidableEq α] (S : matrix3sum α ℚ) : Prop :=
  S.Bₗ.IsTotallyUnimodular

abbrev matrix3sum.HasTuSummandᵣ [DecidableEq α] (S : matrix3sum α ℚ) : Prop :=
  S.Bᵣ.IsTotallyUnimodular

abbrev matrix3sum.HasDisjointDimensions [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.Xₗ ⫗ S.Yₗ ∧ S.Xₗ ⫗ S.Xᵣ ∧ S.Xₗ ⫗ S.Yᵣ ∧ S.Yₗ ⫗ S.Xᵣ ∧ S.Yₗ ⫗ S.Yᵣ ∧ S.Xᵣ ⫗ S.Yᵣ

abbrev matrix3sum.HasDistinctxₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.x₀ₗ ≠ S.x₁ₗ ∧ S.x₀ₗ ≠ S.x₂ₗ ∧ S.x₁ₗ ≠ S.x₂ₗ

abbrev matrix3sum.HasDistinctyₗ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.y₀ₗ ≠ S.y₁ₗ ∧ S.y₀ₗ ≠ S.y₂ₗ ∧ S.y₁ₗ ≠ S.y₂ₗ

abbrev matrix3sum.HasDistinctxᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.x₀ᵣ ≠ S.x₁ᵣ ∧ S.x₀ᵣ ≠ S.x₂ᵣ ∧ S.x₁ᵣ ≠ S.x₂ᵣ

abbrev matrix3sum.HasDistinctyᵣ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.y₀ᵣ ≠ S.y₁ᵣ ∧ S.y₀ᵣ ≠ S.y₂ᵣ ∧ S.y₁ᵣ ≠ S.y₂ᵣ

abbrev matrix3sum.HasEqD₀ [DecidableEq α] {F : Type} [Field F] (S : matrix3sum α F) : Prop :=
  S.D₀ₗ = S.D₀ᵣ

abbrev matrix3sum.HasFormInter₀ [DecidableEq α] (S : matrix3sum α Z2) : Prop :=
  S.Sₗ = matrix3x3unsignedZ2₀ ∧ S.Sᵣ = matrix3x3unsignedZ2₀

abbrev matrix3sum.HasFormInter₁ [DecidableEq α] (S : matrix3sum α Z2) : Prop :=
  S.Sₗ = matrix3x3unsignedZ2₁ ∧ S.Sᵣ = matrix3x3unsignedZ2₁

abbrev matrix3sum.HasFormInter₀₁ [DecidableEq α] (S : matrix3sum α Z2) : Prop :=
  S.HasFormInter₀ ∨ S.HasFormInter₁

abbrev matrix3sum_HasForm_y₂ₗ [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) : Prop :=
  Sₗ.B ⟨x₀, hXX.mem3₀ₗ⟩ ⟨y₂, hYY.mem3₂ₗ⟩ = 1 ∧ Sₗ.B ⟨x₁, hXX.mem3₁ₗ⟩ ⟨y₂, hYY.mem3₂ₗ⟩ = 1 ∧
    ∀ x : α, ∀ hx : x ∈ Sₗ.X, x ≠ x₀ ∧ x ≠ x₁ → Sₗ.B ⟨x, hx⟩ ⟨y₂, hYY.mem3₂ₗ⟩ = 0

abbrev matrix3sum_HasForm_x₂ᵣ [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x₂}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y₂}) : Prop :=
  Sᵣ.B ⟨x₂, hXX.mem3₂ᵣ⟩ ⟨y₀, hYY.mem3₀ᵣ⟩ = 1 ∧ Sᵣ.B ⟨x₂, hXX.mem3₂ᵣ⟩ ⟨y₁, hYY.mem3₁ᵣ⟩ = 1 ∧
    ∀ y : α, ∀ hy : y ∈ Sᵣ.Y, y ≠ y₀ ∧ y ≠ y₁ → Sᵣ.B ⟨x₂, hXX.mem3₂ᵣ⟩ ⟨y, hy⟩ = 0
