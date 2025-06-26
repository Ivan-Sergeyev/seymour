import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


/-

Basic approach:
- matrix level
- standard repr level
- matroid level


New unified design:
`structure`s now include correctness, like `StandardRepr`


`StandardRepr` = standard representation (matrix)
- data = `Matrix` + correctness (disjoint dimensions)
- API def -> conversion to `Matroid`

- works well for composition operations: result of `A + B`
- on matroid level, we have Prop: `M = A + B` (`=` highlighted)


Experiment
1. all sums on matrix level -> structure similar to `StandardRepr` / `MatrixSum3`
2. look at standardrepr level, see a) how 1. changes things, b) if the same approach works
3. look at matroid level, see a) how 1. & 2. changes things, b) if the same approach works
4. consider wrappers for highest level

-/


/-! # 1-sum -/

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices. -/
abbrev matrix1sumComposition {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

/-- `StandardRepr`-level 1-sum of two matroids.
    It checks that everything is disjoint (returned as `.snd` of the output). -/
def standardRepr1sumComposition {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      (matrix1sumComposition Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  ⟩

/-- Binary matroid `M` is a result of 1-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop` but treat it as a predicate. -/
structure Matroid.Is1sumOf {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr1sumComposition hXY hYX).fst = S
  IsValid : (standardRepr1sumComposition hXY hYX).snd


/-! # 2-sum -/

/-! ## Matrix level -/

structure MatrixSum2 (Xₗ Yₗ Xᵣ Yᵣ R : Type) [Zero R] where
  Aₗ : Matrix (Xₗ) (Yₗ ⊕ Unit) R
  r  : Yₗ ⊕ Unit → R
  Aᵣ : Matrix (Unit ⊕ Xᵣ) (Yᵣ) R
  c  : Unit ⊕ Xᵣ → R
  -- hr : r ≠ 0
  -- hc : c ≠ 0

def MatrixSum2.matrix {Xₗ Yₗ Xᵣ Yᵣ R : Type} [Semiring R] (S : MatrixSum2 Xₗ Yₗ Xᵣ Yᵣ R) :=
  ⊞ S.Aₗ 0 (S.c ⊗ S.r) S.Aᵣ

/-- Constructs 2-sum from summands in block form. -/
def MatrixSum2.fromBlockSummands {Xₗ Yₗ Xᵣ Yᵣ R : Type} [Zero R]
    (Bₗ : Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Unit) R) (Bᵣ : Matrix (Unit ⊕ Xᵣ) (Unit ⊕ Yᵣ) R)
    -- (hBₗ : Bₗ.toRows₂ 0 ≠ 0) (hBᵣ : (Bᵣ.toCols₁ · 0) ≠ 0)
    :
    MatrixSum2 Xₗ Yₗ Xᵣ Yᵣ R where
  Aₗ := Bₗ.toRows₁
  r  := Bₗ.toRows₂ 0
  Aᵣ := Bᵣ.toCols₂
  c  := (Bᵣ.toCols₁ · 0)
  -- hr := hBₗ
  -- hc := hBᵣ

/-- Reconstructs the left summand from the matrix 2-sum structure. -/
private abbrev MatrixSum2.Bₗ {Xₗ Yₗ Xᵣ Yᵣ R : Type} [Zero R] (S : MatrixSum2 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Unit) R :=
  S.Aₗ ⊟ ▬S.r

@[app_unexpander MatrixSum2.Bₗ]
private def MatrixSum2.Bₗ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Bₗ))
  | _ => throw ()

/-- Reconstructs the right summand from the matrix 2-sum structure. -/
private abbrev MatrixSum2.Bᵣ {Xₗ Yₗ Xᵣ Yᵣ R : Type} [Zero R] [One R] (S : MatrixSum2 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Unit ⊕ Xᵣ) (Unit ⊕ Yᵣ) R :=
  ▮S.c ◫ S.Aᵣ

@[app_unexpander MatrixSum2.Bᵣ]
private def MatrixSum2.Bᵣ_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `Bᵣ))
  | _ => throw ()

-- lemma : MatrixSum2.fromBlockSummands S.Bₗ S.Bᵣ = S


/-! ## Standard representation level -/

def Matrix.toBlockSummandₗ {α : Type} {Xₗ Yₗ : Set α} {R : Type} (Bₗ : Matrix Xₗ Yₗ R) (xₗ : Xₗ) (yₗ : Yₗ) :
    Matrix ((Xₗ \ {xₗ.val}).Elem ⊕ Unit) ((Yₗ \ {yₗ.val}).Elem ⊕ Unit) R :=
  Bₗ.submatrix
    (·.casesOn (fun i => ⟨i.val, i.property.left⟩) ↓xₗ)
    (·.casesOn (fun j => ⟨j.val, j.property.left⟩) ↓yₗ)

def Matrix.toBlockSummandᵣ {α : Type} {Xᵣ Yᵣ : Set α} {R : Type} (Bᵣ : Matrix Xᵣ Yᵣ R) (xᵣ : Xᵣ) (yᵣ : Yᵣ) :
    Matrix (Unit ⊕ (Xᵣ \ {xᵣ.val}).Elem) (Unit ⊕ (Yᵣ \ {yᵣ.val}).Elem) R :=
  Bᵣ.submatrix
    (·.casesOn ↓xᵣ (fun i => ⟨i.val, i.property.left⟩))
    (·.casesOn ↓yᵣ (fun j => ⟨j.val, j.property.left⟩))

structure StandardReprSum2 (α β R : Type) [DecidableEq α] [DecidableEq β] [Zero R] where
  Sₗ : StandardRepr α R
  Sᵣ : StandardRepr β R
  xₗ : Sₗ.X -- becomes `r`
  yₗ : Sₗ.Y -- shows how `c` aligns with columns of `Sₗ.B`
  xᵣ : Sᵣ.X -- shows how `r` aligns with rows of `Sᵣ.B`
  yᵣ : Sᵣ.Y -- becomes `c`
  -- assumptions
  hr : Sₗ.B xₗ ≠ 0
  hc : (Sᵣ.B · yᵣ) ≠ 0

def map2_fwd {α : Type} [DecidableEq α] {Z : Set α} (z : Z) (i : (Z \ {z.val}).Elem ⊕ Unit) : Z :=
  i.casesOn (fun i => ⟨i.val, i.property.left⟩) ↓z

def map2_bwd {α : Type} [DecidableEq α] {Z : Set α} (z : Z) (i : Z) : (Z \ {z.val}).Elem ⊕ Unit :=
  if hiz : i = z.val then ◪0 else ◩⟨i.val, ⟨i.property, hiz⟩⟩

def StandardReprSum2.toMatrixSum2 {α β R : Type} [DecidableEq α] [DecidableEq β] [Semiring R] (S : StandardReprSum2 α β R) :
    MatrixSum2 (S.Sₗ.X \ {S.xₗ.val}).Elem (S.Sₗ.Y \ {S.yₗ.val}).Elem (S.Sᵣ.X \ {S.xᵣ.val}).Elem (S.Sᵣ.Y \ {S.yᵣ.val}).Elem R :=
  MatrixSum2.fromBlockSummands (S.Sₗ.B.toBlockSummandₗ S.xₗ S.yₗ) (S.Sᵣ.B.toBlockSummandᵣ S.xᵣ S.yᵣ)
  -- let Bₗ := S.Sₗ.B.toBlockSummandₗ S.xₗ S.yₗ
  -- let Bᵣ := S.Sᵣ.B.toBlockSummandᵣ S.xᵣ S.yᵣ
  -- have hBₗ : Bₗ.toRows₂ 0 ≠ 0 := by
  --   unfold Matrix.toRows₂
  --   have h : (fun j => Bₗ ◪0 j) ≠ 0 := by
  --     have := S.hr
  --     have : Function.Surjective (map2_fwd S.xₗ) := sorry
  --     -- have : (Sₗ.B xₗ (·.casesOn (fun i => ⟨i.val, i.property.left⟩) ↓yₗ)) ≠ 0 := sorry
  --     -- have hh :
  --     -- unfold Bₗ Matrix.toBlockSummandₗ

  --     -- simp
  --     -- simp at this
  --     -- exact this

  --     sorry
  --   exact h
  -- have hBᵣ : (Bᵣ.toCols₁ · 0) ≠ 0 := sorry

def Matrix.toDropUnionDrop {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A :
      Matrix
        ((Xₗ \ {xₗ.val}) ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
        ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
        R
    ) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem R :=
  A.submatrix
    (fun i : (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem =>
      if hi₂ₗ : i.val = x₂ₗ then ◩◪0 else
      if hiXₗ : i.val ∈ Xₗ \ {xₗ.val} then ◩◩⟨i, hiXₗ⟩ else
      if hi₀ᵣ : i.val = x₀ᵣ then ◪◩0 else
      if hi₁ᵣ : i.val = x₁ᵣ then ◪◩1 else
      if hiXᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then ◪◪⟨i, hiXᵣ⟩ else
      False.elim (i.property.elim ↓(by simp_all) ↓(by simp_all)))
    (fun j : (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem =>
      if hj₀ₗ : j.val = y₀ₗ then ◩◪0 else
      if hj₁ₗ : j.val = y₁ₗ then ◩◪1 else
      if hjYₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then ◩◩⟨j, hjYₗ⟩ else
      if hj₂ᵣ : j.val = y₂ᵣ then ◪◩0 else
      if hjYᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then ◪◪⟨j, hjYᵣ⟩ else
      False.elim (j.property.elim ↓(by simp_all) ↓(by simp_all)))

def StandardReprSum2.standardRepr {α β R : Type} [DecidableEq α] [DecidableEq β] [Semiring R]
    (S : StandardReprSum2 α β R) : StandardRepr (α ⊕ β) R where
  X := (Sum.inl '' (S.Sₗ.X \ {S.xₗ.val})) ∪ (Sum.inr '' S.Sᵣ.X)
  Y := (Sum.inl '' S.Sₗ.Y) ∪ (Sum.inr '' (S.Sᵣ.Y \ {S.yᵣ.val}))
  hXY := by
    rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left, and_assoc]
    exact ⟨
      (Set.disjoint_image_iff Sum.inl_injective).← S.Sₗ.hXY.disjoint_sdiff_left,
      Set.disjoint_image_image ↓↓↓↓Sum.inr_ne_inl,
      Set.disjoint_image_image ↓↓↓↓Sum.inl_ne_inr,
      (Set.disjoint_image_iff Sum.inr_injective).← S.Sᵣ.hXY.disjoint_sdiff_right⟩
  B := S.toMatrixSum2.matrix
  decmemX := sorry -- inferInstance
  decmemY := sorry -- inferInstance


/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrix2sumComposition {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 (c ⊗ r) Aᵣ

/-- `StandardRepr`-level 2-sum of two matroids.
    The second part checks legitimacy: the ground sets of `Mₗ` and `Mᵣ` are disjoint except for the element `a ∈ Mₗ.X ∩ Mᵣ.Y`,
    and the bottom-most row of `Mₗ` and the left-most column of `Mᵣ` are each nonzero vectors. -/
def standardRepr2sumComposition {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      (Sₗ.X \ {a}) ∪ Sᵣ.X,
      Sₗ.Y ∪ (Sᵣ.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_sdiff_singleton ha, Sᵣ.hXY.disjoint_sdiff_right⟩⟩,
      (matrix2sumComposition (Sₗ.B.dropRow a) (Sₗ.B.interRow ha) (Sᵣ.B.dropCol a) (Sᵣ.B.interCol ha)).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y) ∧ (Sₗ.B.interRow ha ≠ 0 ∧ Sᵣ.B.interCol ha ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop` but treat it as a predicate. -/
structure Matroid.Is2sumOf {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  a : α
  ha : Sₗ.X ∩ Sᵣ.Y = {a}
  hXY : Sᵣ.X ⫗ Sₗ.Y
  IsSum : (standardRepr2sumComposition ha hXY).fst = S
  IsValid : (standardRepr2sumComposition ha hXY).snd


/-! # 3-sum -/





/-- Structural data of 3-sum of matrices. -/
structure MatrixSum3 (Xₗ Yₗ Xᵣ Yᵣ : Type) (R : Type) where
  Aₗ  : Matrix (Xₗ ⊕ Unit) (Yₗ ⊕ Fin 2) R
  Dₗ  : Matrix (Fin 2) Yₗ R
  D₀ₗ : Matrix (Fin 2) (Fin 2) R
  D₀ᵣ : Matrix (Fin 2) (Fin 2) R
  Dᵣ  : Matrix Xᵣ (Fin 2) R
  Aᵣ  : Matrix (Fin 2 ⊕ Xᵣ) (Unit ⊕ Yᵣ) R

-- MatrixSum3.IsCanonicalSigning -> ...

/-- The bottom-left block of 3-sum. -/
noncomputable abbrev MatrixSum3.D {Xₗ Yₗ Xᵣ Yᵣ R : Type} [CommRing R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix (Fin 2 ⊕ Xᵣ) (Yₗ ⊕ Fin 2) R :=
  ⊞ S.Dₗ S.D₀ₗ (S.Dᵣ * S.D₀ₗ⁻¹ * S.Dₗ) S.Dᵣ

/-- The resulting matrix of 3-sum. -/
noncomputable def MatrixSum3.matrix {Xₗ Yₗ Xᵣ Yᵣ R : Type} [CommRing R] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ R) :
    Matrix ((Xₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ)) ((Yₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ)) R :=
  ⊞ S.Aₗ 0 S.D S.Aᵣ

def standardReprMatrixSum3 {α : Type} [DecidableEq α] (Sₗ Sᵣ : StandardRepr α Z2)
    (x₀ₗ x₁ₗ x₂ₗ : Sₗ.X) (y₀ₗ y₁ₗ y₂ₗ : Sₗ.Y) (x₀ᵣ x₁ᵣ x₂ᵣ : Sᵣ.X) (y₀ᵣ y₁ᵣ y₂ᵣ : Sᵣ.Y) :
    MatrixSum3 (Sₗ.X.drop3 x₀ₗ x₁ₗ x₂ₗ) (Sₗ.Y.drop3 y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.X.drop3 x₀ᵣ x₁ᵣ x₂ᵣ) (Sᵣ.Y.drop3 y₀ᵣ y₁ᵣ y₂ᵣ) Z2 :=
  MatrixSum3.fromBlockSummands (Sₗ.B.toBlockSummandₗ x₀ₗ x₁ₗ x₂ₗ y₀ₗ y₁ₗ y₂ₗ) (Sᵣ.B.toBlockSummandᵣ x₀ᵣ x₁ᵣ x₂ᵣ y₀ᵣ y₁ᵣ y₂ᵣ)

def Matrix.toDropUnionDrop {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {R : Type}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    {x₀ₗ x₁ₗ x₂ₗ : Xₗ} {y₀ₗ y₁ₗ y₂ₗ : Yₗ} {x₀ᵣ x₁ᵣ x₂ᵣ : Xᵣ} {y₀ᵣ y₁ᵣ y₂ᵣ : Yᵣ}
    (A :
      Matrix
        ((Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ ⊕ Unit) ⊕ (Fin 2 ⊕ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ))
        ((Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ ⊕ Fin 2) ⊕ (Unit ⊕ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ))
        R
    ) :
    Matrix (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem R :=
  A.submatrix
    (fun i : (Xₗ.drop2 x₀ₗ x₁ₗ ∪ Xᵣ.drop1 x₂ᵣ).Elem =>
      if hi₂ₗ : i.val = x₂ₗ then ◩◪0 else
      if hiXₗ : i.val ∈ Xₗ.drop3 x₀ₗ x₁ₗ x₂ₗ then ◩◩⟨i, hiXₗ⟩ else
      if hi₀ᵣ : i.val = x₀ᵣ then ◪◩0 else
      if hi₁ᵣ : i.val = x₁ᵣ then ◪◩1 else
      if hiXᵣ : i.val ∈ Xᵣ.drop3 x₀ᵣ x₁ᵣ x₂ᵣ then ◪◪⟨i, hiXᵣ⟩ else
      False.elim (i.property.elim ↓(by simp_all) ↓(by simp_all)))
    (fun j : (Yₗ.drop1 y₂ₗ ∪ Yᵣ.drop2 y₀ᵣ y₁ᵣ).Elem =>
      if hj₀ₗ : j.val = y₀ₗ then ◩◪0 else
      if hj₁ₗ : j.val = y₁ₗ then ◩◪1 else
      if hjYₗ : j.val ∈ Yₗ.drop3 y₀ₗ y₁ₗ y₂ₗ then ◩◩⟨j, hjYₗ⟩ else
      if hj₂ᵣ : j.val = y₂ᵣ then ◪◩0 else
      if hjYᵣ : j.val ∈ Yᵣ.drop3 y₀ᵣ y₁ᵣ y₂ᵣ then ◪◪⟨j, hjYᵣ⟩ else
      False.elim (j.property.elim ↓(by simp_all) ↓(by simp_all)))


/-! ## The 3-sum of standard representations -/

noncomputable def standardRepr3sumComposition {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x₂ y₀ y₁ y₂ : α}
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

/-- Binary matroid `M` is a result of 3-summing `Mₗ` and `Mᵣ` in some way. Not a `Prop`, but treat it as a predicate. -/
structure Matroid.Is3sumOf {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
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
