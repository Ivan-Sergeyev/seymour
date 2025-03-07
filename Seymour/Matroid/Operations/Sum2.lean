import Seymour.Matrix.Pivoting
import Seymour.Matrix.TotalUnimodularityViolation
import Seymour.Matroid.Notions.Regularity


variable {α : Type} [DecidableEq α]

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrix2sumComposition {β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

/-- `StandardRepr`-level 2-sum of two matroids.
    The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
    and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def standardRepr2sumComposition {a : α} {S₁ S₂ : StandardRepr α Z2} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
    StandardRepr α Z2 × Prop :=
  let A₁ : Matrix (S₁.X \ {a}).Elem S₁.Y.Elem Z2 := S₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  let A₂ : Matrix S₂.X.Elem (S₂.Y \ {a}).Elem Z2 := (S₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  let x : S₁.Y.Elem → Z2 := S₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
  let y : S₂.X.Elem → Z2 := (S₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
  ⟨
    ⟨
      (S₁.X \ {a}) ∪ S₂.X,
      S₁.Y ∪ (S₂.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨S₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_inter_both_wo ha, S₂.hXY.disjoint_sdiff_right⟩⟩,
      (matrix2sumComposition A₁ x A₂ y).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (S₁.X ⫗ S₂.X ∧ S₁.Y ⫗ S₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
structure Matroid.Is2sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  S : StandardRepr α Z2
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  hS₁ : Finite S₁.X
  hS₂ : Finite S₂.X
  hM : S.toMatroid = M
  hM₁ : S₁.toMatroid = M₁
  hM₂ : S₂.toMatroid = M₂
  a : α
  ha : S₁.X ∩ S₂.Y = {a}
  hXY : S₂.X ⫗ S₁.Y
  IsSum : (standardRepr2sumComposition ha hXY).fst = S
  IsValid : (standardRepr2sumComposition ha hXY).snd

instance Matroid.Is2sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

infix:63 " ⊟ " => Matrix.fromRows
infix:63 " ◫ " => Matrix.fromCols
notation:64 "▬"r:81 => Matrix.row Unit r
notation:64 "▮"c:81 => Matrix.col Unit c

lemma lemma8 {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ} {k : ℕ}
    (hk : 2 ≤ k) (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular)
    (hAxAy : (matrix2sumComposition A₁ x A₂ y).MinimumViolationSizeIs k.succ) :
    ∃ A₁' : Matrix X₁ Y₁ ℚ, ∃ x' : Y₁ → ℚ, ∃ A₂' : Matrix X₂ Y₂ ℚ, ∃ y' : X₂ → ℚ,
      (A₁' ⊟ ▬x').IsTotallyUnimodular ∧
      (▮y' ◫ A₂').IsTotallyUnimodular ∧
      (matrix2sumComposition A₁' x' A₂' y').MinimumViolationSizeIs k := by
  obtain ⟨hA, hA'⟩ := hAxAy
  push_neg at hA'
  obtain ⟨f, g, hf, hg, hAfg⟩ := hA'
  -- first paragraph
  obtain ⟨i₁, x₁, hix₁⟩ : ∃ i₁ : Fin k.succ, ∃ x₁ : X₁, f i₁ = ◩x₁
  · sorry -- because `D ◫ A₂` is TU
  obtain ⟨i₂, x₂, hix₂⟩ : ∃ i₂ : Fin k.succ, ∃ x₂ : X₂, f i₂ = ◪x₂
  · sorry -- because `A₁ ◫ 0` is TU
  obtain ⟨j₁, y₁, hjy₁⟩ : ∃ j₁ : Fin k.succ, ∃ y₁ : Y₁, g j₁ = ◩y₁
  · sorry -- because `0 ⊟ A₂` is TU
  obtain ⟨j₂, y₂, hjy₂⟩ : ∃ j₂ : Fin k.succ, ∃ y₂ : Y₂, g j₂ = ◪y₂
  · sorry -- because `A₁ ⊟ D` is TU
  -- second paragraph
  obtain ⟨j₀, y₀, hyj₀⟩ : ∃ j₀ : Fin k.succ, ∃ y₀ : Y₁, g j₀ = ◩y₀ ∧ A₁ x₁ y₀ ≠ 0
  · sorry -- because the `x₁` row cannot be all `0`s
  -- third paragraph
  let B' := (matrix2sumComposition A₁ x A₂ y).shortTableauPivot ◩x₁ ◩y₀
  have hB' : B' = matrix2sumComposition B'.toBlocks₁₁ x B'.toBlocks₂₂ y -- TODO modify `x` and `y` to make it hold
  · sorry
  use B'.toBlocks₁₁, x, B'.toBlocks₂₂, y -- TODO the same modified `x` and `y` here
  -- first bullet
  have B'_toCols₁_TU : B'.toCols₁.IsTotallyUnimodular
  · sorry -- follows from `hAx` using `Matrix.IsTotallyUnimodular.shortTableauPivot`
  -- second bullet
  have eq_A₂ : B'.toBlocks₂₂ = A₂
  · sorry
  -- TODO thirt bullet
  -- fourth bullet
  have B'_toRows₂_TU : B'.toRows₂.IsTotallyUnimodular
  · rw [hB', eq_A₂]
    show ((fun i j => y i * x j) ◫ A₂).IsTotallyUnimodular
    -- TODO utilize `hAy` here
    sorry
  -- TODO fifth bullet
  -- TODO sixth bullet
  -- conclusion
  constructor
  · sorry -- follows from `B'_toCols₁_TU`
  constructor
  · sorry -- follows from `B'_toRows₂_TU`
  constructor
  · sorry -- missing in the write-up
  · sorry -- the sixth bullet will go here

lemma matrix2sumComposition_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hA₁ : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hA₂ : (▮y ◫ A₂).IsTotallyUnimodular) :
    (matrix2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_none_minimumViolationSizeIs]
  intro k
  cases k with
  | zero => sorry -- 0x0 should be trivial
  | succ m =>
    cases m with
    | zero => sorry -- 1x1 should be trivial
    | succ n =>
      induction n generalizing A₁ A₂ x y with
      | zero => sorry -- 2x2 requires a bit of work
      | succ k ih =>
        intro contr
        obtain ⟨_, _, _, _, hA₁', hA₂', result⟩ := lemma8 (Nat.le_add_left 2 k) hA₁ hA₂ contr
        exact ih hA₁' hA₂' result

lemma standardRepr2sumComposition_B {S₁ S₂ : StandardRepr α Z2} {a : α} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
    ∃ haX₁ : a ∈ S₁.X, ∃ haY₂ : a ∈ S₂.Y,
      (standardRepr2sumComposition ha hXY).fst.B =
      (matrix2sumComposition
        (S₁.B ∘ Set.diff_subset.elem)
        (S₁.B ⟨a, haX₁⟩)
        (S₂.B · ∘ Set.diff_subset.elem)
        (S₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ S₁.X ∩ S₂.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma standardRepr2sumComposition_hasTuSigning {S₁ S₂ : StandardRepr α Z2} {a : α} (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y)
    (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
    (standardRepr2sumComposition ha hXY).fst.HasTuSigning := by
  obtain ⟨B₁, hB₁, hBB₁⟩ := hS₁
  obtain ⟨B₂, hB₂, hBB₂⟩ := hS₂
  obtain ⟨haX₁, haY₂, hB⟩ := standardRepr2sumComposition_B ha hXY
  let x' : S₁.Y.Elem → ℚ := B₁ ⟨a, haX₁⟩
  let y' : S₂.X.Elem → ℚ := (B₂ · ⟨a, haY₂⟩)
  let A₁' : Matrix (S₁.X \ {a}).Elem S₁.Y.Elem ℚ := B₁ ∘ Set.diff_subset.elem
  let A₂' : Matrix S₂.X.Elem (S₂.Y \ {a}).Elem ℚ := (B₂ · ∘ Set.diff_subset.elem)
  have hA₁ :
    ∀ i : (S₁.X \ {a}).Elem, ∀ j : S₁.Y.Elem,
      |A₁' i j| = (S₁.B (Set.diff_subset.elem i) j).val
  · intro i j
    exact hBB₁ (Set.diff_subset.elem i) j
  have hA₂ :
    ∀ i : S₂.X.Elem, ∀ j : (S₂.Y \ {a}).Elem,
      |A₂' i j| = (S₂.B i (Set.diff_subset.elem j)).val
  · intro i j
    exact hBB₂ i (Set.diff_subset.elem j)
  have hx' : ∀ j, |x' j| = (S₁.B ⟨a, haX₁⟩ j).val
  · intro j
    exact hBB₁ ⟨a, haX₁⟩ j
  have hy' : ∀ i, |y' i| = (S₂.B i ⟨a, haY₂⟩).val
  · intro i
    exact hBB₂ i ⟨a, haY₂⟩
  let B' := matrix2sumComposition A₁' x' A₂' y' -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply matrix2sumComposition_isTotallyUnimodular
    · convert hB₁.comp_rows
        (fun i : (S₁.X \ {a}).Elem ⊕ Unit => i.casesOn Set.diff_subset.elem (fun _ => ⟨a, haX₁⟩))
      aesop
    · convert hB₂.comp_cols
        (fun j : Unit ⊕ (S₂.Y \ {a}).Elem => j.casesOn (fun _ => ⟨a, haY₂⟩) Set.diff_subset.elem)
      aesop
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl i₁ =>
      cases j.toSum with
      | inl j₁ =>
        specialize hA₁ i₁ j₁
        simp_all [B']
      | inr j₂ =>
        simp_all [B']
    | inr i₂ =>
      cases hj : j.toSum with
      | inl j₁ =>
        simp only [Matrix.fromBlocks_apply₂₁, B', hx', hy', abs_mul]
        apply Z2val_toRat_mul_Z2val_toRat
      | inr j₂ =>
        specialize hA₂ i₂ j₂
        simp_all [x', y', A₁', A₂', B']

/-- Any 2-sum of regular matroids is a regular matroid.
    This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply standardRepr2sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂
