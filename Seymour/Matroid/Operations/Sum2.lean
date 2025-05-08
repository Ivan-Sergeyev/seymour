import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Notation
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity
import Seymour.Matrix.Determinants
import Seymour.Matrix.PreTUness


section ConvenientAPI

private abbrev Eq._ₗ {α : Type} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : X :=
  ⟨a, Set.mem_of_mem_inter_left (ha.symm.subset rfl)⟩

private abbrev Eq._ᵣ {α : Type} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : Y :=
  ⟨a, Set.mem_of_mem_inter_right (ha.symm.subset rfl)⟩

@[simp]
private abbrev Matrix.dropRow {α R : Type} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix (X \ {a}).Elem Y.Elem R :=
  A ∘ Set.diff_subset.elem

@[simp]
private abbrev Matrix.dropCol {α R : Type} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix X.Elem (Y \ {a}).Elem R :=
  (A · ∘ Set.diff_subset.elem)

@[simp]
private abbrev Matrix.interRow {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : X ∩ Z = {a}) :
    Y.Elem → R :=
  A ha._ₗ

@[simp]
private abbrev Matrix.interCol {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    X.Elem → R :=
  (A · ha._ᵣ)

@[simp]
private abbrev Matrix.reglueRow {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : X ∩ Z = {a}) :
    Matrix ((X \ {a}).Elem ⊕ Unit) Y.Elem R :=
  A.dropRow a ⊟ ▬(A.interRow ha)

@[simp]
private abbrev Matrix.reglueCol {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    Matrix X.Elem (Unit ⊕ (Y \ {a}).Elem) R :=
  ▮(A.interCol ha) ◫ A.dropCol a

private lemma Matrix.reglueRow_eq {α R : Type} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R} {a : α} (ha : X ∩ Z = {a}) :
    A.reglueRow ha = A.submatrix (·.casesOn Set.diff_subset.elem ↓ha._ₗ) id := by
  aesop

private lemma Matrix.reglueCol_eq {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    A.reglueCol ha = A.submatrix id (·.casesOn ↓ha._ᵣ Set.diff_subset.elem) := by
  aesop

private lemma Matrix.IsTotallyUnimodular.dropRow {α R : Type} [CommRing R] {X Y : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) (a : α) :
    (A.dropRow a).IsTotallyUnimodular := by
  exact hA.comp_rows Set.diff_subset.elem

private lemma Matrix.IsTotallyUnimodular.dropCol {α R : Type} [CommRing R] {X Y : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) (a : α) :
    (A.dropCol a).IsTotallyUnimodular := by
  exact hA.comp_cols Set.diff_subset.elem

private lemma Matrix.IsTotallyUnimodular.reglueRow {α R : Type} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) {a : α} (ha : X ∩ Z = {a}) :
    (A.reglueRow ha).IsTotallyUnimodular := by
  rw [A.reglueRow_eq ha]
  apply hA.submatrix

private lemma Matrix.IsTotallyUnimodular.reglueCol {α R : Type} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) {a : α} (ha : Z ∩ Y = {a}) :
    (A.reglueCol ha).IsTotallyUnimodular := by
  rw [A.reglueCol_eq ha]
  apply hA.submatrix

end ConvenientAPI


section TwoSumDefinitions

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrix2sumComposition {α β : Type} [Semiring β] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ β) (x : Yₗ → β) (Aᵣ : Matrix Xᵣ Yᵣ β) (y : Xᵣ → β) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) β :=
  Matrix.fromBlocks Aₗ 0 (y · * x ·) Aᵣ

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

-- Use instead of `unfold standardRepr2sumComposition; dsimp`
private lemma standardRepr2sumComposition_B_eq {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) :
    (standardRepr2sumComposition ha hXY).fst.B =
    (matrix2sumComposition (Sₗ.B.dropRow a) (Sₗ.B.interRow ha) (Sᵣ.B.dropCol a) (Sᵣ.B.interCol ha)).toMatrixUnionUnion :=
  rfl

/-- Binary matroid `M` is a result of 2-summing `Mₗ` and `Mᵣ` in some way. -/
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

instance Matroid.Is2sumOf.finS {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} (hM : M.Is2sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

end TwoSumDefinitions


section TwoSumSpecificPivoting

-- todo: move results from this section to `Pivoting.lean`?

/-- `p`: pivot row, `r`: other row, `g`: map from columns of `r` to columns of `p`, `j'`: pivot column in indexing of `r` -/
private abbrev shortTableauPivotOtherRow {Y Y' R : Type} [DecidableEq Y'] [Field R]
    (p : Y → R) (r : Y' → R) (g : Y' → Y) (y' : Y'): Y' → R :=
  ((▬(p ∘ g) ⊟ ▬r).shortTableauPivot ◩() y') ◪()

private lemma Matrix.shortTableauPivot_otherRow_eq {X Y Y' R : Type} [Field R] [DecidableEq X] [DecidableEq Y] [DecidableEq Y']
    (A : Matrix X Y R) (x : X) (y' : Y') {i : X} (hix : i ≠ x) {g : Y' → Y} (hg : g.Injective) :
    (A.shortTableauPivot x (g y')) i ∘ g = shortTableauPivotOtherRow (A x) (A i ∘ g) g y' := by
  unfold shortTableauPivotOtherRow Matrix.shortTableauPivot
  ext j'
  simp only [one_div, Function.comp_apply, Matrix.of_apply, hix, ↓reduceIte, Matrix.fromRows_apply_inl,
    Matrix.replicateRow_apply, reduceCtorEq, Matrix.fromRows_apply_inr]
  if hj' : j' = y' then
    simp only [hj', ↓reduceIte]
  else
    simp only [hj', ↓reduceIte, ite_eq_right_iff]
    intro hgj'
    exact (hj' (hg hgj')).elim

private lemma Matrix.shortTableauPivot_outer {X Y X' Y' R : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Y'] [Field R]
    (A : Matrix X Y R) (x : X) (y' : Y') (f : X' → X) (g : Y' → Y) (hf : x ∉ f.range) (hg : g.Injective)
    (r : Y' → R) (c : X' → R) (hBfg : A.submatrix f g = (c · * r ·)) :
    (A.shortTableauPivot x (g y')).submatrix f g = (c · * (shortTableauPivotOtherRow (A x) r g y') ·) := by
  ext i j
  rw [Matrix.submatrix_apply]
  have hAfg_eq := A.shortTableauPivot_otherRow_eq x y' (ne_of_mem_of_not_mem (Set.mem_range_self i) hf) hg
  have hAfg_val : A (f i) ∘ g = (c i * r ·) := congrFun hBfg i
  have hAfg_eq := hAfg_val ▸ Function.comp_apply ▸ (congrFun hAfg_eq j)
  rw [hAfg_eq]
  unfold shortTableauPivotOtherRow Matrix.shortTableauPivot
  simp only [Matrix.fromRows_apply_inl, Matrix.replicateRow_apply, Function.comp_apply, one_div, Matrix.of_apply,
    reduceCtorEq, ↓reduceIte, Matrix.fromRows_apply_inr, mul_ite]
  split_ifs <;> ring

private lemma matrix2sumComposition_shortTableauPivot {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (x : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (y : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} :
    (matrix2sumComposition Aₗ x Aᵣ y).shortTableauPivot ◩i ◩j =
    matrix2sumComposition (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) x id j) Aᵣ y := by
  rw [←((matrix2sumComposition Aₗ x Aᵣ y).shortTableauPivot ◩i ◩j).fromBlocks_toBlocks,
      ←(matrix2sumComposition (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) x id j) Aᵣ y).fromBlocks_toBlocks,
      Matrix.fromBlocks_inj]
  constructor
  · exact ((matrix2sumComposition Aₗ x Aᵣ y).submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm
  constructor
  · ext iₗ jᵣ
    exact (matrix2sumComposition Aₗ x Aᵣ y).shortTableauPivot_zero i ◩j Sum.inl Sum.inr
      (by simp) (by simp [matrix2sumComposition]) iₗ jᵣ
  constructor
  · exact (matrix2sumComposition Aₗ x Aᵣ y).shortTableauPivot_outer ◩i j Sum.inr Sum.inl (by simp) Sum.inl_injective x y rfl
  · exact (matrix2sumComposition Aₗ x Aᵣ y).shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr
      (by simp) (by simp) ↓rfl

private lemma Matrix.fromRowsIsTotallyUnimodular_pivot {α : Type} [DecidableEq α] {Xₗ Yₗ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} (hAₗx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) {xₗ : Xₗ} {y₀ : Yₗ} (hxₗy₀ : Aₗ xₗ y₀ ≠ 0) :
    ((Aₗ.shortTableauPivot xₗ y₀) ⊟ ▬(shortTableauPivotOtherRow (Aₗ xₗ) x id y₀)).IsTotallyUnimodular := by
  have hxₗy₀' : (Aₗ ⊟ ▬x) ◩xₗ y₀ ≠ 0 := hxₗy₀
  have hAxtu := hAₗx.shortTableauPivot hxₗy₀'
  convert hAₗx.shortTableauPivot hxₗy₀'
  ext i j
  cases i with
  | inl i =>
      exact congrFun (congrFun (((Aₗ ⊟ ▬x).submatrix_shortTableauPivot Sum.inl_injective Function.injective_id xₗ y₀)) i) j
  | inr i => rfl

private lemma Matrix.shortTableauPivot_abs_det_eq_submatrix_abs_det {F : Type} [LinearOrderedField F] {k : ℕ}
    (A : Matrix (Fin k.succ) (Fin k.succ) F) {i j : Fin k.succ} (hAij : A i j = 1 ∨ A i j = -1) :
    ∃ f : Fin k → Fin k.succ, ∃ g : Fin k → Fin k.succ, f.Injective ∧ g.Injective ∧
      |A.det| = |((A.shortTableauPivot i j).submatrix f g).det| := by
  have hAij0 : A i j ≠ 0 := by cases hAij with
  | inl h1 => exact ne_zero_of_eq_one h1
  | inr hn1 =>
      rw [hn1, ne_eq, neg_eq_zero, ←ne_eq]
      exact one_ne_zero
  obtain ⟨f, g, hf, hg, hAfg⟩ := shortTableauPivot_submatrix_det_abs_eq_div hAij0
  have hAij_abs : |A i j| = 1 := by cases hAij with
  | inl h => rw [h, abs_one]
  | inr h => rw [h, abs_neg, abs_one]
  rw [hAij_abs, div_one] at hAfg
  use f, g, hf, hg, (hAfg).symm

end TwoSumSpecificPivoting


section AdjoinOuterProductTU

-- todo: move results from this section to `TotalUnimodularity.lean`?

private lemma Matrix.IsTotallyUnimodular.fromCols_comm {X Y₁ Y₂ : Type} {A₁ : Matrix X Y₁ ℚ} {A₂ : Matrix X Y₂ ℚ}
    (hA₁A₂ : (A₁ ◫ A₂).IsTotallyUnimodular) :
    (A₂ ◫ A₁).IsTotallyUnimodular := by
  convert hA₁A₂.comp_cols Sum.swap
  ext i
  cases i <;> simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Function.comp_apply, Sum.swap_inl, Sum.swap_inr]

private lemma Matrix.IsTotallyUnimodular.adjoin_pnz_cols {X Y : Type} [DecidableEq Y] {A : Matrix X Y ℚ} {y : X → ℚ}
    (hAy : (A ◫ ▮y).IsTotallyUnimodular) :
    (A ◫ ▮y ◫ ▮(-y) ◫ ▮0).IsTotallyUnimodular := by
  have hAyy : (A ◫ ▮y ◫ ▮y).IsTotallyUnimodular := by
    convert hAy.comp_cols (Sum.casesOn · id Sum.inr)
    ext j
    cases j <;> simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, id_eq, Function.comp_apply]
  convert (hAyy.mul_cols (show ∀ j, (·.casesOn 1 (-1)) j ∈ SignType.cast.range by rintro (_|_) <;> simp)).fromCols_zero Unit
  ext i j
  cases j <;> simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.replicateCol_apply, Matrix.of_apply,
    Pi.one_apply, Pi.neg_apply, mul_neg, mul_one]

private lemma Matrix.IsTotallyUnimodular.adjoin_outerProduct {X Yᵣ Y' : Type} [DecidableEq Yᵣ] {A : Matrix X Yᵣ ℚ} {y : X → ℚ}
    (hAy : (A ◫ ▮y).IsTotallyUnimodular) {x : Y' → ℚ} (hx : ∀ j' : Y', x j' ∈ SignType.cast.range) :
    (A ◫ (y · * x ·)).IsTotallyUnimodular := by
  convert hAy.adjoin_pnz_cols.comp_cols (fun j : Yᵣ ⊕ Y' => j.casesOn (Sum.inl ∘ Sum.inl ∘ Sum.inl) (fun j : Y' =>
    if h1 : x j = 1 then ◩◩◪()
    else if h9 : x j = -1 then ◩◪()
    else if h0 : x j = 0 then ◪()
    else False.elim (by obtain ⟨s, hs⟩ := hx j; cases s <;> simp_all)))
  ext j
  cases j with
  | inl j => simp only [Matrix.fromCols_apply_inl, Function.comp_apply]
  | inr j =>
    -- proof 1: short, but implicit
    obtain ⟨s, hs⟩ := hx j
    simp only [Matrix.fromCols_apply_inr, Matrix.replicateCol_zero, Function.comp_apply]
    split_ifs
    all_goals try simp_all
    exfalso
    cases s <;> simp_all
    -- -- proof 2: explicit, but long
    -- if h1 : x j = 1 then
    --   simp only [h1, Matrix.fromCols_apply_inr, mul_one, Function.comp_apply, Matrix.fromCols_apply_inl,
    --     Matrix.replicateCol_apply, ↓reduceDIte]
    -- else if h9 : x j = -1 then
    --   simp_all only [h9, Matrix.fromCols_apply_inr, mul_neg, mul_one, Matrix.replicateCol_zero, Function.comp_apply,
    --     ↓reduceDIte, Matrix.fromCols_apply_inl, Matrix.replicateCol_apply, Pi.neg_apply]
    -- else if h0 : x j = 0 then
    --   simp only [h0, Matrix.fromCols_apply_inr, mul_zero, Matrix.replicateCol_zero,
    --     Function.comp_apply, zero_ne_one, zero_eq_neg, one_ne_zero, Matrix.zero_apply, ↓reduceDIte]
    -- else
    --   exfalso
    --   obtain ⟨s, hs⟩ := hx j
    --   cases s with
    --   | zero => exact h0 hs.symm
    --   | neg => exact h9 hs.symm
    --   | pos => exact h1 hs.symm

private lemma matrix2sumComposition_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] [DecidableEq Yₗ]
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAₗx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hyAᵣ : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    ((y · * x ·) ◫ Aᵣ).IsTotallyUnimodular :=
  (hyAᵣ.fromCols_comm.adjoin_outerProduct (hAₗx.apply ◪())).fromCols_comm

end AdjoinOuterProductTU


section TwoSumTUness

private lemma matrix2sumComposition_isPreTU_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAₗx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hyAᵣ : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ x Aᵣ y).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact (hAₗx.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hyAᵣ.apply iᵣ ◩()) (hAₗx.apply ◪() jₗ)
    | inr jᵣ => exact (hyAᵣ.comp_cols Sum.inr).apply iᵣ jᵣ

private lemma matrix2sumComposition_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAₗx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hyAᵣ : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ x Aᵣ y).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  cases k with
  | zero => simp [Matrix.IsPreTU]
  | succ m => induction m generalizing Aₗ x Aᵣ y with
    | zero => exact matrix2sumComposition_isPreTU_1 hAₗx hyAᵣ
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      · exact ((matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_rows g hf) ▸ zero_in_signTypeCastRange
      wlog hg : g.Injective
      · exact ((matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_cols f hg) ▸ zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · push_neg at hfₗ
        convert (matrix2sumComposition_bottom_isTotallyUnimodular hAₗx hyAᵣ).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext i j
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ i]
        rfl
      obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((matrix2sumComposition Aₗ x Aᵣ y).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
        intro j
        cases hgj : g j with
        | inl => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ hgₗ j _ hgj
        | inr => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ rfl
      obtain ⟨j₀, y₀, hgj₀, hAₗxy0⟩ := hgₗ
      have hAₗxy1 : Aₗ xₗ y₀ = 1 ∨ Aₗ xₗ y₀ = -1
      · obtain ⟨s, hs⟩ := (hAₗx.comp_rows Sum.inl).apply xₗ y₀
        cases s with
        | zero => exact (hAₗxy0 hs.symm).elim
        | pos => exact Or.inl hs.symm
        | neg => exact Or.inr hs.symm
      have hAₗxy1' : ((matrix2sumComposition Aₗ x Aᵣ y).submatrix f g) iₗ j₀ = 1 ∨
                    ((matrix2sumComposition Aₗ x Aᵣ y).submatrix f g) iₗ j₀ = -1 := by
        rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
        exact hAₗxy1
      obtain ⟨f', g', hf', hg', hdet⟩ := Matrix.shortTableauPivot_abs_det_eq_submatrix_abs_det
        ((matrix2sumComposition Aₗ x Aᵣ y).submatrix f g) hAₗxy1'
      rw [in_signTypeCastRange_iff_abs, hdet, (matrix2sumComposition Aₗ x Aᵣ y).submatrix_shortTableauPivot hf hg iₗ j₀,
        hfiₗ, hgj₀, Matrix.submatrix_submatrix, matrix2sumComposition_shortTableauPivot Aₗ x Aᵣ y, ←in_signTypeCastRange_iff_abs]
      exact (ih (Matrix.fromRowsIsTotallyUnimodular_pivot hAₗx hAₗxy0) hyAᵣ) (f ∘ f') (g ∘ g')

end TwoSumTUness


section TwoSumRegularty

lemma standardRepr2sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {a : α}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr2sumComposition ha hXY).fst.B.HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  let B' := matrix2sumComposition (Bₗ.dropRow a) (Bₗ.interRow ha) (Bᵣ.dropCol a) (Bᵣ.interCol ha)
  use B'.toMatrixUnionUnion
  constructor
  · exact (matrix2sumComposition_isTotallyUnimodular (hBₗ.reglueRow ha) (hBᵣ.reglueCol ha)).toMatrixUnionUnion
  · intro i j
    simp only [standardRepr2sumComposition_B_eq, Matrix.toMatrixUnionUnion, Function.comp_apply]
    exact i.toSum.casesOn
      (fun iₗ => j.toSum.casesOn (hBBₗ (Set.diff_subset.elem iₗ)) (fun _ => rfl))
      (fun iᵣ => j.toSum.casesOn
        (fun jₗ => Z2val_toRat_mul_Z2val_toRat (Sᵣ.B.interCol ha iᵣ) (Sₗ.B.interRow ha jₗ) ▸ hBBₗ ha._ₗ jₗ ▸ hBBᵣ iᵣ ha._ᵣ ▸
            abs_mul (Bᵣ.interCol ha iᵣ) (Bₗ.interRow ha jₗ))
        (hBBᵣ iᵣ <| Set.diff_subset.elem ·))

/-- Any 2-sum of regular matroids is a regular matroid.
    This is part two (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is2sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr2sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ

end TwoSumRegularty
