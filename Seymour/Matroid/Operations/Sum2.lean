import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Notation
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity
import Seymour.Matrix.Determinants
import Seymour.Matrix.PreTUness


section Experimental

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

-- TODO - refactor appliations of these
lemma Matrix.IsTotallyUnimodular.duplicate_last_row {X Y : Type} {Aₗ : Matrix X Y ℚ} {x : Y → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) :
    (Aₗ ⊟ ▬x ⊟ ▬x).IsTotallyUnimodular := by
  convert hAx.comp_rows (Sum.casesOn · id Sum.inr)
  aesop

private lemma Matrix.IsTotallyUnimodular.aux190 {α : Type} [DecidableEq α] {Xₗ Yₗ : Set α} {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) :
    (Aₗ ⊟ ▬x ⊟ ▬(-x) ⊟ ▬0).IsTotallyUnimodular := by
  convert ((hAx.duplicate_last_row).mul_rows (show ∀ j, (·.casesOn 1 (-1)) j ∈ SignType.cast.range by rintro (_|_) <;> simp)
    ).fromRows_zero Unit
  aesop

end Experimental


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
lemma standardRepr2sumComposition_B_eq {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
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

private lemma matrix2sumComposition_left_isTotallyUnimodular_aux {α : Type} [DecidableEq α]
    {Xₗ Yₗ Xᵣ : Set α} {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hy : ∀ x : Xᵣ, y x ∈ SignType.cast.range) :
    (Aₗ ⊟ (y · * x ·)).IsTotallyUnimodular := by
  convert hAx.aux190.comp_rows (fun i : Xₗ.Elem ⊕ Xᵣ.Elem => i.casesOn (Sum.inl ∘ Sum.inl ∘ Sum.inl) (fun iᵣ : Xᵣ =>
    if h1 : y iᵣ = 1 then
      ◩◩◪()
    else if h9 : y iᵣ = -1 then
      ◩◪()
    else if h0 : y iᵣ = 0 then
      ◪()
    else False.elim (by
      obtain ⟨s, hs⟩ := hy iᵣ
      cases s <;> simp_all)))
  ext i
  cases i with
  | inl iₗ =>
    simp
  | inr iᵣ =>
    obtain ⟨s, hs⟩ := hy iᵣ
    if h1 : y iᵣ = 1 then
      simp_all
    else if h9 : y iᵣ = -1 then
      simp_all
    else if h0 : y iᵣ = 0 then
      simp_all
    else
      exfalso
      obtain ⟨s, hs⟩ := hy iᵣ
      cases s <;> simp_all

private lemma matrix2sumComposition_bottom_isTotallyUnimodular_aux' {α : Type} [DecidableEq α]
    {Yₗ Xᵣ Yᵣ : Set α} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {x : Yₗ → ℚ} {y : Xᵣ → ℚ}
    (hAy : (Aᵣ ◫ ▮y).IsTotallyUnimodular) (hx : ∀ y : Yₗ, x y ∈ SignType.cast.range) :
    (Aᵣ ◫ (y · * x ·)).IsTotallyUnimodular := by
  have hAy' := hAy.transpose
  rw [Matrix.transpose_fromCols, Matrix.transpose_replicateCol] at hAy'
  have result := (matrix2sumComposition_left_isTotallyUnimodular_aux hAy' hx).transpose
  rw [Matrix.transpose_fromRows, Matrix.transpose_transpose] at result
  simp_rw [mul_comm]
  exact result

private lemma matrix2sumComposition_bottom_isTotallyUnimodular_aux {α : Type} [DecidableEq α]
    {Yₗ Xᵣ Yᵣ : Set α} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {x : Yₗ → ℚ} {y : Xᵣ → ℚ}
    (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) (hx : ∀ y : Yₗ, x y ∈ SignType.cast.range) :
    ((y · * x ·) ◫ Aᵣ).IsTotallyUnimodular := by
  have hAy' : (Aᵣ ◫ ▮y).IsTotallyUnimodular
  · convert hAy.comp_cols Sum.swap
    aesop
  convert (matrix2sumComposition_bottom_isTotallyUnimodular_aux' hAy' hx).comp_cols Sum.swap
  aesop

lemma matrix2sumComposition_left_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (Aₗ ⊟ (y · * x ·)).IsTotallyUnimodular :=
  matrix2sumComposition_left_isTotallyUnimodular_aux hAx (hAy.apply · ◩())

lemma matrix2sumComposition_bottom_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    ((y · * x ·) ◫ Aᵣ).IsTotallyUnimodular :=
  matrix2sumComposition_bottom_isTotallyUnimodular_aux hAy (hAx.apply ◪())

private lemma matrix2sumComposition_eq_fromRows {α β : Type} [Semiring β] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ β) (x : Yₗ → β) (Aᵣ : Matrix Xᵣ Yᵣ β) (y : Xᵣ → β) :
    matrix2sumComposition Aₗ x Aᵣ y = (Aₗ ◫ 0) ⊟ ((y · * x ·) ◫ Aᵣ) := by
  rfl

/-- The result of the vector `v` after pivoting on `j`th element in the row `u` and restriction. -/
noncomputable def shortTableauPivotOuterRow {Y Y' R : Type} [DecidableEq Y'] [DivisionRing R]
    (u : Y → R) (j : Y') (g : Y' → Y) (v : Y' → R) : Y' → R :=
  fun j' : Y' => if j' = j then - v j' / u (g j) else (u (g j) * v j' - u (g j') * v j) / u (g j)

private lemma Matrix.shortTableauPivot_outer {X Y X' Y' R : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Y'] [Field R]
    (B : Matrix X Y R) (i : X) (j : Y') (f : X' → X) (g : Y' → Y) (hf : i ∉ f.range) (hg : g.Injective)
    (hBij : B i (g j) = 1 ∨ B i (g j) = -1)
    (v : Y' → R) (y : X' → R) (hBfg : ∀ i j, B (f i) (g j) = y i * v j) :
    ∀ i' : X', ∀ j' : Y',
      (B.shortTableauPivot i (g j)) (f i') (g j') =
      y i' * shortTableauPivotOuterRow (B i) j g v j' := by
  intro i' j'
  unfold Matrix.shortTableauPivot shortTableauPivotOuterRow
  cases hBij with
  | inl h1 =>
    if hj : j' = j then
      simp_all
    else
      have hgj : g j' ≠ g j := (hj <| hg ·)
      have hfi : f i' ≠ i := (hf <| ⟨i', ·⟩)
      simp [*]
      ring
  | inr h9 =>
    if hj : j' = j then
      simp_all
    else
      have hgj : g j' ≠ g j := (hj <| hg ·)
      have hfi : f i' ≠ i := (hf <| ⟨i', ·⟩)
      simp [*]
      ring

private lemma matrix2sumComposition_shortTableauPivot {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (x : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (y : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} (hAij : Aₗ i j = 1 ∨ Aₗ i j = -1) :
    let B := matrix2sumComposition Aₗ x Aᵣ y
    B.shortTableauPivot ◩i ◩j =
    matrix2sumComposition (Aₗ.shortTableauPivot i j) (shortTableauPivotOuterRow (B ◩i) j Sum.inl x) Aᵣ y := by
  intro B
  have hBAₗ : (B.shortTableauPivot ◩i ◩j).toBlocks₁₁ = Aₗ.shortTableauPivot i j
  · exact (B.submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm
  have hB0 : (B.shortTableauPivot ◩i ◩j).toBlocks₁₂ = 0
  · ext iₗ jᵣ
    exact B.shortTableauPivot_zero i ◩j Sum.inl Sum.inr (by simp) (by simp [matrix2sumComposition, B]) iₗ jᵣ
  have hBD : (B.shortTableauPivot ◩i ◩j).toBlocks₂₁ = Matrix.of (y · * shortTableauPivotOuterRow (B ◩i) j Sum.inl x ·)
  · have := B.shortTableauPivot_outer ◩i j Sum.inr Sum.inl (by simp) Sum.inl_injective hAij x y
    aesop
  have hBAᵣ : (B.shortTableauPivot ◩i ◩j).toBlocks₂₂ = Aᵣ
  · exact B.shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr (by simp) (by simp) ↓rfl
  rw [←(B.shortTableauPivot ◩i ◩j).fromBlocks_toBlocks, hBAₗ, hBAᵣ, hB0, hBD]
  rfl

-- OK
private lemma matrix2sumComposition_isPreTU_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ x Aᵣ y).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact (hAx.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAy.apply iᵣ ◩()) (hAx.apply ◪() jₗ)
    | inr jᵣ => exact (hAy.comp_cols Sum.inr).apply iᵣ jᵣ

lemma matrix2sumComposition_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ x Aᵣ y).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  cases k with
  | zero => simp [Matrix.IsPreTU]
  | succ m => induction m generalizing Aₗ x Aᵣ y with
    | zero => exact matrix2sumComposition_isPreTU_1 hAx hAy
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      · exact ((matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_rows g hf) ▸ zero_in_signTypeCastRange
      wlog hg : g.Injective
      · exact ((matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_cols f hg) ▸ zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · push_neg at hfₗ
        convert (matrix2sumComposition_bottom_isTotallyUnimodular hAx hAy).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext i j
        rw [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ i]
        rfl
      obtain ⟨iₗ, xₗ, hixₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((matrix2sumComposition Aₗ x Aᵣ y).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
        intro j
        cases hgj : g j with
        | inl => exact Matrix.submatrix_apply .. ▸ hgj ▸ hixₗ ▸ hgₗ j _ hgj
        | inr => exact Matrix.submatrix_apply .. ▸ hgj ▸ hixₗ ▸ rfl
      obtain ⟨j₀, y₀, hjy₀, hAxy0⟩ := hgₗ
      have hAxy1 : Aₗ xₗ y₀ = 1 ∨ Aₗ xₗ y₀ = -1
      · obtain ⟨s, hs⟩ := (hAx.comp_rows Sum.inl).apply xₗ y₀
        cases s with
        | zero => exact (hAxy0 hs.symm).elim
        | pos => exact Or.inl hs.symm
        | neg => exact Or.inr hs.symm
      by_contra hAfg
      obtain ⟨_, _, -, -, impossible⟩ :=
        shortTableauPivot_submatrix_det_ni_signTypeCastRange hAfg iₗ j₀ (by convert hAxy1 <;> simp [matrix2sumComposition, *])
      apply impossible
      rw [(matrix2sumComposition Aₗ x Aᵣ y).submatrix_shortTableauPivot hf hg, Matrix.submatrix_submatrix,
        hixₗ, hjy₀, matrix2sumComposition_shortTableauPivot Aₗ x Aᵣ y hAxy1]
      apply ih _ hAy
      have hAxy0' : (Aₗ ⊟ ▬x) ◩xₗ y₀ ≠ 0 := hAxy0
      convert hAx.shortTableauPivot hAxy0'
      ext i j
      cases i with
      | inl =>
        simp [Matrix.shortTableauPivot]
      | inr =>
        simp [Matrix.shortTableauPivot, shortTableauPivotOuterRow]
        if hj : j = y₀ then
          cases hAxy1 with
          | inl h1 => simp [hj, h1]
          | inr h9 => simp [hj, h9]
        else
          field_simp [hj]
          ring


-- OK
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

-- OK
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
