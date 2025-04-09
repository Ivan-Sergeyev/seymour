import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Notions.Regularity
import Seymour.Matrix.PreTU


/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrix2sumComposition {α β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

/-- `StandardRepr`-level 2-sum of two matroids.
    The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
    and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def standardRepr2sumComposition {α : Type} [DecidableEq α] {a : α} {S₁ S₂ : StandardRepr α Z2}
    (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
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
structure Matroid.Is2sumOf {α : Type} [DecidableEq α] (M : Matroid α) (M₁ M₂ : Matroid α) where
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

instance Matroid.Is2sumOf.finS {α : Type} [DecidableEq α] {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

infixl:63 " ⊟ " => Matrix.fromRows
infixl:63 " ◫ " => Matrix.fromCols
notation:64 "▬"r:81 => Matrix.replicateRow Unit r
notation:64 "▮"c:81 => Matrix.replicateCol Unit c

lemma Matrix.IsTotallyUnimodular.duplicate_last_row {X Y : Type} {A₁ : Matrix X Y ℚ} {x : Y → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) :
    (A₁ ⊟ ▬x ⊟ ▬x).IsTotallyUnimodular := by
  convert hAx.comp_rows (Sum.casesOn · id Sum.inr)
  aesop

private lemma Matrix.IsTotallyUnimodular.aux190 {α : Type} [DecidableEq α] {X₁ Y₁ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) :
    (A₁ ⊟ ▬x ⊟ ▬(-x) ⊟ ▬0).IsTotallyUnimodular := by
  rw [Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff]
  intro k f g hf hg
  have almost := hAx.duplicate_last_row k f g hf hg
  if last_row : ∃ i : Fin k, f i = ◪() then
    apply in_signTypeCastRange_of_neg_one_mul
    convert almost
    obtain ⟨i, hi⟩ := last_row
    have flipped : (A₁ ⊟ ▬x ⊟ ▬(-x)) = (A₁ ⊟ ▬x ⊟ ▬x).updateRow ◪() (-x)
    · aesop
    have bubbled : ((A₁ ⊟ ▬x ⊟ ▬x).updateRow (◪()) (-x)).submatrix f g = ((A₁ ⊟ ▬x ⊟ ▬x).submatrix f g).updateRow i ((-x) ∘ g)
    · ext r
      if hr : r = i then
        simp [hr, hi]
      else
        have hfr : f r ≠ ◪() := (hr <| hf <| ·.trans hi.symm)
        simp [hr, hfr]
    rw [flipped, bubbled, ←((A₁ ⊟ ▬x ⊟ ▬x).submatrix f g).det_updateRow_smul i (-1) ((-x) ∘ g)]
    convert_to (((A₁ ⊟ ▬x ⊟ ▬x).submatrix f g).updateRow i (x ∘ g)).det = ((A₁ ⊟ ▬x ⊟ ▬x).submatrix f g).det
    · congr!
      ext
      simp
    congr
    ext r
    if hr : r = i then
      simp [hr, hi]
    else
      have hfr : f r ≠ ◪() := (hr <| hf <| ·.trans hi.symm)
      simp [hr, hfr]
  else
    convert almost using 2
    ext i
    cases hfi : f i <;> simp_all

private lemma lemma6₁_aux {α : Type} [DecidableEq α] {X₁ Y₁ X₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hy : ∀ x : X₂, y x ∈ SignType.cast.range) :
    (A₁ ⊟ (y · * x ·)).IsTotallyUnimodular := by
  convert hAx.aux190.comp_rows (fun i : X₁.Elem ⊕ X₂.Elem => i.casesOn (Sum.inl ∘ Sum.inl ∘ Sum.inl) (fun i₂ =>
    if h1 : y i₂ = 1 then
      ◩◩◪()
    else if h9 : y i₂ = -1 then
      ◩◪()
    else if h0 : y i₂ = 0 then
      ◪()
    else False.elim (by
      obtain ⟨s, hs⟩ := hy i₂
      cases s <;> simp_all)))
  ext i
  cases i with
  | inl i₁ =>
    simp
  | inr i₂ =>
    obtain ⟨s, hs⟩ := hy i₂
    if h1 : y i₂ = 1 then
      simp_all
    else if h9 : y i₂ = -1 then
      simp_all
    else if h0 : y i₂ = 0 then
      simp_all
    else
      exfalso
      obtain ⟨s, hs⟩ := hy i₂
      cases s <;> simp_all

private lemma lemma6₂_aux' {α : Type} [DecidableEq α] {Y₁ X₂ Y₂ : Set α} {A₂ : Matrix X₂ Y₂ ℚ} {x : Y₁ → ℚ} {y : X₂ → ℚ}
    (hAy : (A₂ ◫ ▮y).IsTotallyUnimodular) (hx : ∀ y : Y₁, x y ∈ SignType.cast.range) :
    (A₂ ◫ (y · * x ·)).IsTotallyUnimodular := by
  have hAy' := hAy.transpose
  rw [Matrix.transpose_fromCols, Matrix.transpose_replicateCol] at hAy'
  have result := (lemma6₁_aux hAy' hx).transpose
  rw [Matrix.transpose_fromRows, Matrix.transpose_transpose] at result
  simp_rw [mul_comm]
  exact result

private lemma lemma6₂_aux {α : Type} [DecidableEq α] {Y₁ X₂ Y₂ : Set α} {A₂ : Matrix X₂ Y₂ ℚ} {x : Y₁ → ℚ} {y : X₂ → ℚ}
    (hAy : (▮y ◫ A₂).IsTotallyUnimodular) (hx : ∀ y : Y₁, x y ∈ SignType.cast.range) :
    ((y · * x ·) ◫ A₂).IsTotallyUnimodular := by
  have hAy' : (A₂ ◫ ▮y).IsTotallyUnimodular
  · convert hAy.comp_cols Sum.swap
    aesop
  convert (lemma6₂_aux' hAy' hx).comp_cols Sum.swap
  aesop

lemma lemma6₁ {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular) :
    (A₁ ⊟ (y · * x ·)).IsTotallyUnimodular :=
  lemma6₁_aux hAx (hAy.apply · ◩())

lemma lemma6₂ {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular) :
    ((y · * x ·) ◫ A₂).IsTotallyUnimodular :=
  lemma6₂_aux hAy (hAx.apply ◪())

private lemma matrix2sumComposition_eq_fromRows {α β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    matrix2sumComposition A₁ x A₂ y = (A₁ ◫ 0) ⊟ ((y · * x ·) ◫ A₂) := by
  rfl

private lemma matrix2sumComposition_eq_fromCols {α β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    matrix2sumComposition A₁ x A₂ y = (A₁ ⊟ (y · * x ·)) ◫ (0 ⊟ A₂) := by
  symm
  apply Matrix.fromCols_fromRows_eq_fromBlocks

private lemma lemma11₁ {α : Type} {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular) :
    (matrix2sumComposition A₁ x A₂ y).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  have hA₁ : A₁.IsTotallyUnimodular := hAx.comp_rows Sum.inl
  have hA₂ : A₂.IsTotallyUnimodular := hAy.comp_cols Sum.inr
  cases f 0 with
  | inl i₁ => cases g 0 with
    | inl j₁ => exact hA₁.apply i₁ j₁
    | inr j₂ => exact zero_in_signTypeCastRange
  | inr i₂ => cases g 0 with
    | inl j₁ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAy.apply i₂ ◩()) (hAx.apply ◪() j₁)
    | inr j₂ => exact hA₂.apply i₂ j₂

private lemma lemma11₂_auxl {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    {n : ℕ} {f : Fin n → ↑X₁ ⊕ ↑X₂} {g : Fin n → ↑Y₁ ⊕ ↑Y₂}
    (hg : ∀ a : Fin n, ∀ b : Y₂, g a ≠ ◪b) :
    (matrix2sumComposition A₁ x A₂ y).submatrix f g = (A₁ ⊟ (y · * x ·)).submatrix f (fn_of_sum_ne_inr hg) := by
  ext
  rw [Matrix.submatrix_apply, eq_of_fn_sum_ne_inr hg, matrix2sumComposition_eq_fromCols]
  simp

private lemma lemma11₂_auxr {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    {n : ℕ} {f : Fin n → ↑X₁ ⊕ ↑X₂} {g : Fin n → ↑Y₁ ⊕ ↑Y₂}
    (hf : ∀ a : Fin n, ∀ b : X₁, f a ≠ ◩b) :
    (matrix2sumComposition A₁ x A₂ y).submatrix f g = ((y · * x ·) ◫ A₂).submatrix (fn_of_sum_ne_inl hf) g := by
  ext
  rw [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hf, matrix2sumComposition_eq_fromRows]
  simp

private lemma lemma11₂_auxll {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    {n : ℕ} {f : Fin n → ↑X₁ ⊕ ↑X₂} {g : Fin n → ↑Y₁ ⊕ ↑Y₂}
    (hf : ∀ a : Fin n, ∀ b : X₂, f a ≠ ◪b) (hg : ∀ a : Fin n, ∀ b : Y₂, g a ≠ ◪b) :
    (matrix2sumComposition A₁ x A₂ y).submatrix f g = A₁.submatrix (fn_of_sum_ne_inr hf) (fn_of_sum_ne_inr hg) := by
  ext
  simp [eq_of_fn_sum_ne_inr hf, eq_of_fn_sum_ne_inr hg]

private lemma lemma11₂_auxrl {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    {n : ℕ} {f : Fin n → ↑X₁ ⊕ ↑X₂} {g : Fin n → ↑Y₁ ⊕ ↑Y₂}
    (hf : ∀ a : Fin n, ∀ b : X₁, f a ≠ ◩b) (hg : ∀ a : Fin n, ∀ b : Y₂, g a ≠ ◪b) :
    (matrix2sumComposition A₁ x A₂ y).submatrix f g =
    Matrix.submatrix (y · * x ·) (fn_of_sum_ne_inl hf) (fn_of_sum_ne_inr hg) := by
  ext
  simp [eq_of_fn_sum_ne_inl hf, eq_of_fn_sum_ne_inr hg]

private lemma lemma11₂_auxrr {α : Type} {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    {n : ℕ} {f : Fin n → ↑X₁ ⊕ ↑X₂} {g : Fin n → ↑Y₁ ⊕ ↑Y₂}
    (hf : ∀ a : Fin n, ∀ b : X₁, f a ≠ ◩b) (hg : ∀ a : Fin n, ∀ b : Y₁, g a ≠ ◩b) :
    (matrix2sumComposition A₁ x A₂ y).submatrix f g = A₂.submatrix (fn_of_sum_ne_inl hf) (fn_of_sum_ne_inl hg) := by
  ext
  simp [eq_of_fn_sum_ne_inl hf, eq_of_fn_sum_ne_inl hg]

private lemma lemma11₂ {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular) :
    (matrix2sumComposition A₁ x A₂ y).IsPreTU 2 := by
  intro f g
  have hA₁ : A₁.IsTotallyUnimodular := hAx.comp_rows Sum.inl
  have hA₂ : A₂.IsTotallyUnimodular := hAy.comp_cols Sum.inr
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hg0 : g 0 <;> cases hg1 : g 1
  all_goals try
    rw [Matrix.det_fin_two]
    repeat rw [Matrix.submatrix_apply]
    simp only [hf0, hf1, hg0, hg1,
      Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, mul_zero, zero_mul, sub_zero, zero_sub, neg_mul_eq_neg_mul, zero_in_signTypeCastRange]
    all_goals apply in_signTypeCastRange_mul_in_signTypeCastRange <;>
      simp only [neg_in_signTypeCastRange, hA₁.apply, hA₂.apply]
  · rw [lemma11₂_auxll (by fin_cases · <;> simp_all) (by fin_cases · <;> simp_all)]
    apply A₁.isTotallyUnimodular_iff.→ hA₁
  · rw [lemma11₂_auxl (by fin_cases · <;> simp_all)]
    apply (Matrix.isTotallyUnimodular_iff _).→ (lemma6₁ hAx hAy)
  · rw [lemma11₂_auxl (by fin_cases · <;> simp_all)]
    apply (Matrix.isTotallyUnimodular_iff _).→ (lemma6₁ hAx hAy)
  · rw [lemma11₂_auxrl (by fin_cases · <;> simp_all) (by fin_cases · <;> simp_all)]
    apply (Matrix.isTotallyUnimodular_iff _).→ ((lemma6₁ hAx hAy).comp_rows Sum.inr)
  · rw [lemma11₂_auxr (by fin_cases · <;> simp_all)]
    apply (Matrix.isTotallyUnimodular_iff _).→ (lemma6₂ hAx hAy)
  · rw [lemma11₂_auxr (by fin_cases · <;> simp_all)]
    apply (Matrix.isTotallyUnimodular_iff _).→ (lemma6₂ hAx hAy)
  · rw [lemma11₂_auxrr (by fin_cases · <;> simp_all) (by fin_cases · <;> simp_all)]
    apply A₂.isTotallyUnimodular_iff.→ hA₂

/-- Compute the row vector for the outer product after pivoting outside of the outer product. -/
private noncomputable def Matrix.shortTableauPivotTheRow {X Y Y' R : Type} [DecidableEq Y'] [DivisionRing R]
    (B : Matrix X Y R) (r : X) (c' : Y') (g : Y' → Y) (x : Y' → R) (s : R) :
    Y' → R :=
  fun j : Y' => if j = c' then -s * x j else (B r (g c') * x j - B r (g j) * x c') / B r (g c')

private lemma Matrix.shortTableauPivot_outer {X Y X' Y' R : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Y'] [Field R]
    (B : Matrix X Y R) (r : X) (c' : Y') (f : X' → X) (g : Y' → Y) (hf : r ∉ f.range) (hg : g.Injective)
    (hBrc : B r (g c') = 1 ∨ B r (g c') = -1)
    (x : Y' → R) (y : X' → R) (hBfg : ∀ i j, B (f i) (g j) = y i * x j) :
    ∀ i : X', ∀ j : Y',
      (B.shortTableauPivot r (g c')) (f i) (g j) =
      y i * B.shortTableauPivotTheRow r c' g x (B r (g c')) j := by
  intro i j
  unfold shortTableauPivot Matrix.shortTableauPivotTheRow
  cases hBrc with
  | inl h1 =>
    if hj : j = c' then
      simp_all
    else
      have hgj : g j ≠ g c' := (hj <| hg ·)
      have hfi : f i ≠ r := (hf <| ⟨i, ·⟩)
      simp [*]
      ring
  | inr h9 =>
    if hj : j = c' then
      simp_all
    else
      have hgj : g j ≠ g c' := (hj <| hg ·)
      have hfi : f i ≠ r := (hf <| ⟨i, ·⟩)
      simp [*]
      ring

private lemma matrix2sumComposition_shortTableauPivot {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ ℚ) (x : Y₁ → ℚ) (A₂ : Matrix X₂ Y₂ ℚ) (y : X₂ → ℚ) {r : X₁} {c : Y₁} (hrc : A₁ r c = 1 ∨ A₁ r c = -1) :
    let B := matrix2sumComposition A₁ x A₂ y
    B.shortTableauPivot ◩r ◩c =
    matrix2sumComposition (A₁.shortTableauPivot r c) (B.shortTableauPivotTheRow ◩r c Sum.inl x (A₁ r c)) A₂ y := by
  intro B
  have hBA₁ : (B.shortTableauPivot ◩r ◩c).toBlocks₁₁ = A₁.shortTableauPivot r c
  · exact (B.submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective r c).symm
  have hBA₂ : (B.shortTableauPivot ◩r ◩c).toBlocks₂₂ = A₂
  · exact B.shortTableauPivot_submatrix_zero_external_row ◩r ◩c Sum.inr Sum.inr (by aesop) (by aesop) (by aesop)
  have hB0 : (B.shortTableauPivot ◩r ◩c).toBlocks₁₂ = 0
  · ext i j
    exact B.shortTableauPivot_zero r ◩c Sum.inl Sum.inr (by simp) (by simp [matrix2sumComposition, B]) i j
  have hBD :
    (B.shortTableauPivot ◩r ◩c).toBlocks₂₁ = Matrix.of (y · * Matrix.shortTableauPivotTheRow B ◩r c Sum.inl x (B ◩r ◩c) ·)
  · have := B.shortTableauPivot_outer ◩r c Sum.inr Sum.inl (by simp) Sum.inl_injective hrc x y
    aesop
  rw [←(B.shortTableauPivot ◩r ◩c).fromBlocks_toBlocks, hBA₁, hBA₂, hB0, hBD]
  have hBrc : B ◩r ◩c = A₁ r c
  · rfl
  simp [matrix2sumComposition, hBrc]
  ext
  simp [mul_comm]

lemma Matrix.submatrix_det_zero_of_not_injective_right {X Y Z R : Type} [Fintype Z] [DecidableEq Z] [CommRing R] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hg : ¬g.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [Function.not_injective_iff] at hg
  obtain ⟨i, j, hgij, hij⟩ := hg
  apply Matrix.det_zero_of_column_eq hij
  simp [hgij]

lemma Matrix.submatrix_det_zero_of_not_injective_left {X Y Z R : Type} [Fintype Z] [DecidableEq Z] [CommRing R] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hf : ¬f.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [←Matrix.det_transpose, Matrix.transpose_submatrix]
  exact A.transpose.submatrix_det_zero_of_not_injective_right hf

private lemma lemma12 {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α} {k : ℕ}
    (ih : ∀ {A₁ : Matrix X₁ Y₁ ℚ}, ∀ {x : Y₁ → ℚ}, ∀ {A₂ : Matrix X₂ Y₂ ℚ}, ∀ {y : X₂ → ℚ},
      (A₁ ⊟ ▬x).IsTotallyUnimodular → (▮y ◫ A₂).IsTotallyUnimodular → (matrix2sumComposition A₁ x A₂ y).IsPreTU k)
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hAx : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ A₂).IsTotallyUnimodular) :
    (matrix2sumComposition A₁ x A₂ y).IsPreTU k.succ := by
  cases k with
  | zero => exact lemma11₁ hAx hAy
  | succ n => cases n with
    | zero => exact lemma11₂ hAx hAy
    | succ k =>
      have hA₁ : A₁.IsTotallyUnimodular := hAx.comp_rows Sum.inl
      have hA₂ : A₂.IsTotallyUnimodular := hAy.comp_cols Sum.inr
      by_contra contr
      obtain ⟨f, g, hAfg⟩ := exists_submatrix_of_not_isPreTU contr
      wlog hf : f.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix2sumComposition A₁ x A₂ y).submatrix_det_zero_of_not_injective_left hf
      wlog hg : g.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix2sumComposition A₁ x A₂ y).submatrix_det_zero_of_not_injective_right hg
      -- now we show that all four blocks are part of the submatrix
      obtain ⟨i₁, x₁, hix₁⟩ : ∃ i₁ : Fin (k + 3), ∃ x₁ : X₁, f i₁ = ◩x₁
      · have isTU := lemma6₂ hAx hAy -- `D ◫ A₂` is TU
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix2sumComposition_eq_fromRows] at hAfg
        by_contra! hfX₁
        apply hAfg
        convert isTU (k + 3) (fn_of_sum_ne_inl hfX₁) g using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfX₁ i]
        rfl
      obtain ⟨i₂, x₂, hix₂⟩ : ∃ i₂ : Fin (k + 3), ∃ x₂ : X₂, f i₂ = ◪x₂
      · have isTU := hA₁.fromCols_zero Y₂ -- `A₁ ◫ 0` is TU
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix2sumComposition_eq_fromRows] at hAfg
        by_contra! hfX₂
        apply hAfg
        convert isTU (k + 3) (fn_of_sum_ne_inr hfX₂) g using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inr hfX₂ i]
        rfl
      obtain ⟨j₁, y₁, hjy₁⟩ : ∃ j₁ : Fin (k + 3), ∃ y₁ : Y₁, g j₁ = ◩y₁
      · have isTU := hA₂.zero_fromRows X₁ -- `0 ⊟ A₂` is TU
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix2sumComposition_eq_fromCols] at hAfg
        by_contra! hgY₁
        apply hAfg
        convert isTU (k + 3) f (fn_of_sum_ne_inl hgY₁) using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hgY₁ j]
        rfl
      obtain ⟨j₂, y₂, hjy₂⟩ : ∃ j₂ : Fin (k + 3), ∃ y₂ : Y₂, g j₂ = ◪y₂
      · have isTU := lemma6₁ hAx hAy -- `A₁ ⊟ D` is TU
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix2sumComposition_eq_fromCols] at hAfg
        by_contra! hgY₂
        apply hAfg
        convert isTU (k + 3) f (fn_of_sum_ne_inr hgY₂) using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inr hgY₂ j]
        rfl
      obtain ⟨j₀, y₀, hjy₀, hAxy0⟩ : ∃ j₀ : Fin (k + 3), ∃ y₀ : Y₁, g j₀ = ◩y₀ ∧ A₁ x₁ y₀ ≠ 0
      · by_contra! hgY₁ -- because the `i₁`th row cannot be all `0`s
        apply hAfg
        convert zero_in_signTypeCastRange
        apply Matrix.det_eq_zero_of_row_eq_zero i₁
        intro z
        rw [matrix2sumComposition_eq_fromRows, Matrix.submatrix_apply, hix₁, Matrix.fromRows_apply_inl]
        cases hgz : g z with
        | inl => exact hgY₁ z _ hgz
        | inr => simp
      have hAxy1 : A₁ x₁ y₀ = 1 ∨ A₁ x₁ y₀ = -1
      · obtain ⟨s, hs⟩ := hA₁.apply x₁ y₀
        cases s with
        | zero =>
          exfalso
          apply hAxy0
          exact hs.symm
        | pos =>
          left
          exact hs.symm
        | neg =>
          right
          exact hs.symm
      obtain ⟨_, _, -, -, impossible⟩ := corollary1 hAfg i₁ j₀ (by convert hAxy1 <;> simp [matrix2sumComposition, *])
      apply impossible
      rw [(matrix2sumComposition A₁ x A₂ y).submatrix_shortTableauPivot hf hg, Matrix.submatrix_submatrix,
        hix₁, hjy₀, matrix2sumComposition_shortTableauPivot A₁ x A₂ y hAxy1]
      apply ih _ hAy
      have hAxy0' : (A₁ ⊟ ▬x) ◩x₁ y₀ ≠ 0 := hAxy0
      convert hAx.shortTableauPivot hAxy0'
      ext i j
      cases i with
      | inl =>
        simp [Matrix.shortTableauPivot]
      | inr =>
        simp [Matrix.shortTableauPivot, Matrix.shortTableauPivotTheRow]
        if hj : j = y₀ then
          cases hAxy1 with
          | inl h1 => simp [hj, h1]
          | inr h9 => simp [hj, h9]
        else
          field_simp [hj]
          ring

lemma matrix2sumComposition_isTotallyUnimodular {α : Type} [DecidableEq α] {X₁ Y₁ X₂ Y₂ : Set α}
    {A₁ : Matrix X₁ Y₁ ℚ} {x : Y₁ → ℚ} {A₂ : Matrix X₂ Y₂ ℚ} {y : X₂ → ℚ}
    (hA₁ : (A₁ ⊟ ▬x).IsTotallyUnimodular) (hA₂ : (▮y ◫ A₂).IsTotallyUnimodular) :
    (matrix2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  induction k generalizing A₁ x A₂ y with
  | zero => simp [Matrix.IsPreTU]
  | succ _ ih => exact lemma12 ih hA₁ hA₂

lemma standardRepr2sumComposition_B {α : Type} [DecidableEq α] {S₁ S₂ : StandardRepr α Z2} {a : α}
    (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) :
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

lemma standardRepr2sumComposition_hasTuSigning {α : Type} [DecidableEq α] {S₁ S₂ : StandardRepr α Z2} {a : α}
    (ha : S₁.X ∩ S₂.Y = {a}) (hXY : S₂.X ⫗ S₁.Y) (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
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
theorem Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M M₁ M₂ : Matroid α}
    (hM : M.Is2sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply standardRepr2sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂
