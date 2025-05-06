import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity
import Seymour.Matrix.Determinants
import Seymour.Matrix.PreTUness


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
  let Aₗ : Matrix (Sₗ.X \ {a}).Elem Sₗ.Y.Elem Z2 := Sₗ.B ∘ Set.diff_subset.elem -- the top submatrix of `Bₗ`
  let Aᵣ : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {a}).Elem Z2 := (Sᵣ.B · ∘ Set.diff_subset.elem) -- the right submatrix of `Bᵣ`
  let x : Sₗ.Y.Elem → Z2 := Sₗ.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `Bₗ`
  let y : Sᵣ.X.Elem → Z2 := (Sᵣ.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `Bᵣ`
  ⟨
    ⟨
      (Sₗ.X \ {a}) ∪ Sᵣ.X,
      Sₗ.Y ∪ (Sᵣ.Y \ {a}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_inter_both_wo ha, Sᵣ.hXY.disjoint_sdiff_right⟩⟩,
      (matrix2sumComposition Aₗ x Aᵣ y).toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

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

infixl:63 " ⊟ " => Matrix.fromRows
infixl:63 " ◫ " => Matrix.fromCols
notation:64 "▬"r:81 => Matrix.replicateRow Unit r
notation:64 "▮"c:81 => Matrix.replicateCol Unit c

lemma Matrix.IsTotallyUnimodular.duplicate_last_row {X Y : Type} {Aₗ : Matrix X Y ℚ} {x : Y → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) :
    (Aₗ ⊟ ▬x ⊟ ▬x).IsTotallyUnimodular := by
  convert hAx.comp_rows (Sum.casesOn · id Sum.inr)
  aesop

private lemma Matrix.IsTotallyUnimodular.aux190 {α : Type} [DecidableEq α] {Xₗ Yₗ : Set α} {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) :
    (Aₗ ⊟ ▬x ⊟ ▬(-x) ⊟ ▬0).IsTotallyUnimodular := by
  rw [Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff]
  intro k f g hf hg
  have almost := hAx.duplicate_last_row k f g hf hg
  if last_row : ∃ i : Fin k, f i = ◪() then
    apply in_signTypeCastRange_of_neg_one_mul
    convert almost
    obtain ⟨i, hi⟩ := last_row
    have flipped : (Aₗ ⊟ ▬x ⊟ ▬(-x)) = (Aₗ ⊟ ▬x ⊟ ▬x).updateRow ◪() (-x)
    · aesop
    have bubbled : ((Aₗ ⊟ ▬x ⊟ ▬x).updateRow ◪() (-x)).submatrix f g = ((Aₗ ⊟ ▬x ⊟ ▬x).submatrix f g).updateRow i ((-x) ∘ g)
    · ext r
      if hr : r = i then
        simp [hr, hi]
      else
        have hfr : f r ≠ ◪() := (hr <| hf <| ·.trans hi.symm)
        simp [hr, hfr]
    rw [flipped, bubbled, ←((Aₗ ⊟ ▬x ⊟ ▬x).submatrix f g).det_updateRow_smul i (-1) ((-x) ∘ g)]
    convert_to (((Aₗ ⊟ ▬x ⊟ ▬x).submatrix f g).updateRow i (x ∘ g)).det = ((Aₗ ⊟ ▬x ⊟ ▬x).submatrix f g).det
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

private lemma matrix2sumComposition_isPreTU_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {x : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {y : Xᵣ → ℚ}
    (hAx : (Aₗ ⊟ ▬x).IsTotallyUnimodular) (hAy : (▮y ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ x Aᵣ y).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  have hAₗ : Aₗ.IsTotallyUnimodular := hAx.comp_rows Sum.inl
  have hAᵣ : Aᵣ.IsTotallyUnimodular := hAy.comp_cols Sum.inr
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact hAₗ.apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAy.apply iᵣ ◩()) (hAx.apply ◪() jₗ)
    | inr jᵣ => exact hAᵣ.apply iᵣ jᵣ

/-- The result of the vector `v` after pivoting on `j`th element in the row `u` and restriction. -/
noncomputable def shortTableauPivotOuterRow {Y Y' R : Type} [DecidableEq Y'] [DivisionRing R]
    (u : Y → R) (j : Y') (g : Y' → Y) (v : Y' → R) : Y' → R :=
  fun j' : Y' => if j' = j then -v j' / u (g j) else (u (g j) * v j' - u (g j') * v j) / u (g j)

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
  · exact B.shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr (by simp) (by simp) (fun _ => rfl)
  rw [←(B.shortTableauPivot ◩i ◩j).fromBlocks_toBlocks, hBAₗ, hBAᵣ, hB0, hBD]
  rfl

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
      have hAₗ : Aₗ.IsTotallyUnimodular := hAx.comp_rows Sum.inl
      have hAᵣ : Aᵣ.IsTotallyUnimodular := hAy.comp_cols Sum.inr
      by_contra contr
      obtain ⟨f, g, hAfg⟩ := exists_submatrix_of_not_isPreTU contr
      wlog hf : f.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_left hf
      wlog hg : g.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix2sumComposition Aₗ x Aᵣ y).submatrix_det_zero_of_not_injective_right hg
      obtain ⟨iₗ, xₗ, hixₗ⟩ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · have isTU := matrix2sumComposition_bottom_isTotallyUnimodular hAx hAy -- `D ◫ Aᵣ` is TU
        rw [matrix2sumComposition_eq_fromRows] at hAfg
        by_contra! hfXₗ
        apply hAfg
        convert isTU.det (fn_of_sum_ne_inl hfXₗ) g using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfXₗ i]
        rfl
      obtain ⟨j₀, y₀, hjy₀, hAxy0⟩ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · by_contra! hgYₗ -- because the `iₗ`th row cannot be all `0`s
        apply hAfg
        convert zero_in_signTypeCastRange
        apply Matrix.det_eq_zero_of_row_eq_zero iₗ
        intro z
        rw [matrix2sumComposition_eq_fromRows, Matrix.submatrix_apply, hixₗ, Matrix.fromRows_apply_inl]
        cases hgz : g z with
        | inl => exact hgYₗ z _ hgz
        | inr => simp
      have hAxy1 : Aₗ xₗ y₀ = 1 ∨ Aₗ xₗ y₀ = -1
      · obtain ⟨s, hs⟩ := hAₗ.apply xₗ y₀
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

lemma standardRepr2sumComposition_B {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {a : α}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) :
    ∃ haXₗ : a ∈ Sₗ.X, ∃ haYᵣ : a ∈ Sᵣ.Y,
      (standardRepr2sumComposition ha hXY).fst.B =
      (matrix2sumComposition
        (Sₗ.B ∘ Set.diff_subset.elem)
        (Sₗ.B ⟨a, haXₗ⟩)
        (Sᵣ.B · ∘ Set.diff_subset.elem)
        (Sᵣ.B · ⟨a, haYᵣ⟩)
      ).toMatrixUnionUnion :=
  have haXY : a ∈ Sₗ.X ∩ Sᵣ.Y := ha ▸ rfl
  ⟨Set.mem_of_mem_inter_left haXY, Set.mem_of_mem_inter_right haXY, rfl⟩

lemma standardRepr2sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {a : α}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr2sumComposition ha hXY).fst.B.HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  obtain ⟨haXₗ, haYᵣ, hB⟩ := standardRepr2sumComposition_B ha hXY
  let x' : Sₗ.Y.Elem → ℚ := Bₗ ⟨a, haXₗ⟩
  let y' : Sᵣ.X.Elem → ℚ := (Bᵣ · ⟨a, haYᵣ⟩)
  let Aₗ' : Matrix (Sₗ.X \ {a}).Elem Sₗ.Y.Elem ℚ := Bₗ ∘ Set.diff_subset.elem
  let Aᵣ' : Matrix Sᵣ.X.Elem (Sᵣ.Y \ {a}).Elem ℚ := (Bᵣ · ∘ Set.diff_subset.elem)
  have hAₗ :
    ∀ i : (Sₗ.X \ {a}).Elem, ∀ j : Sₗ.Y.Elem,
      |Aₗ' i j| = (Sₗ.B (Set.diff_subset.elem i) j).val
  · intro i j
    exact hBBₗ (Set.diff_subset.elem i) j
  have hAᵣ :
    ∀ i : Sᵣ.X.Elem, ∀ j : (Sᵣ.Y \ {a}).Elem,
      |Aᵣ' i j| = (Sᵣ.B i (Set.diff_subset.elem j)).val
  · intro i j
    exact hBBᵣ i (Set.diff_subset.elem j)
  have hx' : ∀ j, |x' j| = (Sₗ.B ⟨a, haXₗ⟩ j).val
  · intro j
    exact hBBₗ ⟨a, haXₗ⟩ j
  have hy' : ∀ i, |y' i| = (Sᵣ.B i ⟨a, haYᵣ⟩).val
  · intro i
    exact hBBᵣ i ⟨a, haYᵣ⟩
  let B' := matrix2sumComposition Aₗ' x' Aᵣ' y' -- the signing is obtained using the same function but for `ℚ`
  use B'.toMatrixUnionUnion
  constructor
  · apply Matrix.IsTotallyUnimodular.toMatrixUnionUnion
    apply matrix2sumComposition_isTotallyUnimodular
    · convert hBₗ.comp_rows
        (fun i : (Sₗ.X \ {a}).Elem ⊕ Unit => i.casesOn Set.diff_subset.elem (fun _ => ⟨a, haXₗ⟩))
      aesop
    · convert hBᵣ.comp_cols
        (fun j : Unit ⊕ (Sᵣ.Y \ {a}).Elem => j.casesOn (fun _ => ⟨a, haYᵣ⟩) Set.diff_subset.elem)
      aesop
  · intro i j
    simp only [hB, Matrix.toMatrixUnionUnion, Function.comp_apply]
    cases hi : i.toSum with
    | inl iₗ =>
      cases j.toSum with
      | inl jₗ =>
        specialize hAₗ iₗ jₗ
        simp_all [B']
      | inr jᵣ =>
        simp_all [B']
    | inr iᵣ =>
      cases hj : j.toSum with
      | inl jₗ =>
        simp only [Matrix.fromBlocks_apply₂₁, B', hx', hy', abs_mul]
        apply Z2val_toRat_mul_Z2val_toRat
      | inr jᵣ =>
        specialize hAᵣ iᵣ jᵣ
        simp_all [x', y', Aₗ', Aᵣ', B']

/-- Any 2-sum of regular matroids is a regular matroid.
    This is the middle of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is2sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr2sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
