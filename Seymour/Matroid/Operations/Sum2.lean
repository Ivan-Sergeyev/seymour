import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity

/-!
# Matroid 2-sum

Here we study the 2-sum of matroids (starting with the 2-sum of matrices).
-/

/-! ## Shorthands for convenience -/

private abbrev Eq._ₗ {α : Type} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : X :=
  ⟨a, Set.mem_of_mem_inter_left (ha.symm.subset rfl)⟩

private abbrev Eq._ᵣ {α : Type} {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : Y :=
  ⟨a, Set.mem_of_mem_inter_right (ha.symm.subset rfl)⟩

private abbrev Matrix.dropRow {α R : Type} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix (X \ {a}).Elem Y.Elem R :=
  A ∘ Set.diff_subset.elem

private abbrev Matrix.dropCol {α R : Type} {X Y : Set α} (A : Matrix X Y R) (a : α) :
    Matrix X.Elem (Y \ {a}).Elem R :=
  (A · ∘ Set.diff_subset.elem)

private abbrev Matrix.interRow {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : X ∩ Z = {a}) :
    Y.Elem → R :=
  A ha._ₗ

private abbrev Matrix.interCol {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    X.Elem → R :=
  (A · ha._ᵣ)

private abbrev Matrix.reglueRow {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : X ∩ Z = {a}) :
    Matrix ((X \ {a}).Elem ⊕ Unit) Y.Elem R :=
  A.dropRow a ⊟ ▬(A.interRow ha)

private abbrev Matrix.reglueCol {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    Matrix X.Elem (Unit ⊕ (Y \ {a}).Elem) R :=
  ▮(A.interCol ha) ◫ A.dropCol a

private lemma Matrix.reglueRow_eq {α R : Type} [CommRing R] {X Y Z : Set α} {A : Matrix X Y R} {a : α} (ha : X ∩ Z = {a}) :
    A.reglueRow ha = A.submatrix (·.casesOn Set.diff_subset.elem ↓ha._ₗ) id := by
  aesop

private lemma Matrix.reglueCol_eq {α R : Type} {X Y Z : Set α} (A : Matrix X Y R) {a : α} (ha : Z ∩ Y = {a}) :
    A.reglueCol ha = A.submatrix id (·.casesOn ↓ha._ᵣ Set.diff_subset.elem) := by
  aesop

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


/-! ## Definition -/

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrixSum2 {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 (c ⊗ r) Aᵣ

/-- `StandardRepr`-level 2-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum2 {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {x y : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  open scoped Classical in if
    Sₗ.B.interRow hXX ≠ 0 ∧ Sᵣ.B.interCol hYY ≠ 0
  then
    some ⟨
      -- row indices
      (Sₗ.X \ {x}) ∪ Sᵣ.X,
      -- col indices
      Sₗ.Y ∪ (Sᵣ.Y \ {y}),
      -- row and col indices are disjoint
      by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
         exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right,
            Sᵣ.hXY.disjoint_sdiff_right⟩⟩,
      -- standard representation matrix
      (matrixSum2 (Sₗ.B.dropRow x) (Sₗ.B.interRow hXX) (Sᵣ.B.dropCol y) (Sᵣ.B.interCol hYY)).toMatrixUnionUnion,
      -- decidability of row indices
      inferInstance,
      -- decidability of col indices
      inferInstance⟩
  else
    none

/-- Binary matroid `M` is a result of 2-summing `Mₗ` and `Mᵣ` in some way. -/
def Matroid.Is2sumOf {α : Type} [DecidableEq α] (M : Matroid α) (Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ x y : α,
  ∃ hXX : Sₗ.X ∩ Sᵣ.X = {x},
  ∃ hYY : Sₗ.Y ∩ Sᵣ.Y = {y},
  ∃ hXY : Sₗ.X ⫗ Sᵣ.Y,
  ∃ hYX : Sₗ.Y ⫗ Sᵣ.X,
  standardReprSum2 hXX hYY hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ


/-! ## Specifics about pivoting for the proof of 2-sum regularity -/

private abbrev shortTableauPivotOtherRow {Y Y' R : Type} [DecidableEq Y'] [DivisionRing R]
    (p : Y → R) (r : Y' → R) (g : Y' → Y) (y' : Y') : Y' → R :=
  -- `p` is the pivot row; `r` is the other row; `g` is a map from the columns of `r` to the columns of `p`
  (▬(p ∘ g) ⊟ ▬r).shortTableauPivot ◩() y' ◪()

private lemma Matrix.shortTableauPivot_otherRow_eq {X Y Y' R : Type}
    [Field R] [DecidableEq X] [DecidableEq Y] [DecidableEq Y']
    (A : Matrix X Y R) (x : X) (y' : Y') {i : X} (hix : i ≠ x) {g : Y' → Y} (hg : g.Injective) :
    (A.shortTableauPivot x (g y')) i ∘ g = shortTableauPivotOtherRow (A x) (A i ∘ g) g y' := by
  ext j'
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.replicateRow_apply, Matrix.of_apply,
    Matrix.shortTableauPivot_eq, shortTableauPivotOtherRow, Function.comp_apply, one_div, reduceCtorEq, hix]
  if hj' : j' = y' then
    simp only [hj']
  else
    simp only [hj', ↓reduceIte, ite_eq_right_iff]
    exact (False.elim <| hj' <| hg ·)

private lemma Matrix.shortTableauPivot_outer {X Y X' Y' F : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Y'] [Field F]
    (A : Matrix X Y F) (x : X) (y' : Y') (f : X' → X) (g : Y' → Y) (hf : x ∉ f.range) (hg : g.Injective)
    (r : Y' → F) (c : X' → F) (hBfg : A.submatrix f g = (c ⊗ r)) :
    (A.shortTableauPivot x (g y')).submatrix f g = (c ⊗ shortTableauPivotOtherRow (A x) r g y') := by
  ext i j
  have hfig : A (f i) ∘ g = (c i * r ·) := congr_fun hBfg i
  have hAgfg := hfig ▸ Function.comp_apply ▸
      congr_fun (A.shortTableauPivot_otherRow_eq x y' (ne_of_mem_of_not_mem (Set.mem_range_self i) hf) hg) j
  rw [Matrix.submatrix_apply, hAgfg]
  by_cases hj : j = y'
  <;> simp [shortTableauPivotOtherRow, Matrix.shortTableauPivot_eq, hj]
  <;> ring

private lemma matrixSum2_shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (c : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} :
    (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j =
    matrixSum2 (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c :=
  ((matrixSum2 Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j).fromBlocks_toBlocks ▸
   (matrixSum2 (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c).fromBlocks_toBlocks ▸
    Matrix.fromBlocks_inj.← ⟨
    ((matrixSum2 Aₗ r Aᵣ c).submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm,
    Matrix.ext ((matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_zero i ◩j Sum.inl Sum.inr
      (by simp) (by simp [matrixSum2])),
    (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_outer ◩i j Sum.inr Sum.inl (by simp) Sum.inl_injective r c rfl,
    (matrixSum2 Aₗ r Aᵣ c).shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr
      (by simp) (by simp) ↓rfl⟩

private lemma Matrix.shortTableauPivot_adjoinRow_eq {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (x : X) (y : Y) (j : Y) :
    (▬A x ⊟ ▬r).shortTableauPivot (◩()) y (◪()) j = (A ⊟ ▬r).shortTableauPivot (◩x) y (◪()) j := by
  by_cases hj : j = y <;> simp [hj, Matrix.shortTableauPivot, Matrix.longTableauPivot]

private lemma Matrix.IsTotallyUnimodular.fromRows_pivot {α : Type} [DecidableEq α] {X Y : Set α}
    {A : Matrix X Y ℚ} {r : Y → ℚ} (hAr : (A ⊟ ▬r).IsTotallyUnimodular) {x : X} {y : Y} (hAxy : A x y ≠ 0) :
    ((A.shortTableauPivot x y) ⊟ ▬(shortTableauPivotOtherRow (A x) r id y)).IsTotallyUnimodular := by
  have hArxy : (A ⊟ ▬r) ◩x y ≠ 0 := hAxy
  convert hAr.shortTableauPivot hArxy
  exact Matrix.ext (fun i : X ⊕ Unit => fun j : Y => (i.casesOn (fun iₗ : X =>
      congr_fun₂ ((A ⊟ ▬r).submatrix_shortTableauPivot Sum.inl_injective Function.injective_id x y) iₗ j)
    ↓(A.shortTableauPivot_adjoinRow_eq r x y j)))


/-! ## Total unimodularity after adjoining an outer product -/

private lemma Matrix.IsTotallyUnimodular.fromCols_pnz {X Y : Type} [DecidableEq Y] {A : Matrix X Y ℚ} {c : X → ℚ}
    (hAc : (A ◫ ▮c).IsTotallyUnimodular) :
    (A ◫ ▮c ◫ ▮(-c) ◫ ▮0).IsTotallyUnimodular := by
  have hAcc : (A ◫ ▮c ◫ ▮c).IsTotallyUnimodular
  · convert hAc.comp_cols (Sum.casesOn · id Sum.inr)
    ext (_|_) <;> simp
  convert (hAcc.mul_cols (show ∀ j, (·.casesOn 1 (-1)) j ∈ SignType.cast.range by rintro (_|_) <;> simp)).fromCols_zero Unit
  ext _ (_|_) <;> simp

private lemma Matrix.IsTotallyUnimodular.fromCols_outer {X Yᵣ Y' : Type} [DecidableEq Yᵣ]
    {A : Matrix X Yᵣ ℚ} {r : Y' → ℚ} {c : X → ℚ}
    (hAc : (A ◫ ▮c).IsTotallyUnimodular) (hr : ∀ j' : Y', r j' ∈ SignType.cast.range) :
    (A ◫ (c ⊗ r)).IsTotallyUnimodular := by
  convert hAc.fromCols_pnz.comp_cols
    (fun j : Yᵣ ⊕ Y' => j.casesOn (Sum.inl ∘ Sum.inl ∘ Sum.inl) (fun j : Y' =>
      if h0 : r j = 0 then ◪()
      else if h1 : r j = 1 then ◩◩◪()
      else if h9 : r j = -1 then ◩◪()
      else False.elim (by obtain ⟨s, hs⟩ := hr j; cases s <;> simp_all)
    ))
  ext (_ | j)
  · simp
  · obtain ⟨s, hs⟩ := hr j
    simp only [Matrix.fromCols_apply_inr, Matrix.replicateCol_zero, Function.comp_apply]
    split_ifs
    all_goals try simp [*]
    exfalso
    cases s <;> simp_all

private lemma matrixSum2_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] [DecidableEq Yₗ]
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    ((c ⊗ r) ◫ Aᵣ).IsTotallyUnimodular :=
  (hAc.fromCols_comm.fromCols_outer (hAr.apply ◪())).fromCols_comm


/-! ## Proof of regularity of the 2-sum -/

private lemma matrixSum2_isPartiallyUnimodular_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (matrixSum2 Aₗ r Aᵣ c).IsPartiallyUnimodular 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact (hAr.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAc.apply iᵣ ◩()) (hAr.apply ◪() jₗ)
    | inr jᵣ => exact (hAc.comp_cols Sum.inr).apply iᵣ jᵣ

private lemma matrixSum2_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (matrixSum2 Aₗ r Aᵣ c).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular]
  intro k
  cases k with
  | zero => simp [Matrix.IsPartiallyUnimodular]
  | succ m => induction m generalizing Aₗ r Aᵣ c with
    | zero => exact matrixSum2_isPartiallyUnimodular_1 hAr hAc
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      · exact (matrixSum2 Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_rows g hf ▸ zero_in_signTypeCastRange
      wlog hg : g.Injective
      · exact (matrixSum2 Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_cols f hg ▸ zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · push_neg at hfₗ
        convert (matrixSum2_bottom_isTotallyUnimodular hAr hAc).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext
        rewrite [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ]
        rfl
      obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((matrixSum2 Aₗ r Aᵣ c).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
        intro j
        cases hgj : g j with
        | inl => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ hgₗ j _ hgj
        | inr => exact Matrix.submatrix_apply .. ▸ hgj ▸ hfiₗ ▸ rfl
      obtain ⟨j₀, y₀, hgj₀, hAxy0⟩ := hgₗ
      have hAxy1 : Aₗ xₗ y₀ = 1 ∨ Aₗ xₗ y₀ = -1
      · obtain ⟨s, hs⟩ := (hAr.comp_rows Sum.inl).apply xₗ y₀
        cases s with
        | zero => exact (hAxy0 hs.symm).elim
        | pos => exact Or.inl hs.symm
        | neg => exact Or.inr hs.symm
      have hArAc1 : ((matrixSum2 Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = 1 ∨
                    ((matrixSum2 Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = -1
      · rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
        exact hAxy1
      obtain ⟨f', g', hArAc⟩ := ((matrixSum2 Aₗ r Aᵣ c).submatrix f g).abs_det_eq_shortTableauPivot_submatrix_abs_det hArAc1
      rw [in_signTypeCastRange_iff_abs, hArAc, (matrixSum2 Aₗ r Aᵣ c).submatrix_shortTableauPivot hf hg iₗ j₀,
        hfiₗ, hgj₀, Matrix.submatrix_submatrix, matrixSum2_shortTableauPivot Aₗ r Aᵣ c,
        ←in_signTypeCastRange_iff_abs]
      exact ih (hAr.fromRows_pivot hAxy0) hAc (f ∘ f') (g ∘ g')

private lemma standardReprSum2_X_x {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = {x}} {hy : Sₗ.Y ∩ Sᵣ.Y = {y}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.X = (Sₗ.X \ {x}) ∪ Sᵣ.X := by
  simp_rw [standardReprSum2, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm

lemma standardReprSum2_X {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = {x}} {hy : Sₗ.Y ∩ Sᵣ.Y = {y}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.X = Sₗ.X ∪ Sᵣ.X := by
  rw [standardReprSum2_X_x hS]
  ext a
  if a = x then
    simp [*, singleton_inter_in_right hx]
  else
    simp [*]

private lemma standardReprSum2_Y_y {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = {x}} {hy : Sₗ.Y ∩ Sᵣ.Y = {y}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ (Sᵣ.Y \ {y}) := by
  simp_rw [standardReprSum2, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm

lemma standardReprSum2_Y {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = {x}} {hy : Sₗ.Y ∩ Sᵣ.Y = {y}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ Sᵣ.Y := by
  rw [standardReprSum2_Y_y hS]
  ext a
  if a = y then
    simp [*, singleton_inter_in_left hy]
  else
    simp [*]

lemma standardReprSum2_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ S : StandardRepr α Z2} {x y : α}
    {hx : Sₗ.X ∩ Sᵣ.X = {x}} {hy : Sₗ.Y ∩ Sᵣ.Y = {y}} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) (hS : standardReprSum2 hx hy hXY hYX = some S) :
    S.B.HasTuSigning := by
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  have hSX : S.X = Sₗ.X \ {x} ∪ Sᵣ.X := standardReprSum2_X_x hS
  have hSY : S.Y = Sₗ.Y ∪ Sᵣ.Y \ {y} := standardReprSum2_Y_y hS
  have hSB : S.B = (matrixSum2 (Sₗ.B.dropRow x) (Sₗ.B.interRow hx) (Sᵣ.B.dropCol y) (Sᵣ.B.interCol hy)).toMatrixElemElem hSX hSY
  · simp_rw [standardReprSum2, Option.ite_none_right_eq_some] at hS
    aesop
  use
    (matrixSum2 (Bₗ.dropRow x) (Bₗ.interRow hx) (Bᵣ.dropCol y) (Bᵣ.interCol hy)).toMatrixElemElem hSX hSY,
    (matrixSum2_isTotallyUnimodular (hBₗ.reglueRow hx) (hBᵣ.reglueCol hy)).toMatrixElemElem hSX hSY
  rw [hSB]
  intro i j
  simp only [Matrix.toMatrixElemElem_apply]
  exact (hSX ▸ i).toSum.casesOn
    (fun iₗ => (hSY ▸ j).toSum.casesOn (hBBₗ (Set.diff_subset.elem iₗ)) ↓abs_zero)
    (fun iᵣ => (hSY ▸ j).toSum.casesOn (abs_mul_eq_zmod_cast (hBBᵣ iᵣ hy._ᵣ) <| hBBₗ hx._ₗ ·) (hBBᵣ iᵣ <| Set.diff_subset.elem ·))

/-- Any 2-sum of regular matroids is a regular matroid.
    This is part two (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is2sumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is2sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, _, _, _, _, _, _, _, _, hS, _, _, rfl, rfl, rfl⟩ := hM
  have : Finite S.X := standardReprSum2_X hS ▸ Finite.Set.finite_union ..
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum2_hasTuSigning hMₗ hMᵣ hS

/--
info: 'Matroid.Is2sumOf.isRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matroid.Is2sumOf.isRegular
-- TODO document in `Seymour.lean` and remove here
