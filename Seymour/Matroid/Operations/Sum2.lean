import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity


-- ## Shorthands for convenience

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


-- ## Definition

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev matrix2sumComposition {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 (c · * r ·) Aᵣ

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


-- ## Specifics about pivoting for the proof of 2-sum regularity

-- `p` is the pivot row; `r` is the other row; `g` is a map from the columns of `r` to the columns of `p`
private abbrev shortTableauPivotOtherRow {Y Y' R : Type} [DecidableEq Y'] [DivisionRing R]
    (p : Y → R) (r : Y' → R) (g : Y' → Y) (y' : Y') : Y' → R :=
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
    (r : Y' → F) (c : X' → F) (hBfg : A.submatrix f g = (c · * r ·)) :
    (A.shortTableauPivot x (g y')).submatrix f g = (c · * (shortTableauPivotOtherRow (A x) r g y') ·) := by
  ext i j
  have hfig : A (f i) ∘ g = (c i * r ·) := congr_fun hBfg i
  have hAgfg := hfig ▸ Function.comp_apply ▸
      congr_fun (A.shortTableauPivot_otherRow_eq x y' (ne_of_mem_of_not_mem (Set.mem_range_self i) hf) hg) j
  rw [Matrix.submatrix_apply, hAgfg]
  by_cases hj : j = y'
  <;> simp [shortTableauPivotOtherRow, Matrix.shortTableauPivot_eq, hj]
  <;> ring

private lemma matrix2sumComposition_shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (c : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} :
    (matrix2sumComposition Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j =
    matrix2sumComposition (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c :=
  ((matrix2sumComposition Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j).fromBlocks_toBlocks ▸
   (matrix2sumComposition (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c).fromBlocks_toBlocks ▸
    Matrix.fromBlocks_inj.← ⟨
    ((matrix2sumComposition Aₗ r Aᵣ c).submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm,
    Matrix.ext ((matrix2sumComposition Aₗ r Aᵣ c).shortTableauPivot_zero i ◩j Sum.inl Sum.inr
      (by simp) (by simp [matrix2sumComposition])),
    (matrix2sumComposition Aₗ r Aᵣ c).shortTableauPivot_outer ◩i j Sum.inr Sum.inl (by simp) Sum.inl_injective r c rfl,
    (matrix2sumComposition Aₗ r Aᵣ c).shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr
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
      congr_fun (congr_fun (((A ⊟ ▬r).submatrix_shortTableauPivot Sum.inl_injective Function.injective_id x y)) iₗ) j)
    ↓(A.shortTableauPivot_adjoinRow_eq r x y j)))

private lemma Matrix.shortTableauPivot_abs_det_eq_submatrix_abs_det {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {k : ℕ} (A : Matrix (Fin k.succ) (Fin k.succ) F) {i j : Fin k.succ} (hAij : A i j = 1 ∨ A i j = -1) :
    ∃ f : Fin k → Fin k.succ, ∃ g : Fin k → Fin k.succ, f.Injective ∧ g.Injective ∧
      |A.det| = |((A.shortTableauPivot i j).submatrix f g).det| := by
  have hAij0 : A i j ≠ 0
  · cases hAij with
    | inl h1 => exact ne_zero_of_eq_one h1
    | inr h9 => simp [h9]
  obtain ⟨f, g, hf, hg, hAfg⟩ := shortTableauPivot_submatrix_det_abs_eq_div hAij0
  have hAij_abs : |A i j| = 1
  · cases hAij with
    | inl h1 => rw [h1, abs_one]
    | inr h9 => rw [h9, abs_neg, abs_one]
  rw [hAij_abs, div_one] at hAfg
  exact ⟨f, g, hf, hg, hAfg.symm⟩


-- ## Total unimodularity after adjoining an outer product

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
    (A ◫ (c · * r ·)).IsTotallyUnimodular := by
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

private lemma matrix2sumComposition_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] [DecidableEq Yₗ]
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    ((c · * r ·) ◫ Aᵣ).IsTotallyUnimodular :=
  (hAc.fromCols_comm.fromCols_outer (hAr.apply ◪())).fromCols_comm


-- ## Proof of regularity of the 2-sum

private lemma matrix2sumComposition_isPartiallyUnimodular_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ r Aᵣ c).isPartiallyUnimodular 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact (hAr.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAc.apply iᵣ ◩()) (hAr.apply ◪() jₗ)
    | inr jᵣ => exact (hAc.comp_cols Sum.inr).apply iᵣ jᵣ

private lemma matrix2sumComposition_isTotallyUnimodular {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (matrix2sumComposition Aₗ r Aᵣ c).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_isPartiallyUnimodular]
  intro k
  cases k with
  | zero => simp [Matrix.isPartiallyUnimodular]
  | succ m => induction m generalizing Aₗ r Aᵣ c with
    | zero => exact matrix2sumComposition_isPartiallyUnimodular_1 hAr hAc
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      · exact (matrix2sumComposition Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_rows g hf ▸ zero_in_signTypeCastRange
      wlog hg : g.Injective
      · exact (matrix2sumComposition Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_cols f hg ▸ zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · push_neg at hfₗ
        convert (matrix2sumComposition_bottom_isTotallyUnimodular hAr hAc).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext
        rewrite [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ]
        rfl
      obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((matrix2sumComposition Aₗ r Aᵣ c).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
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
      have hArAc1 : ((matrix2sumComposition Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = 1 ∨
                    ((matrix2sumComposition Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = -1
      · rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
        exact hAxy1
      obtain ⟨f', g', -, -, hArAc⟩ :=
        ((matrix2sumComposition Aₗ r Aᵣ c).submatrix f g).shortTableauPivot_abs_det_eq_submatrix_abs_det hArAc1
      rw [in_signTypeCastRange_iff_abs, hArAc, (matrix2sumComposition Aₗ r Aᵣ c).submatrix_shortTableauPivot hf hg iₗ j₀,
        hfiₗ, hgj₀, Matrix.submatrix_submatrix, matrix2sumComposition_shortTableauPivot Aₗ r Aᵣ c,
        ←in_signTypeCastRange_iff_abs]
      exact ih (hAr.fromRows_pivot hAxy0) hAc (f ∘ f') (g ∘ g')

lemma standardRepr2sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2} {a : α}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hXY : Sᵣ.X ⫗ Sₗ.Y) (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr2sumComposition ha hXY).fst.B.HasTuSigning :=
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  ⟨_, (matrix2sumComposition_isTotallyUnimodular (hBₗ.reglueRow ha) (hBᵣ.reglueCol ha)).toMatrixUnionUnion,
    (fun i j =>
      show
        |((matrix2sumComposition (Bₗ.dropRow a) (Bₗ.interRow ha) (Bᵣ.dropCol a) (Bᵣ.interCol ha) ∘ _) i ∘ _) j| =
        ZMod.val (((_ ∘ _) i ∘ _) j)
      from Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸
        i.toSum.casesOn
          (fun iₗ => j.toSum.casesOn (hBBₗ (Set.diff_subset.elem iₗ)) ↓rfl)
          (fun iᵣ => j.toSum.casesOn
            (fun jₗ => Z2val_toRat_mul_Z2val_toRat (Sᵣ.B.interCol ha iᵣ) (Sₗ.B.interRow ha jₗ) ▸
                hBBₗ ha._ₗ jₗ ▸ hBBᵣ iᵣ ha._ᵣ ▸ abs_mul (Bᵣ.interCol ha iᵣ) (Bₗ.interRow ha jₗ))
            (hBBᵣ iᵣ <| Set.diff_subset.elem ·)))⟩

instance Matroid.Is2sumOf.finS {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} (hM : M.Is2sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  apply Finite.Set.finite_union

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
