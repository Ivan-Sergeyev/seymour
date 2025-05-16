import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity
import Seymour.Matrix.Determinants
import Seymour.Matrix.PreTUness


-- ## Convenient API

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

-- ## 2-sum of matrices

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix.twoSum {R : Type} [Semiring R] {Xₗ Yₗ Xᵣ Yᵣ : Type}
    (Aₗ : Matrix Xₗ Yₗ R) (r : Yₗ → R) (Aᵣ : Matrix Xᵣ Yᵣ R) (c : Xᵣ → R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 (c · * r ·) Aᵣ


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

private lemma Matrix.twoSum_shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Type}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r : Yₗ → ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (c : Xᵣ → ℚ) {i : Xₗ} {j : Yₗ} :
    (Matrix.twoSum Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j =
    Matrix.twoSum (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c :=
  ((Matrix.twoSum Aₗ r Aᵣ c).shortTableauPivot ◩i ◩j).fromBlocks_toBlocks ▸
   (Matrix.twoSum (Aₗ.shortTableauPivot i j) (shortTableauPivotOtherRow (Aₗ i) r id j) Aᵣ c).fromBlocks_toBlocks ▸
    Matrix.fromBlocks_inj.← ⟨
    ((Matrix.twoSum Aₗ r Aᵣ c).submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm,
    Matrix.ext ((Matrix.twoSum Aₗ r Aᵣ c).shortTableauPivot_zero i ◩j Sum.inl Sum.inr
      (by simp) (by simp [Matrix.twoSum])),
    (Matrix.twoSum Aₗ r Aᵣ c).shortTableauPivot_outer ◩i j Sum.inr Sum.inl (by simp) Sum.inl_injective r c rfl,
    (Matrix.twoSum Aₗ r Aᵣ c).shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr
      (by simp) (by simp) ↓rfl⟩

private lemma Matrix.shortTableauPivot_adjoinRow_eq {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y ℚ) (r : Y → ℚ) (x : X) (y : Y) (j : Y) :
    (▬A x ⊟ ▬r).shortTableauPivot (◩()) y (◪()) j = (A ⊟ ▬r).shortTableauPivot (◩x) y (◪()) j := by
  by_cases hj : j = y <;> simp [hj, Matrix.shortTableauPivot, Matrix.longTableauPivot]

private lemma Matrix.IsTotallyUnimodular.fromRows_pivot {α : Type} {X Y : Set α} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X Y ℚ} {r : Y → ℚ} (hAr : (A ⊟ ▬r).IsTotallyUnimodular) {x : X} {y : Y} (hAxy : A x y ≠ 0) :
    ((A.shortTableauPivot x y) ⊟ ▬(shortTableauPivotOtherRow (A x) r id y)).IsTotallyUnimodular := by
  have hArxy : (A ⊟ ▬r) ◩x y ≠ 0 := hAxy
  convert hAr.shortTableauPivot hArxy
  exact Matrix.ext (fun i : X ⊕ Unit => fun j : Y => (i.casesOn (fun iₗ : X =>
      congr_fun (congr_fun (((A ⊟ ▬r).submatrix_shortTableauPivot Sum.inl_injective Function.injective_id x y)) iₗ) j)
    ↓(A.shortTableauPivot_adjoinRow_eq r x y j)))

private lemma Matrix.shortTableauPivot_abs_det_eq_submatrix_abs_det {F : Type} [LinearOrderedField F] {k : ℕ}
    (A : Matrix (Fin k.succ) (Fin k.succ) F) {i j : Fin k.succ} (hAij : A i j = 1 ∨ A i j = -1) :
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

private lemma Matrix.twoSum_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Yᵣ] [DecidableEq Yₗ]
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    ((c · * r ·) ◫ Aᵣ).IsTotallyUnimodular :=
  (hAc.fromCols_comm.fromCols_outer (hAr.apply ◪())).fromCols_comm


-- ## 2-sum of TU matrices is TU

private lemma Matrix.twoSum_isPreTU_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (Matrix.twoSum Aₗ r Aᵣ c).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  cases f 0 with
  | inl iₗ => cases g 0 with
    | inl jₗ => exact (hAr.comp_rows Sum.inl).apply iₗ jₗ
    | inr jᵣ => exact zero_in_signTypeCastRange
  | inr iᵣ => cases g 0 with
    | inl jₗ => exact in_signTypeCastRange_mul_in_signTypeCastRange (hAc.apply iᵣ ◩()) (hAr.apply ◪() jₗ)
    | inr jᵣ => exact (hAc.comp_cols Sum.inr).apply iᵣ jᵣ

private lemma Matrix.twoSum_isTotallyUnimodular {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Aₗ : Matrix Xₗ Yₗ ℚ} {r : Yₗ → ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c : Xᵣ → ℚ}
    (hAr : (Aₗ ⊟ ▬r).IsTotallyUnimodular) (hAc : (▮c ◫ Aᵣ).IsTotallyUnimodular) :
    (Matrix.twoSum Aₗ r Aᵣ c).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  cases k with
  | zero => simp [Matrix.IsPreTU]
  | succ m => induction m generalizing Aₗ r Aᵣ c with
    | zero => exact Matrix.twoSum_isPreTU_1 hAr hAc
    | succ n ih =>
      intro f g
      wlog hf : f.Injective
      · exact (Matrix.twoSum Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_rows g hf ▸ zero_in_signTypeCastRange
      wlog hg : g.Injective
      · exact (Matrix.twoSum Aₗ r Aᵣ c).submatrix_det_zero_of_not_injective_cols f hg ▸ zero_in_signTypeCastRange
      wlog hfₗ : ∃ iₗ : Fin (n + 2), ∃ xₗ : Xₗ, f iₗ = ◩xₗ
      · push_neg at hfₗ
        convert (Matrix.twoSum_bottom_isTotallyUnimodular hAr hAc).det (fn_of_sum_ne_inl hfₗ) g using 2
        ext
        rewrite [Matrix.submatrix_apply, Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfₗ]
        rfl
      obtain ⟨iₗ, xₗ, hfiₗ⟩ := hfₗ
      wlog hgₗ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ xₗ y₀ ≠ 0
      · push_neg at hgₗ
        convert zero_in_signTypeCastRange
        apply ((Matrix.twoSum Aₗ r Aᵣ c).submatrix f g).det_eq_zero_of_row_eq_zero iₗ
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
      have hArAc1 : ((Matrix.twoSum Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = 1 ∨
                    ((Matrix.twoSum Aₗ r Aᵣ c).submatrix f g) iₗ j₀ = -1
      · rw [Matrix.submatrix_apply, hfiₗ, hgj₀]
        exact hAxy1
      obtain ⟨f', g', -, -, hArAc⟩ :=
        ((Matrix.twoSum Aₗ r Aᵣ c).submatrix f g).shortTableauPivot_abs_det_eq_submatrix_abs_det hArAc1
      rw [in_signTypeCastRange_iff_abs, hArAc, (Matrix.twoSum Aₗ r Aᵣ c).submatrix_shortTableauPivot hf hg iₗ j₀,
        hfiₗ, hgj₀, Matrix.submatrix_submatrix, Matrix.twoSum_shortTableauPivot Aₗ r Aᵣ c,
        ←in_signTypeCastRange_iff_abs]
      exact ih (hAr.fromRows_pivot hAxy0) hAc (f ∘ f') (g ∘ g')

private lemma Matrix.twoSum_hasTuSigning {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Aₗ : Matrix Xₗ Yₗ Z2} {r : Yₗ → Z2} {Aᵣ : Matrix Xᵣ Yᵣ Z2} {c : Xᵣ → Z2}
    (hAr : (Aₗ ⊟ ▬r).HasTuSigning) (hAc : (▮c ◫ Aᵣ).HasTuSigning) :
    (Matrix.twoSum Aₗ r Aᵣ c).HasTuSigning := by
  have ⟨Bₗ, hBAₗ, hBₗ⟩ := hAr
  have ⟨Bᵣ, hBAᵣ, hBᵣ⟩ := hAc
  let Aₗ' := Bₗ.toRows₁
  let r' := Bₗ.toRows₂ ()
  let Aᵣ' := Bᵣ.toCols₂
  let c' := (Bᵣ.toCols₁ · ())
  have hBₗeq : Bₗ = Aₗ' ⊟ ▬r' := by ext i j; cases i <;> rfl
  have hBᵣeq : Bᵣ = ▮c' ◫ Aᵣ' := by ext i j; cases j <;> rfl
  exact ⟨
    Matrix.twoSum Aₗ' r' Aᵣ' c',
    (fun i j => i.casesOn
      (fun iₗ => j.casesOn (fun jₗ => hBAₗ (◩iₗ) jₗ) (fun jᵣ => rfl))
      (fun iᵣ => j.casesOn
        (fun jₗ => Z2val_toRat_mul_Z2val_toRat (c iᵣ) (r jₗ) ▸ (hBAₗ (◪()) jₗ) ▸ (hBAᵣ iᵣ (◩())) ▸ abs_mul (c' iᵣ) (r' jₗ))
        (fun jᵣ => hBAᵣ iᵣ (◪jᵣ)))),
    Matrix.twoSum_isTotallyUnimodular (hBₗeq ▸ hBₗ) (hBᵣeq ▸ hBᵣ)
  ⟩

private lemma Matrix.HasTuSigning.toMatrixUnionUnion {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α} {A : Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) Z2}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hA : A.HasTuSigning) :
    A.toMatrixUnionUnion.HasTuSigning :=
  have ⟨_, hAA, hB⟩ := hA
  ⟨
    _,
    (hAA ·.toSum ·.toSum),
    hB.toMatrixUnionUnion
  ⟩


-- ## 2-sum of standard representations

noncomputable def standardReprTwoSumRepr {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 where
  X := (Sₗ.X \ {a}) ∪ Sᵣ.X
  Y := Sₗ.Y ∪ (Sᵣ.Y \ {a})
  hXY := (by
    rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
    exact ⟨⟨Sₗ.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨disjoint_of_sdiff_singleton ha, Sᵣ.hXY.disjoint_sdiff_right⟩⟩)
  A := (Matrix.twoSum (Sₗ.A.dropRow a) (Sₗ.A.interRow ha) (Sᵣ.A.dropCol a) (Sᵣ.A.interCol ha)).toMatrixUnionUnion
  deqX := inferInstance
  deqY := inferInstance
  dmemX := inferInstance
  dmemY := inferInstance

noncomputable def standardReprTwoSumIsValid {α : Type} {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (_hYX : Sₗ.Y ⫗ Sᵣ.X) : Prop :=
  (Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y) ∧ (Sₗ.A.interRow ha ≠ 0 ∧ Sᵣ.A.interCol ha ≠ 0)

noncomputable def standardReprTwoSum {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨standardReprTwoSumRepr ha hYX, standardReprTwoSumIsValid ha hYX⟩

lemma standardReprTwoSum_hasTuSigning {α : Type} [DecidableEq α] {a : α} {Sₗ Sᵣ : StandardRepr α Z2}
    (ha : Sₗ.X ∩ Sᵣ.Y = {a}) (hYX : Sₗ.Y ⫗ Sᵣ.X) (hSₗ : Sₗ.A.HasTuSigning) (hSᵣ : Sᵣ.A.HasTuSigning) :
    (standardReprTwoSumRepr ha hYX).A.HasTuSigning :=
  have ⟨Aₗ, hAAₗ, hAₗ⟩ := hSₗ
  have ⟨Aᵣ, hAAᵣ, hAᵣ⟩ := hSᵣ
  have hAr : (Sₗ.A.dropRow a ⊟ ▬Sₗ.A.interRow ha).HasTuSigning := ⟨
    Aₗ.dropRow a ⊟ ▬Aₗ.interRow ha,
    (fun i j => i.casesOn (fun iₗ => hAAₗ (Set.diff_subset.elem iₗ) j) ↓(hAAₗ ha._ₗ j)),
    hAₗ.reglueRow ha
  ⟩
  have hAc : (▮(Sᵣ.A.interCol ha) ◫ Sᵣ.A.dropCol a).HasTuSigning := ⟨
    ▮Aᵣ.interCol ha ◫ Aᵣ.dropCol a,
    (fun i j => j.casesOn ↓(hAAᵣ i ha._ᵣ) (fun jᵣ => hAAᵣ i (Set.diff_subset.elem jᵣ))),
    hAᵣ.reglueCol ha
  ⟩
  (Matrix.twoSum_hasTuSigning hAr hAc).toMatrixUnionUnion


-- ## 2-sum of matroids

/-- Matroid `M` is a 2-sum composition of `Mₗ` and `Mᵣ`. -/
structure Matroid.IsTwoSumOf {α : Type} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) where
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Fintype Sₗ.Y
  hSᵣ : Fintype Sᵣ.Y
  a : α
  ha : Sₗ.X ∩ Sᵣ.Y = {a}
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hMₗ : Mₗ = Sₗ.toMatroid
  hMᵣ : Mᵣ = Sᵣ.toMatroid
  hM : M = (standardReprTwoSumRepr ha hYX).toMatroid
  IsValid : standardReprTwoSumIsValid ha hYX

noncomputable instance Matroid.IsTwoSumOf.finY {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} (hM : M.IsTwoSumOf Mₗ Mᵣ) :
    Fintype (standardReprTwoSumRepr hM.ha hM.hYX).Y :=
  have := hM.hSₗ
  have := hM.hSᵣ
  Fintype.ofFinite ↑(hM.Sₗ.Y ∪ hM.Sᵣ.Y \ {hM.a})

/-- Any 2-sum of regular matroids is a regular matroid.
    This is part two (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsTwoSumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.IsTwoSumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finY
  obtain ⟨Sₗ, Sᵣ, hSₗ, hSᵣ, a, ha, hYX, rfl, rfl, rfl, IsValid⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprTwoSum_hasTuSigning ha hYX hMₗ hMᵣ
