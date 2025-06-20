import Mathlib.Data.Matrix.Rank
import Seymour.Basic.SubmoduleSpans
import Seymour.Matrix.Basic

/-!
# Linear Independence and Matrices

This file provides lemmas about linear independence in the context of matrices that are not present in Mathlib.
-/

lemma Matrix.linearIndependent_iff_fromCols_zero {X Y R : Type} [Ring R] (A : Matrix X Y R) (Y₀ : Type) :
    LinearIndependent R A ↔ LinearIndependent R (A ◫ (0 : Matrix X Y₀ R)) := by
  simp only [linearIndependent_iff']
  constructor
  <;> intro hA s c hscA
  <;> apply hA
  <;> ext j
  · simpa using congr_fun hscA ◩j
  · exact j.casesOn (by simpa using congr_fun hscA ·) (by simp)

private lemma LinearIndepOn.exists_maximal {ι R O : Type} [DivisionRing R] [AddCommGroup O] [Module R O] {t : Set ι}
    {v : ι → O} {s₀ : Set ι} (hRv : LinearIndepOn R v s₀) (ht : s₀ ⊆ t) :
    ∃ s : Set ι, s₀ ⊆ s ∧ Maximal (fun r : Set ι => r ⊆ t ∧ LinearIndepOn R v r) s :=
  zorn_subset_nonempty { r : Set ι | r ⊆ t ∧ LinearIndepOn R v r }
    (fun c hcss cchain _ => ⟨⋃₀ c, ⟨Set.sUnion_subset ↓(hcss ·|>.left),
      linearIndepOn_sUnion_of_directed cchain.directedOn ↓(hcss ·|>.right)⟩,
      ↓Set.subset_sUnion_of_mem⟩) s₀ ⟨ht, hRv⟩

namespace Matrix

variable {m n R : Type}

private def rowFun (A : Matrix m n R) (i : m) : n → R := A i

private def colFun (A : Matrix m n R) (i : n) : m → R := Aᵀ i

private lemma colFun_apply (A : Matrix m n R) (i : m) (j : n) : A.colFun j i = A i j := rfl

private lemma transpose_rowFun (A : Matrix m n R) : Aᵀ.rowFun = A.colFun := rfl

private lemma range_submatrix_left {α l : Type} (A : Matrix m n α) (f : l → m) :
    (A.submatrix f id).rowFun.range = A.rowFun '' f.range := by
  ext
  simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
  rfl

/-- For `A : Matrix m n R` and `s : Set m`
    `A.IsRowBasis R s` means that `s` indexes an `R`-basis for the row space of `A`. -/
private def IsRowBasis (R : Type) [Semiring R] (A : Matrix m n R) (s : Set m) : Prop :=
  Maximal (LinearIndepOn R A.rowFun ·) s

/-- For `A : Matrix m n R` and `t : Set n`
    `A.IsColBasis R t` means that `t` indexes an `R`-basis for the column space of `A`. -/
private def IsColBasis (R : Type) [Semiring R] (A : Matrix m n R) (t : Set n) : Prop :=
  Aᵀ.IsRowBasis R t

private lemma IsRowBasis.span_eq [DivisionRing R] {s : Set m} {A : Matrix m n R} (hs : A.IsRowBasis R s) :
    Submodule.span R (A.rowFun '' s) = Submodule.span R A.rowFun.range :=
  span_eq_top_of_maximal_linearIndepOn hs

/-- If `A.IsRowBasis R s` then `s` naturally indexes an `R`-`Basis` for the row space of `A`. -/
private noncomputable def IsRowBasis.basis [DivisionRing R] {s : Set m} {A : Matrix m n R} (hs : A.IsRowBasis R s) :
    Basis s R (Submodule.span R A.rowFun.range) :=
  (Basis.span hs.prop.linearIndependent).map (LinearEquiv.ofEq _ _ (by rw [←Set.image_eq_range, hs.span_eq]))

private lemma IsColBasis.encard_eq [DivisionRing R] {t : Set n} {A : Matrix m n R} (hA : A.IsColBasis R t) :
    t.encard = A.eRank := by
  simpa using congr_arg Cardinal.toENat hA.basis.mk_eq_rank

private lemma exists_isRowBasis {R : Type} [DivisionRing R] (A : Matrix m n R) :
    ∃ s : Set m, A.IsRowBasis R s := by
  obtain ⟨s, -, hs⟩ := (linearIndepOn_empty R A).exists_maximal (Set.subset_univ _)
  exact ⟨s, by simpa using hs⟩

private lemma exists_isColBasis (R : Type) [DivisionRing R] (A : Matrix m n R) : ∃ s : Set n, A.IsColBasis R s :=
  Aᵀ.exists_isRowBasis

/-- If the row space of `A₁` is a subspace of the row space of `A₂`, then independence of
    a set of columns of `A₁` implies independence in `A₂`. -/
private lemma linearIndepOn_col_le_of_span_row_le {m₁ m₂ : Type} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (hR : Submodule.span R A₁.rowFun.range ≤ Submodule.span R A₂.rowFun.range) :
    LinearIndepOn R A₁.colFun ≤ LinearIndepOn R A₂.colFun := by
  refine fun t ht => linearIndepOn_iff.← fun l hl hl0 => linearIndepOn_iff.→ ht l hl ?_
  ext i
  have hi : A₁ i ∈ Submodule.span R A₂.range := hR (Submodule.subset_span (Set.mem_range_self _))
  simp_rw [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum] at hi
  obtain ⟨c, hc⟩ := hi
  have hrw (i' : m₂) : ∑ x ∈ l.support, l x * A₂ i' x = 0
  · simpa [Finsupp.linearCombination, Finsupp.sum] using congr_fun hl0 i'
  suffices : ∑ x ∈ l.support, l x * ∑ x_1 ∈ c.support, c x_1 * A₂ x_1 x = 0
  · simpa [Finsupp.linearCombination, Finsupp.sum, colFun_apply, ←hc]
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := l.support), mul_left_comm (a := l _), ←Finset.mul_sum]
  simp [hrw]

/-- Two matrices with the same row space have the same linearly independent sets of columns. -/
private lemma linearIndepOn_col_eq_of_span_row_eq {m₁ m₂ : Type} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (hA : Submodule.span R A₁.rowFun.range = Submodule.span R A₂.rowFun.range) :
    LinearIndepOn R A₁.colFun = LinearIndepOn R A₂.colFun :=
  (linearIndepOn_col_le_of_span_row_le hA.le).antisymm
    (linearIndepOn_col_le_of_span_row_le hA.symm.le)

private lemma isColBasis_iff_of_span_row_eq {m₁ m₂ : Type} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (hA : Submodule.span R A₁.rowFun.range = Submodule.span R A₂.rowFun.range) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, transpose_rowFun, linearIndepOn_col_eq_of_span_row_eq hA,
     IsColBasis, IsRowBasis, transpose_rowFun]

private lemma IsRowBasis.span_submatrix_eq [DivisionRing R] {s : Set m} {A : Matrix m n R} (hs : A.IsRowBasis R s) :
    Submodule.span R (A.submatrix (fun x : s => x) id).rowFun.range = Submodule.span R A.rowFun.range := by
  simp only [range_submatrix_left, Subtype.range_coe_subtype, Set.setOf_mem_eq, ←hs.span_eq]

private lemma IsColBasis.submatrix_isColBasis [Field R] {s : Set m} {t : Set n} {A : Matrix m n R}
    (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix (fun x : s => x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).← ht

private lemma IsRowBasis.submatrix_isRowBasis [Field R] {s : Set m} {t : Set n} {A : Matrix m n R}
    (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix id (fun x : t => x)).IsRowBasis R s :=
  IsColBasis.submatrix_isColBasis (A := Aᵀ) hs ht

private lemma basis_encard_le_aux [Field R] {s : Set m} {t : Set n} {A : Matrix m n R}
    (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    s.encard ≤ t.encard := by
  wlog T_fin : t.Finite
  · simp [Set.Infinite.encard_eq T_fin]
  have := T_fin.fintype
  convert OrderHomClass.mono Cardinal.toENat (hs.submatrix_isRowBasis ht).prop.linearIndependent.cardinal_lift_le_rank <;> simp

private lemma IsRowBasis.encard_eq [Field R] {s : Set m} {A : Matrix m n R} (hA : A.IsRowBasis R s) : s.encard = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [←ht.encard_eq]
  exact (basis_encard_le_aux hA ht).antisymm (basis_encard_le_aux ht hA)

end Matrix


open scoped Matrix

/-- Every invertible matrix has linearly independent rows (unapplied version). -/
lemma IsUnit.linearIndependent_matrix {α R : Type} [DecidableEq α] [Fintype α] [Ring R] {A : Matrix α α R} (hA : IsUnit A) :
    LinearIndependent R A :=
  A.linearIndependent_rows_of_isUnit hA

variable {X Y F : Type} [Fintype X] [Fintype Y] [Field F]

lemma Matrix.not_linearIndependent_of_rank_lt (A : Matrix X Y F) (hA : A.rank < #X) :
    ¬ LinearIndependent F A :=
  (A.rank_eq_finrank_span_row ▸ finrank_span_eq_card · ▸ hA |>.false)

lemma Matrix.not_linearIndependent_of_too_many_rows (A : Matrix X Y F) (hYX : #Y < #X) :
    ¬ LinearIndependent F A :=
  A.not_linearIndependent_of_rank_lt (A.rank_le_card_width.trans_lt hYX)

lemma Matrix.exists_submatrix_rank (A : Matrix X Y F) :
    ∃ r : Fin A.rank → X, (A.submatrix r id).rank = A.rank := by
  obtain ⟨s, hs⟩ := A.exists_isRowBasis
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  have hFt : (A.submatrix (fun x : s => x) id).IsColBasis F t := Matrix.IsColBasis.submatrix_isColBasis ht hs
  have hsA : s.ncard = A.rank
  · rw [show A.rank = A.eRank.toNat by rw [Matrix.eRank_toNat_eq_rank], Set.ncard, Matrix.IsRowBasis.encard_eq hs]
  rw [←hsA]
  suffices : ∃ r : s → X, (A.submatrix r id).rank = s.ncard
  · obtain ⟨r, hr⟩ := this
    simp_rw [←hr]
    have : Nonempty (Fin s.ncard ≃ s) := Nonempty.intro (Finite.equivFinOfCardEq rfl).symm
    let e : Fin s.ncard ≃ s := Classical.ofNonempty
    use r ∘ e
    have hAr : (A.submatrix r id).submatrix e id = (A.submatrix (r ∘ e) id)
    · simp [Matrix.submatrix_submatrix]
    rw [←hAr]
    have := (A.submatrix r id).rank_submatrix e (Equiv.refl Y)
    simp_all
  use (·)
  have hts : t.ncard = s.ncard
  · rw [Set.ncard, Set.ncard, hs.encard_eq, ht.encard_eq]
  rw [←hts, Set.ncard, hFt.encard_eq, Matrix.eRank_toNat_eq_rank]

variable [DecidableEq X]

/-- Rows of a matrix are linearly independent iff the matrix contains a nonsigular square submatrix of full height. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_unit (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, IsUnit (A.submatrix id f) := by
  constructor
  · intro hA
    have hXA : #X = Aᵀ.rank := (A.rank_transpose.trans hA.rank_matrix).symm
    obtain ⟨f, hf⟩ := Aᵀ.exists_submatrix_rank
    use f ∘ Fintype.equivFinOfCardEq hXA
    have hX : #X = (A.submatrix id (f ∘ Fintype.equivFinOfCardEq hXA)).rank
    · rw [←Matrix.transpose_submatrix, Matrix.rank_transpose] at hf
      conv => lhs; rw [hXA, ←hf]
      exact ((A.submatrix id f).rank_submatrix (Equiv.refl X) (Fintype.equivFinOfCardEq hXA)).symm
    rw [←Matrix.linearIndependent_rows_iff_isUnit, linearIndependent_iff_card_eq_finrank_span, hX]
    apply Matrix.rank_eq_finrank_span_row
  · intro ⟨f, hAf⟩
    exact hAf.linearIndependent_matrix.of_comp (LinearMap.funLeft F F f)

/-- Rows of a matrix are linearly independent iff the matrix contains a square submatrix of full height with nonzero det. -/
lemma Matrix.linearIndependent_iff_exists_submatrix_det (A : Matrix X Y F) :
    LinearIndependent F A ↔ ∃ f : X → Y, (A.submatrix id f).det ≠ 0 := by
  convert A.linearIndependent_iff_exists_submatrix_unit
  convert isUnit_iff_ne_zero.symm
  apply Matrix.isUnit_iff_isUnit_det
