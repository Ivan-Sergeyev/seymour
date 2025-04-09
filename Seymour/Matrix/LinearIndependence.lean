import Seymour.Matrix.Basic
import Mathlib.Data.Matrix.Rank
section fromPetersProject

section LinearIndepen

open Function Set Submodule

variable {ι R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M] {s₀ s t : Set ι} {v : ι → M}

theorem LinearIndepOn.exists_maximal (hli : LinearIndepOn R v s₀) (hs₀t : s₀ ⊆ t) :
    ∃ s, s₀ ⊆ s ∧ Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s :=
  zorn_subset_nonempty {r | r ⊆ t ∧ LinearIndepOn R v r}
    (fun c hcss hchain _ ↦ ⟨⋃₀ c, ⟨sUnion_subset fun _ hxc ↦ (hcss hxc).1,
      linearIndepOn_sUnion_of_directed hchain.directedOn fun _ hxc ↦ (hcss hxc).2⟩,
      fun _ hs ↦ subset_sUnion_of_mem hs⟩) s₀ ⟨hs₀t, hli⟩

lemma LinearIndepOn.span_eq_of_maximal_subset
    (hmax : Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s) :
    span R (v '' s) = span R (v '' t) := by
  refine le_antisymm (span_mono (image_mono hmax.prop.1)) <| span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hmax.prop.2.mem_span_iff.2 <|
    fun h ↦ hmax.mem_of_prop_insert ⟨(insert_subset hx hmax.prop.1), h⟩

lemma LinearIndepOn.span_eq_top_of_maximal (hmax : Maximal (LinearIndepOn R v ·) s) :
    span R (v '' s) = span R (range v) := by
  rw [← image_univ, LinearIndepOn.span_eq_of_maximal_subset (t := univ) (by simpa)]

end LinearIndepen
namespace Matrix


open Set Submodule Cardinal

universe u v w u₁ u₂

variable {m n R : Type*} {A A₁ A₂ : Matrix m n R} {s : Set m} {t : Set n}

def rowFun (A : Matrix m n R) (i : m) : n → R := A i

def colFun (A : Matrix m n R) (i : n) : m → R := Aᵀ i

@[simp]
lemma colFun_apply (A : Matrix m n R) (i : m) (j : n) : A.colFun j i = A i j := rfl

@[simp]
lemma transpose_rowFun (A : Matrix m n R) : Aᵀ.rowFun = A.colFun := rfl

@[simp]
lemma range_submatrix_left {α l : Type*} (A : Matrix m n α) (r_reindex : l → m) :
    range (A.submatrix r_reindex id).rowFun = A.rowFun '' range r_reindex := by
  ext x
  simp only [mem_range, mem_image, exists_exists_eq_and]
  rfl

/-- For `A : Matrix m n R` and `s : Set m`,
`A.IsRowBasis R s` means that `s` indexes an `R`-basis for the row space of `A`. -/
def IsRowBasis (R : Type*) [Semiring R] (A : Matrix m n R) (s : Set m) : Prop :=
  Maximal (LinearIndepOn R A.rowFun ·) s

/-- For `A : Matrix m n R` and `t : Set n`,
`A.IsColBasis R t` means that `t` indexes an `R`-basis for the column space of `A`. -/
def IsColBasis (R : Type*) [Semiring R] (A : Matrix m n R) (t : Set n) : Prop :=
  Aᵀ.IsRowBasis R t

lemma IsRowBasis.span_eq [DivisionRing R] (hs : A.IsRowBasis R s) :
    span R (A.rowFun '' s) = span R (range A.rowFun) :=
  LinearIndepOn.span_eq_top_of_maximal hs

/-- If `A.IsRowBasis R s`, then `s` naturally indexes an `R`-`Basis` for the row space of `A`. -/
noncomputable def IsRowBasis.basis [DivisionRing R] (hs : A.IsRowBasis R s) :
    Basis s R <| span R (range A.rowFun) :=
  (Basis.span hs.prop.linearIndependent).map <|
    LinearEquiv.ofEq _ _ <| by rw [← image_eq_range, hs.span_eq]

lemma IsColBasis.isRowBasis_transpose [Semiring R] (h : A.IsColBasis R t) : Aᵀ.IsRowBasis R t :=
  h

/-- If `A.IsColBasis R t`, then `t` naturally indexes an `R`-`Basis` for the column space of `A`. -/
noncomputable def IsColBasis.basis [DivisionRing R] (ht : A.IsColBasis R t) :
    Basis t R <| span R (range A.colFun) :=
  ht.isRowBasis_transpose.basis

lemma IsColBasis.encard_eq [DivisionRing R] (h : A.IsColBasis R t) : t.encard = A.eRank := by
  simpa using congr_arg Cardinal.toENat h.basis.mk_eq_rank

lemma exists_isRowBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) :
    ∃ s, A.IsRowBasis R s := by
  obtain ⟨s, -, hs⟩ := (linearIndepOn_empty R A).exists_maximal (subset_univ _)
  exact ⟨s, by simpa using hs⟩

lemma IsRowBasis.isColBasis_transpose [Semiring R] (h : A.IsRowBasis R s) : Aᵀ.IsColBasis R s :=
  h

lemma exists_isColBasis (R : Type*) [DivisionRing R] (A : Matrix m n R) : ∃ s, A.IsColBasis R s :=
  Aᵀ.exists_isRowBasis R


variable {α : Type*}

/-- If the row space of `A₁` is a subspace of the row space of `A₂`, then independence of
a set of columns of `A₁` implies independence in `A₂`. -/
theorem linearIndepOn_col_le_of_span_row_le {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) ≤ span R (range A₂.rowFun)) :
    LinearIndepOn R A₁.colFun ≤ LinearIndepOn R A₂.colFun := by
  -- Perhaps this proof can be simplified by not fully unfolding `LinearCombination` and `sum`.
  refine fun t ht ↦ linearIndepOn_iff.2 fun l hl hl0 ↦ linearIndepOn_iff.1 ht l hl ?_
  ext i
  have hi : A₁ i ∈ span R (range A₂) := h <| subset_span <| mem_range_self ..
  simp_rw [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum] at hi
  obtain ⟨c, hc⟩ := hi
  have hrw (i' : m₂) : ∑ x ∈ l.support, l x * A₂ i' x = 0 := by
    simpa [Finsupp.linearCombination, Finsupp.sum] using congr_fun hl0 i'
  suffices ∑ x ∈ l.support, l x * ∑ x_1 ∈ c.support, c x_1 * A₂ x_1 x = 0 by
    simpa [Finsupp.linearCombination, Finsupp.sum, ← hc]
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := l.support), mul_left_comm (a := l _),
    ← Finset.mul_sum]
  simp [hrw]

/-- Two matrices with the same row space have the same linearly independent sets of columns. -/
lemma linearIndepOn_col_eq_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) = span R (range A₂.rowFun)) :
    LinearIndepOn R A₁.colFun = LinearIndepOn R A₂.colFun :=
  (linearIndepOn_col_le_of_span_row_le h.le).antisymm
    (linearIndepOn_col_le_of_span_row_le h.symm.le)

lemma isColBasis_iff_of_span_row_eq {m₁ m₂ : Type*} [CommRing R] {A₁ : Matrix m₁ n R}
    {A₂ : Matrix m₂ n R} (h : span R (range A₁.rowFun) = span R (range A₂.rowFun)) (t : Set n) :
    A₁.IsColBasis R t ↔ A₂.IsColBasis R t := by
  rw [IsColBasis, IsRowBasis, transpose_rowFun, linearIndepOn_col_eq_of_span_row_eq h,
     IsColBasis, IsRowBasis, transpose_rowFun]

lemma IsRowBasis.span_submatrix_eq [DivisionRing R] (hs : A.IsRowBasis R s) :
    span R (range (A.submatrix (fun x : s ↦ x) id).rowFun) = span R (range A.rowFun) := by
  simp only [range_submatrix_left, Subtype.range_coe_subtype, setOf_mem_eq, ← hs.span_eq]

lemma IsColBasis.submatrix_isColBasis [Field R] (ht : A.IsColBasis R t) (hs : A.IsRowBasis R s) :
    (A.submatrix (fun x : s ↦ x) id).IsColBasis R t :=
  (isColBasis_iff_of_span_row_eq hs.span_submatrix_eq _).2 ht

lemma IsRowBasis.submatrix_isRowBasis [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    (A.submatrix id (fun x : t ↦ x)).IsRowBasis R s :=
  IsColBasis.submatrix_isColBasis (A := Aᵀ) hs ht

private lemma basis_encard_le_aux [Field R] (hs : A.IsRowBasis R s) (ht : A.IsColBasis R t) :
    s.encard ≤ t.encard := by
  wlog hfin : t.Finite
  · simp [Infinite.encard_eq hfin]
  have := hfin.fintype
  convert OrderHomClass.mono toENat <|
    (hs.submatrix_isRowBasis ht).prop.linearIndependent.cardinal_lift_le_rank <;>
  simp

/-- The `encard` of a row basis is equal to the rank of the column space.
Unlike the column basis case (where this is essentially just the definition), this needs a `Field`.
One can also prove with `DivisionRing` that `s.encard = Aᵀ.eRank` using `h.IsColBasis.encard_eq` -/
lemma IsRowBasis.encard_eq [Field R] (h : A.IsRowBasis R s) : s.encard = A.eRank := by
  obtain ⟨t, ht⟩ := A.exists_isColBasis
  rw [← ht.encard_eq]
  exact (basis_encard_le_aux h ht).antisymm (basis_encard_le_aux ht.isRowBasis_transpose h)

end Matrix

end fromPetersProject

open scoped Matrix

variable {X Y F : Type} [Fintype X] [Fintype Y] [Field F]

lemma Matrix.not_linearIndependent_of_rank_lt (A : Matrix X Y F) (hA : A.rank < #X) :
    ¬ LinearIndependent F A :=
  (A.rank_eq_finrank_span_row ▸ finrank_span_eq_card · ▸ hA |>.false)

lemma Matrix.not_linearIndependent_of_too_many_rows (A : Matrix X Y F) (hYX : #Y < #X) :
    ¬ LinearIndependent F A :=
  A.not_linearIndependent_of_rank_lt (A.rank_le_card_width.trans_lt hYX)

lemma Matrix.exists_submatrix_rank (A : Matrix X Y F) :
    ∃ r : Fin A.rank → X, (A.submatrix r id).rank = A.rank := by
  obtain ⟨s, hs⟩ := exists_isRowBasis F A
  obtain ⟨t, ht⟩ := exists_isColBasis F A
  have h₃ : (A.submatrix (fun x : s ↦ x) id).IsColBasis F t := IsColBasis.submatrix_isColBasis ht hs
  have : s.ncard = A.rank := by
    rw [show A.rank = A.eRank.toNat by rw [eRank_toNat_eq_rank], Set.ncard, IsRowBasis.encard_eq hs]
  rw [← this]
  suffices ∃ r : s → X, (A.submatrix r id).rank = s.ncard by
    obtain ⟨r, hr⟩ := this
    simp_rw [← hr]
    haveI : Nonempty (Fin s.ncard ≃ s) := Nonempty.intro (Finite.equivFinOfCardEq rfl).symm
    let eq : Fin s.ncard ≃ s := Classical.ofNonempty
    use r ∘ eq
    have : (A.submatrix r id).submatrix eq id = (A.submatrix (r ∘ eq) id) := by
      simp [Matrix.submatrix_submatrix]
    rw [← this]
    have := (A.submatrix r id).rank_submatrix eq (Equiv.refl Y)
    simp_all
  use fun x ↦ x
  have : t.ncard = s.ncard := by rw [Set.ncard, Set.ncard, hs.encard_eq, ht.encard_eq]
  rw [← this, Set.ncard, h₃.encard_eq, eRank_toNat_eq_rank]

variable [DecidableEq X] [DecidableEq Y]

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
