import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Map
import Mathlib.Data.Matroid.Sum

import Seymour.Basic.Basic
import Seymour.Basic.Fin
import Seymour.Basic.Sets
import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.Pivoting
import Seymour.Matrix.Support
import Seymour.Matroid.Elementary.Basic

open scoped Matrix Set.Notation


-- ## Vector matroid defined by its full matrix representation

variable {α R : Type} {X Y : Set α}

/-- Predicate of linear independence of a set of rows of a matrix. -/
def Matrix.linearIndepRows [Semiring R] (A : Matrix X Y R) : Set α → Prop :=
  fun I : Set α => I ⊆ X ∧ LinearIndepOn R A (X ↓∩ I)

/-- Equivalent definition of linear independence of rows via `Subset.elem.range`. -/
@[simp]
lemma Matrix.linearIndepRows_iff_elem [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
    A.linearIndepRows I ↔ ∃ hI : I ⊆ X, LinearIndepOn R A hI.elem.range := by
  unfold HasSubset.Subset.elem
  simp_all only [Function.range, Set.range_inclusion, exists_prop]
  rfl

/-- Equivalent definition of linear independence of rows via `Matrix.submatrix`. -/
lemma Matrix.linearIndepRows_iff_submatrix [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
    A.linearIndepRows I ↔ ∃ hI : I ⊆ X, LinearIndependent R (A.submatrix hI.elem id) := by
  constructor
  <;> intro ⟨hI, hAI⟩
  <;> use hI
  <;> let e : I ≃ X ↓∩ I := (Equiv.ofInjective hI.elem hI.elem_injective).trans hI.elem_range.≃
  · exact (linearIndependent_equiv' e rfl).← hAI
  · exact (linearIndependent_equiv' e rfl).→ hAI

/-- Empty set of rows is linearly independent. -/
lemma Matrix.linearIndepRows_empty [Semiring R] (A : Matrix X Y R) :
    A.linearIndepRows ∅ :=
  ⟨X.empty_subset, linearIndepOn_empty _ _⟩

/-- Intersections with `X` on the left viewed as sets in `Set X` respect taking subsets. -/
private lemma inter_subtype_left_subset {I J : Set α} (hIJ : I ⊆ J) :
    X ↓∩ I ⊆ X ↓∩ J :=
  fun _ hx => hIJ hx

/-- Subset of a lineraly independent set of rows is also linearly independent. -/
lemma Matrix.linearIndepRows_subset [Semiring R] {A : Matrix X Y R} {I J : Set α}
    (hJ : A.linearIndepRows J) (hIJ : I ⊆ J) :
    A.linearIndepRows I :=
  ⟨hIJ.trans hJ.left, hJ.right.comp (inter_subtype_left_subset hIJ).elem ((inter_subtype_left_subset hIJ).elem_injective)⟩

/-- Non-maximal linearly independent set of rows can be augmented with a row from a maximal linearly independent set of rows.

To see why `DivisionRing` is necessary, consider `(!![0, 1, 2, 3; 1, 0, 3, 2] : Matrix (Fin 2) (Fin 4) (ZMod 6))`. Here
`{0}` is non-maximal independent,  `{2, 3}` is maximal independent, but neither `{0, 2}` nor `{0, 3}` is independent. -/
lemma Matrix.linearIndepRows_aug [DivisionRing R] {A : Matrix X Y R} {I J : Set α}
    (hI : A.linearIndepRows I) (hI' : ¬Maximal A.linearIndepRows I) (hJ : Maximal A.linearIndepRows J) :
    ∃ x ∈ J \ I, A.linearIndepRows (x ᕃ I) := by
  by_contra! non_aug
  rw [Maximal] at hI'
  push_neg at hI'
  obtain ⟨hIX, hI⟩ := hI
  obtain ⟨⟨hJX, hJ⟩, hJ'⟩ := hJ
  obtain ⟨K, hK, hIK, hnKI⟩ := hI' ⟨hIX, hI⟩
  let I' : Set X := { x : X.Elem | x.val ∈ I }
  let J' : Set X := { x : X.Elem | x.val ∈ J }
  let Iᵥ : Set (Y → R) := A '' I'
  let Jᵥ : Set (Y → R) := A '' J'
  let Iₛ : Submodule R (Y → R) := Submodule.span R Iᵥ
  let Jₛ : Submodule R (Y → R) := Submodule.span R Jᵥ
  have Jᵥ_ss_Iₛ : Jᵥ ⊆ Iₛ
  · intro v ⟨x, hxJ, hxv⟩
    by_cases hvI : v ∈ Iᵥ
    · simp_all only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_left, Iᵥ, I', Iₛ]
      obtain ⟨_, hI', _⟩ := hvI
      apply SetLike.mem_of_subset
      · apply Submodule.subset_span
      · simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left]
        exact ⟨_, hI', by simp_all only⟩
    · have x_in_J : ↑x ∈ J := hxJ
      have x_ni_I : ↑x ∉ I
      · simp_all only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_left, not_exists, not_and, I', Iₛ, Iᵥ]
        intro hI'
        exact hvI _ hI' (hIX hI') hxv
      have x_in_JwoI : ↑x ∈ J \ I := Set.mem_diff_of_mem x_in_J x_ni_I
      have hMxI : ¬A.linearIndepRows (↑x ᕃ I) := non_aug ↑x x_in_JwoI
      rw [Matrix.linearIndepRows] at hMxI
      push_neg at hMxI
      have hnMxI : ¬LinearIndepOn R A (X ↓∩ (↑x ᕃ I)) := hMxI (Set.insert_subset (hJX hxJ) hIX)
      have hYxI : X ↓∩ (↑x ᕃ I) = x ᕃ I'
      · aesop
      rw [hYxI] at hnMxI
      have I'_indep : LinearIndepOn R A I' := hI
      by_contra! v_ni_Iₛ
      have : v ∉ Submodule.span R Iᵥ := v_ni_Iₛ
      have hx_ni_I : x ∉ I' := x_ni_I
      have Mx_ni_span_I : A x ∉ Submodule.span R (A '' I')
      · simp [*, I', J', Iₛ, Iᵥ, Jᵥ]
      have xI_indep : LinearIndepOn R A (x ᕃ I') := (linearIndepOn_insert hx_ni_I).← ⟨I'_indep, Mx_ni_span_I⟩
      exact hnMxI xI_indep
  have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  · intro v ⟨x, hxI, hxv⟩
    by_contra! v_ni_Jₛ
    have Mx_ni_span_J' : A x ∉ Submodule.span R (A '' J') := congr_arg (· ∈ Submodule.span R Jᵥ) hxv ▸ v_ni_Jₛ
    have x_ni_J' : x ∉ J'
    · by_contra! hx_in_J'
      have Mx_in_MJ' : A x ∈ (A '' J') := Set.mem_image_of_mem A hx_in_J'
      have v_in_MJ' : v ∈ (A '' J') := Set.mem_of_eq_of_mem hxv.symm Mx_in_MJ'
      exact v_ni_Jₛ (Submodule.mem_span.← (fun p a => a v_in_MJ'))
    have J'_indep : LinearIndepOn R A J' := hJ
    have xJ'_indep : LinearIndepOn R A (x ᕃ J') := (linearIndepOn_insert x_ni_J').← ⟨J'_indep, Mx_ni_span_J'⟩
    have M_indep_xJ : A.linearIndepRows (↑x ᕃ J)
    · rw [Matrix.linearIndepRows]
      constructor
      · exact Set.insert_subset (hIX hxI) hJX
      · have hxJ' : X ↓∩ (↑x ᕃ J) = x ᕃ J'
        · aesop
        rw [hxJ']
        exact xJ'_indep
    have xJ_ss_J : ↑x ᕃ J ⊆ J := by simp_all
    exact x_ni_J' (xJ_ss_J (J.mem_insert ↑x))
  have Iₛ_eq_Jₛ : Iₛ = Jₛ := Submodule.span_eq_span Iᵥ_ss_Jₛ Jᵥ_ss_Iₛ
  obtain ⟨k, k_in_K, k_ni_I⟩ := Set.not_subset.→ hnKI
  have kI_ss_K : (k ᕃ I) ⊆ K := Set.insert_subset k_in_K hIK
  have M_indep_kI : A.linearIndepRows (k ᕃ I) := A.linearIndepRows_subset hK kI_ss_K
  have kI_ss_Y : k ᕃ I ⊆ X := M_indep_kI.left
  have k_in_Y : k ∈ X := kI_ss_Y (I.mem_insert k)
  let k' : X.Elem := ⟨k, k_in_Y⟩
  by_cases hkJ' : k' ∈ J'
  · have k_in_JwoI : k ∈ J \ I := Set.mem_diff_of_mem hkJ' k_ni_I
    exact non_aug k k_in_JwoI M_indep_kI
  . have hkI' : X ↓∩ (k ᕃ I) = ↑k' ᕃ I'
    · aesop
    have k'_ni_I' : k' ∉ I' := k_ni_I
    rw [Matrix.linearIndepRows, hkI'] at M_indep_kI
    obtain ⟨_, M_indep_kI⟩ := M_indep_kI
    have Mk'_ni_span_I' : A k' ∉ Submodule.span R (A '' I') := ((linearIndepOn_insert k'_ni_I').→ M_indep_kI).right
    have Mk'_ni_span_J' : A k' ∉ Submodule.span R (A '' J')
    · have span_I'_eq_span_J' : Submodule.span R (A '' I') = Submodule.span R (A '' J') := Iₛ_eq_Jₛ
      rw [←span_I'_eq_span_J']
      exact Mk'_ni_span_I'
    have J'_indep : LinearIndepOn R A J' := hJ
    have kJ'_indep : LinearIndepOn R A (k' ᕃ J') := (linearIndepOn_insert hkJ').← ⟨J'_indep, Mk'_ni_span_J'⟩
    have hMkJ : A.linearIndepRows (k ᕃ J)
    · rw [Matrix.linearIndepRows]
      constructor
      · exact Set.insert_subset k_in_Y hJX
      · have hkJ : X ↓∩ (k ᕃ J) = k' ᕃ J'
        · aesop
        rw [hkJ]
        exact kJ'_indep
    have kJ_ss_J : k ᕃ J ⊆ J := by simp_all
    exact hkJ' (kJ_ss_J (J.mem_insert k))

/-- todo: docstring -/
private lemma linearIndepOn_sUnion_of_directedOn [Semiring R] {X Y : Set α} {A : Matrix Y X R} {s : Set (Set α)}
    (hs : DirectedOn (· ⊆ ·) s) (hA : ∀ a ∈ s, LinearIndepOn R A (Y ↓∩ a)) :
    LinearIndepOn R A (Y ↓∩ (⋃₀ s)) := by
  let s' : Set (Set Y.Elem) := (fun t : s => Y ↓∩ t).range
  have hss' : Y ↓∩ ⋃₀ s = s'.sUnion
  · simp [s']
  rw [hss']
  apply linearIndepOn_sUnion_of_directed
  · intro x' hx' y' hy'
    obtain ⟨x, hxs, hxM⟩ : ∃ x ∈ s, x' = Y ↓∩ x := by aesop
    obtain ⟨y, hys, hyM⟩ : ∃ y ∈ s, y' = Y ↓∩ y := by aesop
    obtain ⟨z, _, hz⟩ := hs x hxs y hys
    exact ⟨Y ↓∩ z, by aesop, hxM ▸ Set.preimage_mono hz.left, hyM ▸ Set.preimage_mono hz.right⟩
  · aesop

/-- Every set of rows contains a maximal linearly independent subset of rows. -/
lemma Matrix.linearIndepRows_maximal [Semiring R] (A : Matrix X Y R) (I : Set α) :
    Matroid.ExistsMaximalSubsetProperty A.linearIndepRows I :=
  fun J hJ hJI =>
    zorn_subset_nonempty
      { K : Set α | A.linearIndepRows K ∧ K ⊆ I }
      (fun c hcS chain_c _ =>
        ⟨⋃₀ c,
        ⟨⟨Set.sUnion_subset ↓(hcS ·|>.left.left),
          linearIndepOn_sUnion_of_directedOn chain_c.directedOn ↓(hcS ·|>.left.right)⟩,
          Set.sUnion_subset ↓(hcS ·|>.right)⟩,
        ↓Set.subset_sUnion_of_mem⟩)
      J ⟨hJ, hJI⟩

/-- Vector matroid in the form of `IndepMatroid` defined by its full matrix representation. -/
def Matrix.toVectorIndepMatroid [DivisionRing R] (A : Matrix X Y R) : IndepMatroid α where
  E := X
  Indep := A.linearIndepRows
  indep_empty := A.linearIndepRows_empty
  indep_subset _ _ hJ hIJ := Matrix.linearIndepRows_subset hJ hIJ
  indep_aug _ _ hI hI' hJ := A.linearIndepRows_aug hI hI' hJ
  indep_maximal S _ := A.linearIndepRows_maximal S
  subset_ground _ := And.left

/-- Vector matroid converted to `Matroid`. -/
def Matrix.toVectorMatroid [DivisionRing R] (A : Matrix X Y R) : Matroid α :=
  A.toVectorIndepMatroid.matroid

@[simp]
lemma Matrix.toVectorMatroid_E [DivisionRing R] (A : Matrix X Y R) :
    A.toVectorMatroid.E = X :=
  rfl

@[simp low]
lemma Matrix.toVectorMatroid_indep [DivisionRing R] (A : Matrix X Y R) :
    A.toVectorMatroid.Indep = A.linearIndepRows :=
  rfl

lemma Matrix.toVectorMatroid_X_congr [DivisionRing R] {X' Y' : Set α} {A : Matrix X Y R} {B : Matrix X' Y' R}
    (hAB : A.toVectorMatroid = B.toVectorMatroid) :
    X = X' :=
  congr_arg Matroid.E hAB

/-- Vector matroids are finitary. -/
lemma Matrix.toVectorMatroid_Finitary [DivisionRing R] (A : Matrix X Y R) :
    A.toVectorMatroid.Finitary := by
  constructor
  intro I hI
  -- simp
  wlog hIY : I ⊆ A.toVectorMatroid.E
  · obtain ⟨x, hx, hxE⟩ := Set.not_subset_iff_exists_mem_not_mem.→ hIY
    specialize hI { x } (Set.singleton_subset_iff.← hx) (Set.finite_singleton x)
    exact hxE.elim (hI.subset_ground rfl)
  use hIY
  rw [linearIndepOn_iff]
  intro s hs hAs
  rw [Finsupp.mem_supported] at hs
  specialize hI s.support.toSet (Set.image_subset_iff.← hs) (Subtype.val '' s.support).toFinite
  simp [Matrix.linearIndepRows_iff_elem] at hI
  rw [linearIndepOn_iff] at hI
  exact hI s (fun a ha => ⟨⟨a.val, Set.mem_image_of_mem Subtype.val ha⟩, by simp⟩) hAs


-- ## Vector matroid defined by its standard matrix representation

variable [DecidableEq α] [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]

/-- Conversion from standard to full matrix representation. -/
def Matrix.standardToFullRepr [Zero R] [One R] (A : Matrix X Y R) (hXY : X ⫗ Y) :
    Matrix (X ∪ Y).Elem Y R :=
  (A ⊟ 1) ∘ (Subtype.toSum : (X ∪ Y).Elem → X ⊕ Y)

/-- Vector matroid defined by its standard matrix representation. -/
def Matrix.toStandardVectorMatroid [DivisionRing R] (A : Matrix X Y R) (hXY : X ⫗ Y) :
    Matroid α :=
  (A.standardToFullRepr hXY).toVectorMatroid

-- noncomputable abbrev StandardRepr.loopy (R : Type) (Y : Set α) : StandardRepr α R where
--   X := ∅
--   Y := Y
--   hXY _ a _ := a
--   B x _ := x.prop.elim
--   decmemX := Set.decidableEmptyset
--   decmemY a := Classical.propDecidable (a ∈ Y)

-- variable {R : Type}

-- @[simp]
-- lemma StandardRepr.loopy_X (Y : Set α) : (StandardRepr.loopy R Y).X = ∅ :=
--   rfl

-- @[simp]
-- lemma StandardRepr.loopy_toVectorMatroid [DivisionRing R] {Y : Set α} :
--     (StandardRepr.loopy R Y).toMatroid = Matroid.loopyOn Y := by
--   ext X hX
--   · simp
--   · rw [StandardRepr.toMatroid_E] at hX
--     rw [StandardRepr.toMatroid_indep_iff', Matroid.loopyOn_indep_iff]
--     simp_rw [hX, true_and]
--     refine ⟨fun hR => ?_, by rintro rfl; simp⟩
--     by_cases hXX : X ⊆ (StandardRepr.loopy R Y).X
--     · simp_all
--     · by_cases hY : Y = ∅
--       · rw [Set.empty_union] at hX
--         exact Set.subset_eq_empty hX hY
--       · absurd hR
--         rw [linearDepOn_iff]
--         rw [Set.subset_empty_iff] at hXX
--         have ⟨x, hx⟩ := Set.nonempty_def.→ (Set.nonempty_iff_ne_empty.← hXX)
--         use Finsupp.single ⟨x, hX hx⟩ 1
--         exact ⟨Finsupp.single_mem_supported R 1 hx, funext (False.elim <| IsEmpty.false ·), by simp⟩


/-- Ground set of vector matroid given by its standard representation is the union of row and column index sets. -/
@[simp high]
lemma Matrix.toStandardVectorMatroid_E [DivisionRing R] (A : Matrix X Y R) (hXY : X ⫗ Y) :
    (A.toStandardVectorMatroid hXY).E = X ∪ Y :=
  rfl

/-- Vector matroid given by its standard representation has finite ground set if both row and column index sets are finite. -/
instance [DivisionRing R] {A : Matrix X Y R} {hXY : X ⫗ Y} [Finite X] [Finite Y] :
    Finite (A.toStandardVectorMatroid hXY).E :=
  Finite.Set.finite_union X Y




private lemma exists_standardRepr_isBase_aux_left {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)]
    [DivisionRing R] {A : Matrix X Y R} {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R
      ((1 ⊟ (Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id)
        ∘ Subtype.toSum)
      hIGX.elem.range := by
  have hX : G ∪ (X \ G) = X := Set.union_diff_cancel' (by tauto) hGX
  let e : hIGX.elem.range → hIX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert (B.linearIndepOn_in_submodule hAI).comp e ↓↓(by ext; simpa [e] using ·) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · simp_rw [hij]
        simp only [hij, if_true] at hBij
        convert hBij
        ext
        apply hB
    else
      convert Eq.refl (0 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · convert hBij
        · ext
          apply hB
        · symm
          simpa using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [Matrix.submatrix, Subtype.toSum, hiX, hiG, e]

private lemma exists_standardRepr_isBase_aux_right {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)]
    [DivisionRing R] {A : Matrix X Y R} {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hBI : LinearIndepOn R
      ((1 ⊟ (Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id)
        ∘ Subtype.toSum) hIGX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  apply B.linearIndepOn_of_in_submodule
  have hX : X = G ∪ (X \ G) := (Set.union_diff_cancel' (by tauto) hGX).symm
  let e : hIX.elem.range → hIGX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert hBI.comp e ↓↓(by ext; simpa [e] using ·) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simp [*]
      · simp [Matrix.submatrix, Subtype.toSum, e, hiG]
        simpa [Matrix.one_apply] using hij
    else
      convert Eq.refl (0 : R)
      · simp [*]
      · simp [Matrix.submatrix, Subtype.toSum, e, hiG]
        simpa [Matrix.one_apply] using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [Matrix.submatrix, Subtype.toSum, hiX, hiG, e]

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_isBase [DivisionRing R] {G : Set α}
    (M : VectorMatroid α R) (hMG : M.toMatroid.IsBase G) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = M.toMatroid := by
  have hGY : G ⊆ M.Y := hMG.subset_ground
  -- First, prove that `G`-cols of `A` span the entire vector space generated by `Y`-cols of `A` (i.e., the entire colspace).
  have hRAGY : Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range = Submodule.span R M.Aᵀ.range
  · have easy : (M.Aᵀ.submatrix hGY.elem id).range ⊆ M.Aᵀ.range
    · intro v ⟨j, hjv⟩
      exact ⟨hGY.elem j, hjv⟩
    have difficult : M.Aᵀ.range ≤ Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range
    · by_contra contr
      obtain ⟨v, ⟨j, hjv⟩, hvG⟩ : ∃ v : M.X → R, v ∈ M.Aᵀ.range ∧ v ∉ Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range :=
        Set.not_subset.→ contr
      have hj : j.val ∉ G
      · intro hjG
        apply hvG
        have hv : v ∈ (M.Aᵀ.submatrix hGY.elem id).range
        · aesop
        rw [Submodule.mem_span]
        exact ↓(· hv)
      have hMvG : M.toMatroid.Indep (j.val ᕃ G)
      · obtain ⟨-, hAG⟩ := hMG.indep
        use Set.insert_subset_iff.← ⟨j.property, hGY⟩
        convert_to LinearIndepOn R M.Aᵀ (j ᕃ (M.Y ↓∩ G))
        · aesop
        rw [linearIndepOn_insert_iff]
        use hAG
        intro hjR
        exfalso
        apply hvG
        rw [←hjv]
        convert hjR
        aesop
      exact M.toMatroid.base_not_ssubset_indep hMG hMvG (Set.ssubset_insert hj)
    exact le_antisymm (Submodule.span_mono easy) (Submodule.span_le.← difficult)
  obtain ⟨-, lin_indep⟩ := hMG.indep
  let B : Basis G R (Submodule.span R M.Aᵀ.range)
  · apply Basis.mk (v := fun j : G.Elem => ⟨M.Aᵀ (hGY.elem j), in_submoduleSpan_range M.Aᵀ (hGY.elem j)⟩)
    · unfold LinearIndepOn at lin_indep
      rw [linearIndependent_iff'] at lin_indep ⊢
      intro s g hsg i hi
      let e : (M.Y ↓∩ G).Elem ≃ G.Elem :=
        ⟨G.restrictPreimage Subtype.val, (⟨hGY.elem ·, by simp⟩), congr_fun rfl, congr_fun rfl⟩
      have hsA : ∑ i ∈ s.map e.symm.toEmbedding, (g ∘ e) i • M.Aᵀ i = 0
      · rw [Subtype.ext_iff_val, ZeroMemClass.coe_zero] at hsg
        rw [←hsg]
        convert_to ∑ x ∈ s, g x • M.Aᵀ (e.symm x) = ∑ x ∈ s, g x • M.Aᵀ (hGY.elem x)
        · simp
        · simp
        rfl
      exact lin_indep (s.map e.symm.toEmbedding) (g ∘ e) hsA (e.symm i) (Finset.mem_map_equiv.← hi)
    · apply le_of_eq
      -- Christian Merten's idea:
      apply Submodule.map_injective_of_injective (Submodule.span R M.Aᵀ.range).subtype_injective
      simp [Submodule.map_span, ←hRAGY, ←Set.range_comp, Function.comp_def]
      rfl
  let C : Matrix G M.Y R := Matrix.of (fun i : G => fun j : M.Y => B.coord i ⟨M.Aᵀ j, in_submoduleSpan_range M.Aᵀ j⟩)
  have hYGY : M.Y \ G ⊆ M.Y := Set.diff_subset
  use ⟨G, M.Y \ G, Set.disjoint_sdiff_right, C.submatrix id hYGY.elem,
    (Classical.propDecidable <| · ∈ G), (Classical.propDecidable <| · ∈ M.Y \ G)⟩
  constructor
  · simp
  ext I hIGY
  · aesop
  have hB :
    ∀ j : α, ∀ g : G, ∀ hjy : j ∈ M.Y, ∀ hjg : j ∈ G, ∀ hjR : M.Aᵀ ⟨j, hjy⟩ ∈ Submodule.span R M.Aᵀ.range,
      B.repr ⟨M.Aᵀ ⟨j, hjy⟩, hjR⟩ g = B.repr (B ⟨j, hjg⟩) g
  · simp [B]
  simp only [StandardRepr.toMatroid_indep_iff_elem', VectorMatroid.toMatroid_indep_iff_elem,
    Matrix.one_fromCols_transpose, Matrix.transpose_submatrix, Set.union_diff_self]
  have hGYY : G ∪ M.Y = M.Y := Set.union_eq_self_of_subset_left hGY
  constructor
  · intro ⟨hI, hRCI⟩
    use hGYY ▸ hI
    classical
    apply exists_standardRepr_isBase_aux_right hGY hYGY (hGYY ▸ hI) hIGY hB
    convert hRCI
  · intro ⟨hI, hRAI⟩
    use hGYY.symm ▸ hI
    classical
    convert exists_standardRepr_isBase_aux_left hGY hYGY hI hIGY hB hRAI

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr [DivisionRing R] (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, S.toMatroid = M.toMatroid := by
  peel M.exists_standardRepr_isBase M.toMatroid.exists_isBase.choose_spec with hS
  exact hS.right

lemma VectorMatroid.exists_lin_indep_rows [Field R] (V : VectorMatroid α R) :
    ∃ W : VectorMatroid α R, V.toMatroid = W.toMatroid ∧ LinearIndependent R W.A := by
  sorry

lemma VectorMatroid.exists_lin_indep_rows_TU [Field R] (V : VectorMatroid α R) (hVA : V.A.IsTotallyUnimodular) :
    ∃ W : VectorMatroid α R, V.toMatroid = W.toMatroid ∧ LinearIndependent R W.A ∧ W.A.IsTotallyUnimodular := by
  sorry

lemma VectorMatroid.exists_lin_indep_rows_isBase_TU [Field R] {G : Set α}
    (V : VectorMatroid α R) (hVG : V.toMatroid.IsBase G) (hVA : V.A.IsTotallyUnimodular) :
    ∃ W : VectorMatroid α R, V.toMatroid = W.toMatroid ∧ LinearIndependent R W.A ∧ W.X = G ∧ W.A.IsTotallyUnimodular := by
  sorry

/-- Every vector matroid whose full representation matrix is totally unimodular has a standard representation whose rows are
    a given base and the standard representation matrix is totally unimodular. -/
lemma VectorMatroid.exists_standardRepr_isBase_isTotallyUnimodular [Field R] {G : Set α}
    (V : VectorMatroid α R) (hVG : V.toMatroid.IsBase G) (hVA : V.A.IsTotallyUnimodular) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = V.toMatroid ∧ S.B.IsTotallyUnimodular := by
  have hGV : G ⊆ V.Y := hVG.subset_ground
  -- 1. delete linearly dependent rows
  obtain ⟨W, hVW, hW, hWG, hWtu⟩ := V.exists_lin_indep_rows_isBase_TU hVG hVA
  have hGW : G ⊆ W.Y := vectorMatroid_toMatroid_Y_congr hVW ▸ hGV
  have : Fintype G := sorry
  wlog hG : 0 < #G
  · rw [not_lt, nonpos_iff_eq_zero, ← Set.toFinset_card, Finset.card_eq_zero, Set.toFinset_eq_empty] at hG
    use StandardRepr.loopy R V.Y
    subst hG
    simpa using (Matroid.not_rankPos_iff.→ ((not_congr (Matroid.rankPos_iff V.toMatroid)).← (· hVG))).symm
  let f : Fin #G → G := (Fintype.equivFin G).invFun
  have indu : ∀ k : ℕ, ∀ hk : k ≤ #G, ∃ W' : VectorMatroid α R,
    W'.toMatroid = W.toMatroid ∧ W'.A.IsTotallyUnimodular ∧ ∃ hGX' : G = W'.X, ∃ hGY' : G ⊆ W'.Y,
      ∀ j : Fin k, ∀ g : G,
        if g = f ⟨j.val, by omega⟩
        then W'.A (hGX' ▸ g) (hGY'.elem (f ⟨j.val, by omega⟩)) = 1
        else W'.A (hGX' ▸ g) (hGY'.elem (f ⟨j.val, by omega⟩)) = 0
  · intro k
    induction k with
    | zero =>
      intro _
      use W, rfl, hWtu, hWG.symm, hGW
      intro ⟨_, _⟩
      omega
    | succ n ih =>
      intro hn
      obtain ⟨W', hWW, hW'tu, hGX', hGY', hfW'⟩ := ih (by omega)
      obtain ⟨i, hi⟩ : ∃ i : W'.X, W'.A i (hGY'.elem (f ⟨n, by omega⟩)) ≠ 0
      · sorry
      use ⟨W'.X, W'.Y, W'.A.longTableauPivot i (hGY'.elem (f ⟨n, by omega⟩))⟩
      constructor
      · rw [←hWW]
        ext I hI
        · simp
        · rw [VectorMatroid.toMatroid_indep_iff_elem, VectorMatroid.toMatroid_indep_iff_elem]
          congr! 2 with hIY
          sorry -- pivoting preserves linear (in)dependence of columns
      refine ⟨hW'tu.longTableauPivot i _ hi, hGX', hGY', ?_⟩
      -- previous columns are unaffected because the element in the pivot row was already `0`
      -- new column is by definition of the long-tableau pivot
      sorry
  obtain ⟨W', hWW, hW'tu, hGX', hGY', hfW'⟩ := indu #G (by rfl)
  let I : Matrix G G R := W'.A.submatrix hGX'.≃ hGY'.elem
  have hYGY : W'.Y \ G ⊆ W'.Y := Set.diff_subset
  use ⟨_, _, Set.disjoint_sdiff_right, W'.A.submatrix hGX'.≃ hYGY.elem,
    G.decidableMemOfFintype, (Classical.propDecidable <| · ∈ W'.Y \ G)⟩
  refine ⟨by simp, ?_, hW'tu.submatrix hGX'.≃ hYGY.elem⟩
  rw [hVW, ←hWW]
  -- let B : Basis G R (Submodule.span R W'.Aᵀ.range)
  -- · apply Basis.mk (v := fun j : G.Elem => ⟨W'.Aᵀ (hGY'.elem j), in_submoduleSpan_range W'.Aᵀ (hGY'.elem j)⟩)
  --   · sorry
  --   · sorry
  ext I hIGYG
  · exact (congr_fun (Set.union_diff_cancel' ↓id hGY') _).to_iff
  · dsimp at hIGYG
    simp only [StandardRepr.toMatroid_indep_iff_elem', VectorMatroid.toMatroid_indep_iff_elem, Set.union_diff_self,
      Matrix.one_fromCols_transpose, Matrix.transpose_submatrix]
    have hGYY : G ∪ W'.Y = W'.Y := Set.union_eq_self_of_subset_left hGY'
    constructor
    · intro ⟨hIGY, hRAI⟩
      use hGYY ▸ hIGY
      sorry
    · intro ⟨hI, hRAI⟩
      use hGYY.symm ▸ hI
      sorry

/-- The identity matrix has linearly independent rows. -/
lemma Matrix.one_linearIndependent [Ring R] : LinearIndependent R (1 : Matrix α α R) := by
  -- Riccardo Brasca proved:
  rw [linearIndependent_iff]
  intro l hl
  ext j
  simpa [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum_apply', Matrix.one_apply] using congr_fun hl j

/-- The set of all rows of a standard representation is a base in the resulting matroid. -/
lemma StandardRepr.toMatroid_isBase_X [Field R] (S : StandardRepr α R) [Fintype S.X] :
    S.toMatroid.IsBase S.X := by
  apply Matroid.Indep.isBase_of_forall_insert
  · rw [StandardRepr.toMatroid_indep_iff_submatrix]
    use Set.subset_union_left
    simp [Matrix.submatrix]
    show @LinearIndependent S.X R _ 1ᵀ ..
    rw [Matrix.transpose_one]
    exact Matrix.one_linearIndependent
  · intro e he
    rw [StandardRepr.toMatroid_indep_iff_submatrix]
    push_neg
    intro _
    apply Matrix.not_linearIndependent_of_too_many_rows
    have heX : e ∉ S.X.toFinset := (Set.not_mem_of_mem_diff he <| Set.mem_toFinset.→ ·)
    simp [heX]

omit R

private lemma sum_support_image_subtype_eq_zero {X Y : Set α} {F : Type} [Field F] {B : Matrix Y X F} {D : Set X} {y : Y}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} (hXXY : X ⊆ X ∪ Y) (hYXY : Y ⊆ X ∪ Y) -- redundant but keep
    {l : (X ∪ Y).Elem →₀ F} (hl : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D) (hly : l (hYXY.elem y) = 0)
    {i : (X ∪ Y).Elem} (hiX : i.val ∈ X) (hlBi : ∑ a ∈ l.support, l a • (1 ⊟ B) a.toSum ⟨i, hiX⟩ = 0) :
    ∑ a ∈ (l.support.image Subtype.val).subtype (· ∈ X),
      l (hXXY.elem a) • (1 ⊟ B) (hXXY.elem a).toSum ⟨i, hiX⟩ = 0 := by
  rw [←Finset.sum_finset_coe] at hlBi
  convert hlBi
  apply Finset.sum_bij (fun a ha => ⟨hXXY.elem a, by simpa using ha⟩)
  · simp
  · simp
  · intro z _
    simp only [HasSubset.Subset.elem, Finset.coe_sort_coe, Finset.mem_subtype, Finset.mem_image, Finsupp.mem_support_iff,
      Subtype.exists, Subtype.coe_prop, Set.mem_union, exists_and_right, exists_true_left, exists_eq_right, true_or]
    use z
    simp only [exists_prop, and_true]
    refine ⟨?_, (l.mem_support_toFun z).→ (by simp)⟩
    have hzD : z.val.val ∈ Subtype.val '' D
    · cases hl z (by simp) with
      | inl hp =>
        have hzy : z.val = hYXY.elem y := Subtype.coe_inj.→ hp
        rw [←hzy] at hly
        exact absurd hly (l.mem_support_iff.→ (by simp))
      | inr hp => exact hp
    have hDX : Subtype.val '' D ⊆ X
    · rw [Set.image, Set.setOf_subset]
      rintro _ ⟨⟨_, ha⟩, ⟨_, rfl⟩⟩
      exact ha
    exact Set.mem_of_mem_of_subset hzD hDX
  · intros
    rfl

set_option maxHeartbeats 1000000 in
private lemma support_eq_support_of_same_matroid_aux {F₁ F₂ : Type} [Field F₁] [Field F₂] [DecidableEq F₁] [DecidableEq F₂]
    {X Y : Set α} {hXY : X ⫗ Y} {B₁ : Matrix X Y F₁} {B₂ : Matrix X Y F₂}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
    (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
    B₁.support = B₂.support := by
  rw [←Matrix.transpose_inj]
  apply Matrix.ext_col
  intro y
  have hXXY : X ⊆ X ∪ Y := Set.subset_union_left
  have hYXY : Y ⊆ X ∪ Y := Set.subset_union_right
  have hSS' := congr_arg Matroid.Indep hSS
  let D₁ := { x : X | B₁ᵀ y x ≠ 0 }
  let D₂ := { x : X | B₂ᵀ y x ≠ 0 }
  suffices hDD : D₁ = D₂
  · ext x
    if hx₁ : B₁ᵀ y x = 0 then
      have hx₂ : x ∉ D₂
      · rw [←hDD]
        simp_rw [D₁, Set.mem_setOf_eq, not_not]
        exact hx₁
      simp_all [D₂]
    else
      have hx₂ : x ∈ D₂
      · rw [←hDD]
        simp_rw [D₁, Set.mem_setOf_eq]
        exact hx₁
      simp_all [D₂]
  apply Set.eq_of_subset_of_subset
  on_goal 1 => let D := D₁; let Dₒ := D₂; let B := B₁; let Bₒ := B₂; let F := F₁; let F₀ := F₂
  on_goal 2 => let D := D₂; let Dₒ := D₁; let B := B₂; let Bₒ := B₁; let F := F₂; let F₀ := F₁
  all_goals
  · by_contra hD
    rw [Set.not_subset_iff_exists_mem_not_mem] at hD
    -- otherwise `y ᕃ Dₒ` is dependent in `Mₒ` but indep in `M`
    have hMₒ : ¬ (StandardRepr.mk X Y hXY Bₒ hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · rw [StandardRepr.toMatroid_indep_iff_elem', not_exists]
      intro hDₒ
      erw [not_linearIndependent_iff]
      refine ⟨Finset.univ, (·.val.toSum.casesOn (- Bₒᵀ y) 1), ?_, ⟨hYXY.elem y, by simp_all⟩, Finset.mem_univ _, by
        dsimp only
        cases _ : (hYXY.elem y).toSum with
        | inl => simp_all [Subtype.toSum, hXY.not_mem_of_mem_right y.property]
        | inr => exact ne_zero_of_eq_one rfl⟩
      ext x
      simp only at x hDₒ
      simp_rw [Function.comp_apply]
      rw [Finset.sum_apply]
      show ∑ i : hDₒ.elem.range.Elem, (i.val.toSum.casesOn (- Bₒᵀ y) 1 : F₀) • (1 ◫ Bₒ) x i.val.toSum = 0
      suffices separated : Bₒ x y + ∑ i : Dₒ.Elem, (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i.val = 0
      · rw [Finset.sum_set_coe (f := (fun i : (X ∪ Y).Elem => (i.toSum.casesOn (- Bₒᵀ y) 1 : F₀) • (1 ◫ Bₒ) x i.toSum)),
          Set.toFinset_range,
          show Finset.univ.image hDₒ.elem = hYXY.elem y ᕃ Finset.map ⟨hXXY.elem, hXXY.elem_injective⟩ { x : X | Bₒᵀ y x ≠ 0 } by
            aesop,
          Finset.sum_insert (by
            simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_map, exists_and_right, not_exists, not_not]
            intro a ⟨_, contradictory⟩
            have hay : a.val = y.val
            · simpa using contradictory
            have impossible : y.val ∈ X ∩ Y := ⟨hay ▸ a.property, y.property⟩
            rw [hXY.inter_eq] at impossible
            exact impossible)]
        convert separated
        · convert_to ((1 : Matrix X X F₀) ◫ Bₒ) x ◪y = Bₒ x y
          · cases _ : (hYXY.elem y).toSum <;> simp_all [Subtype.toSum, hXY.not_mem_of_mem_right y.property]
          rfl
        · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, HasSubset.Subset.elem, Subtype.coe_prop, toSum_left]
          show
            ∑ i ∈ Finset.univ.filter (fun x : X => Bₒ x y ≠ 0), (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i =
            ∑ i : { x : X // Bₒ x y ≠ 0 }, (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i
          apply Finset.sum_subtype
          simp
      if hx : x ∈ Dₒ then
        exact add_eq_zero_iff_eq_neg'.← (sum_elem_smul_matrix_row_of_mem (- Bₒᵀ y) hx)
      else
        convert_to 0 + 0 = (0 : F₀) using 2
        · simpa [Dₒ, D₁, D₂] using hx
        · exact sum_elem_smul_matrix_row_of_nmem (- Bₒᵀ y) hx
        simp
    have hM : (StandardRepr.mk X Y hXY B hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · obtain ⟨d, hd, hd₀⟩ := hD
      simp
      have hDXY : Subtype.val '' Dₒ ⊆ X ∪ Y := (Subtype.coe_image_subset X Dₒ).trans hXXY
      have hyXY : y.val ∈ X ∪ Y := hYXY y.property
      have hyDXY : y.val ᕃ Subtype.val '' Dₒ ⊆ X ∪ Y := Set.insert_subset hyXY hDXY
      use Set.insert_subset hyXY hDXY
      rw [linearIndepOn_iff]
      intro l hl hlB
      have hl' : l.support.toSet ⊆ hyDXY.elem.range
      · rwa [Finsupp.mem_supported] at hl
      have hl'' : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' Dₒ :=
        fun e he => (hyDXY.elem_range ▸ hl') he
      if hly : l (hYXY.elem y) = 0 then
        ext i
        if hil : i ∈ l.support then
          if hiX : i.val ∈ X then
            have hlBiX := congr_fun hlB ⟨i.val, hiX⟩
            rw [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum, Finset.sum_apply] at hlBiX
            simp_rw [Pi.smul_apply, Function.comp_apply] at hlBiX
            have hlBi : ∑ x ∈ (l.support.image Subtype.val).subtype (· ∈ X), l (hXXY.elem x) • (1 : Matrix X X F) x ⟨i, hiX⟩ = 0
            · simpa using sum_support_image_subtype_eq_zero hXXY hYXY hl'' hly hiX hlBiX
            rwa [
              ((l.support.image Subtype.val).subtype (· ∈ X)).sum_of_single_nonzero
                (fun a : X.Elem => l (hXXY.elem a) • (1 : Matrix X X F) a ⟨i, hiX⟩)
                ⟨i, hiX⟩ (by simp_all) ↓↓↓(by simp_all),
              Matrix.one_apply_eq,
              smul_eq_mul,
              mul_one
            ] at hlBi
          else if hiY : i.val ∈ Y then
            have hiy : i = hYXY.elem y
            · cases hl'' i hil with
              | inl hiy => exact SetCoe.ext hiy
              | inr hiD => simp_all
            rw [hiy]
            exact hly
          else
            exfalso
            exact i.property.casesOn hiX hiY
        else
          exact l.not_mem_support_iff.→ hil
      else
        exfalso
        have hlBd := congr_fun hlB d
        rw [Finsupp.linearCombination_apply] at hlBd
        have hlBd' : l.sum (fun i a => a • Matrix.fromRows 1 Bᵀ i.toSum d) = 0
        · simpa [Finsupp.sum] using hlBd
        have untransposed : l.sum (fun i a => a • ((1 : Matrix X X F) ◫ B) d i.toSum) = 0
        · rwa [←Matrix.transpose_transpose (1 ◫ B), Matrix.one_fromCols_transpose]
        have hyl : hYXY.elem y ∈ l.support
        · rwa [Finsupp.mem_support_iff]
        have h0 : ∀ a ∈ l.support, a.val ≠ y.val → l a • ((1 : Matrix X X F) ◫ B) d a.toSum = 0
        · intro a ha hay
          have hal := hl'' a ha
          if haX : a.val ∈ X then
            convert_to l a • ((1 : Matrix X X F) ◫ B) d ◩⟨a.val, haX⟩ = 0
            · simp [Subtype.toSum, haX]
            simp_rw [Matrix.fromCols_apply_inl]
            rw [smul_eq_mul, mul_eq_zero]
            right
            apply Matrix.one_apply_ne
            intro had
            rw [had] at hd
            apply hd
            aesop
          else if haY : a.val ∈ Y then
            exfalso
            cases hal with
            | inl hay' => exact hay hay'
            | inr haDₒ => simp_all
          else
            exfalso
            exact a.property.casesOn haX haY
        have hlyd : l (hYXY.elem y) • ((1 : Matrix X X F) ◫ B) d (hYXY.elem y).toSum ≠ 0
        · intro contr
          refine hly ((mul_eq_zero_iff_right ?_).→ contr)
          have := hXY.not_mem_of_mem_right y.property
          simp_all [B, Dₒ, D₁, D₂]
        rw [Finsupp.sum,
          l.support.sum_of_single_nonzero (fun a : (X ∪ Y).Elem => l a • (1 ◫ B) d a.toSum) (hYXY.elem y) hyl]
        at untransposed
        · rw [untransposed] at hlyd
          exact hlyd rfl
        intro i hil hiy
        apply h0 i hil
        intro contr
        apply hiy
        exact SetCoe.ext contr
    exact (hSS' ▸ hMₒ) hM

-- lemma Matrix.support_Z2 {X Y : Type} (A : Matrix X Y Z2) : A.support = A := by
--   aesop

-- private lemma B_eq_B_of_same_matroid_same_X {X Y : Set α} {hXY : X ⫗ Y} {B₁ B₂ : Matrix X Y Z2}
--     {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
--     (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
--     B₁ = B₂ := by
--   rw [←B₁.support_Z2, ←B₂.support_Z2]
--   exact support_eq_support_of_same_matroid_aux hSS

-- /-- If two standard representations of the same binary matroid have the same base, they are identical. -/
-- lemma ext_standardRepr_of_same_matroid_same_X {S₁ S₂ : StandardRepr α Z2} [Fintype S₁.X]
--     (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
--     S₁ = S₂ := by
--   have hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
--   apply standardRepr_eq_standardRepr_of_B_eq_B hXX hYY
--   apply B_eq_B_of_same_matroid_same_X
--   convert hSS
--   cc

/-- If two standard representations of the same matroid have the same base, then the standard representation matrices have
    the same support. -/
lemma support_eq_support_of_same_matroid_same_X {F₁ F₂ : Type} [Field F₁] [Field F₂] [DecidableEq F₁] [DecidableEq F₂]
    {S₁ : StandardRepr α F₁} {S₂ : StandardRepr α F₂} [Fintype S₂.X]
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    let hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
    hXX ▸ hYY ▸ S₁.B.support = S₂.B.support := by
  intro hYY
  obtain ⟨X₁, Y₁, _, B₁, _, _⟩ := S₁
  obtain ⟨X₂, Y₂, _, B₂, _, _⟩ := S₂
  simp only at hXX hYY
  let B₀ := hXX ▸ hYY ▸ B₁
  have hB₀ : B₀ = hXX ▸ hYY ▸ B₁
  · rfl
  convert_to B₀.support = B₂.support
  · cc
  have hSS' : (StandardRepr.mk X₂ Y₂ _ B₀ _ _).toMatroid = (StandardRepr.mk X₂ Y₂ _ B₂ _ _).toMatroid
  · convert hSS <;> cc
  exact support_eq_support_of_same_matroid_aux hSS'
