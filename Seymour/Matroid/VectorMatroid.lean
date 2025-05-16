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

open scoped Matrix Set.Notation


-- ## Vector matroid defined by its full matrix representation

/-- Predicate of linear independence of a set of rows of a matrix. -/
def Matrix.linearIndepRows {α R : Type} [Semiring R] {X Y : Set α} (A : Matrix X Y R) : Set α → Prop :=
  fun I : Set α => I ⊆ X ∧ LinearIndepOn R A (X ↓∩ I)

/-- Equivalent definition of linear independence of rows via `Subset.elem.range`. -/
@[simp]
lemma Matrix.linearIndepRows_iff_elem {α R : Type} [Semiring R] {X Y : Set α} (A : Matrix X Y R) (I : Set α) :
    A.linearIndepRows I ↔ ∃ hI : I ⊆ X, LinearIndepOn R A hI.elem.range := by
  unfold HasSubset.Subset.elem
  simp_all only [Function.range, Set.range_inclusion, exists_prop]
  rfl

/-- Equivalent definition of linear independence of rows via `Matrix.submatrix`. -/
lemma Matrix.linearIndepRows_iff_submatrix {α R : Type} [Semiring R] {X Y : Set α} (A : Matrix X Y R) (I : Set α) :
    A.linearIndepRows I ↔ ∃ hI : I ⊆ X, LinearIndependent R (A.submatrix hI.elem id) := by
  constructor
  <;> intro ⟨hI, hAI⟩
  <;> use hI
  <;> let e : I ≃ X ↓∩ I := (Equiv.ofInjective hI.elem hI.elem_injective).trans hI.elem_range.≃
  · exact (linearIndependent_equiv' e rfl).← hAI
  · exact (linearIndependent_equiv' e rfl).→ hAI

/-- Empty set of rows is linearly independent. -/
lemma Matrix.linearIndepRows_empty {α R : Type} [Semiring R] {X Y : Set α} (A : Matrix X Y R) :
    A.linearIndepRows ∅ :=
  ⟨X.empty_subset, linearIndepOn_empty _ _⟩

/-- Intersections with `X` on the left viewed as sets in `Set X` respect taking subsets. -/
private lemma inter_subtype_left_subset {α : Type} {X I J : Set α} (hIJ : I ⊆ J) :
    X ↓∩ I ⊆ X ↓∩ J :=
  fun _ hx => hIJ hx

/-- Subset of a lineraly independent set of rows is also linearly independent. -/
lemma Matrix.linearIndepRows_subset {α R : Type} [Semiring R] {X Y : Set α} {A : Matrix X Y R} {I J : Set α}
    (hJ : A.linearIndepRows J) (hIJ : I ⊆ J) :
    A.linearIndepRows I :=
  ⟨hIJ.trans hJ.left, hJ.right.comp (inter_subtype_left_subset hIJ).elem ((inter_subtype_left_subset hIJ).elem_injective)⟩

/-- Non-maximal linearly independent set of rows can be augmented with a row from a maximal linearly independent set of rows.

To see why `DivisionRing` is necessary, consider `(!![0, 1, 2, 3; 1, 0, 3, 2] : Matrix (Fin 2) (Fin 4) (ZMod 6))`. Here
`{0}` is non-maximal independent,  `{2, 3}` is maximal independent, but neither `{0, 2}` nor `{0, 3}` is independent. -/
lemma Matrix.linearIndepRows_aug {α R : Type} [DivisionRing R] {X Y : Set α} {A : Matrix X Y R} {I J : Set α}
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
    have xJ_ss_J : ↑x ᕃ J ⊆ J := hJ' M_indep_xJ (Set.subset_insert ↑x J)
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
    · simp_all only [Set.mem_diff, Matrix.linearIndepRows_iff_elem, Function.range, not_exists, and_imp, exists_true_left,
        Set.le_eq_subset, forall_exists_index, Set.image_subset_iff, Set.mem_setOf_eq, Iᵥ, Jᵥ, J', Iₛ, I', Jₛ, k']
      simp_all only [Iᵥ]
      obtain ⟨val, property⟩ := k'
      obtain ⟨w, h⟩ := hK
      ext x : 1
      simp_all only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_setOf_eq, Iᵥ]
      obtain ⟨val_1, property_1⟩ := x
      simp_all only [Subtype.mk.injEq, Iᵥ]
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
        · simp_all only [Set.mem_diff, Matrix.linearIndepRows_iff_elem, Function.range, not_exists, and_imp, exists_true_left,
        Set.le_eq_subset, forall_exists_index, Set.image_subset_iff, Set.mem_setOf_eq, Iᵥ, Jᵥ, J', Iₛ, I', Jₛ, k']
          simp_all only [not_false_eq_true, k', I', Jₛ, Jᵥ, J', Iᵥ, Iₛ]
          obtain ⟨val, property⟩ := k'
          obtain ⟨w, h⟩ := hK
          ext x : 1
          simp_all only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_setOf_eq, I', Jₛ, Jᵥ, J', Iᵥ, Iₛ]
          obtain ⟨val_1, property_1⟩ := x
          simp_all only [Subtype.mk.injEq, I', Jₛ, Jᵥ, J', Iᵥ, Iₛ]
        rw [hkJ]
        exact kJ'_indep
    have kJ_ss_J : k ᕃ J ⊆ J := hJ' hMkJ (Set.subset_insert k J)
    exact hkJ' (kJ_ss_J (J.mem_insert k))

private lemma linearIndepOn_sUnion_of_directedOn {α R : Type} [Semiring R] {X Y : Set α} {A : Matrix Y X R} {s : Set (Set α)}
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
lemma Matrix.linearIndepRows_maximal {α R : Type} [Semiring R] {X Y : Set α} (A : Matrix X Y R) (I : Set α) :
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
private def Matrix.toIndepMatroid {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) : IndepMatroid α where
  E := X
  Indep := A.linearIndepRows
  indep_empty := A.linearIndepRows_empty
  indep_subset _ _ hJ hIJ := Matrix.linearIndepRows_subset hJ hIJ
  indep_aug _ _ hI hI' hJ := A.linearIndepRows_aug hI hI' hJ
  indep_maximal S _ := A.linearIndepRows_maximal S
  subset_ground _ := And.left

/-- Vector matroid converted to `Matroid`. -/
def Matrix.toMatroid {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) : Matroid α :=
  A.toIndepMatroid.matroid

@[simp]
lemma Matrix.toMatroid_E {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) :
    A.toMatroid.E = X :=
  rfl

@[simp low]
lemma Matrix.toMatroid_indep {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) :
    A.toMatroid.Indep = A.linearIndepRows :=
  rfl

lemma Matrix.toMatroid_X_congr {α R : Type} [DivisionRing R] {X Y X' Y' : Set α} {A : Matrix X Y R} {B : Matrix X' Y' R}
    (hAB : A.toMatroid = B.toMatroid) :
    X = X' :=
  congr_arg Matroid.E hAB

/-- Vector matroids are finitary. -/
lemma Matrix.toMatroid_Finitary {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) :
    A.toMatroid.Finitary := by
  constructor
  intro I hI
  wlog hIY : I ⊆ A.toMatroid.E
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

/-- Result of remapping a vector matroid from type `α` to equivalent type `β`. -/
lemma Matrix.toMatroid_mapEquiv_eq {α R : Type} [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) {β : Type} (e : α ≃ β) :
    A.toMatroid.mapEquiv e = (A.submatrix (e.image X).symm (e.image Y).symm).toMatroid := by
  apply Matroid.ext_indep (A.toMatroid.mapEquiv_ground_eq e)
  intro I hIE
  rw [A.toMatroid.mapEquiv_indep_iff, (A.submatrix (e.image X).symm (e.image Y).symm).toMatroid_indep,
    A.toMatroid_indep, Matrix.linearIndepRows, Matrix.linearIndepRows, Equiv.symm_image_subset]
  constructor
  all_goals
    apply And.imp_right
    intro hI
    rw [linearIndepOn_iff] at hI ⊢
    intro s hs hss
  on_goal 2 => refine Finsupp.embDomain_eq_zero.→ (hI (Finsupp.embDomain (e.image X) s) ?_ ?_)
  on_goal 1 => refine Finsupp.embDomain_eq_zero.→ (hI (Finsupp.embDomain (e.image X).symm s) ?_ ?_)
  on_goal 4 =>
    rw [Finsupp.linearCombination_embDomain]
    show (Finsupp.linearCombination R (A.submatrix ((e.image X).symm ∘ e.image X) (e.image Y).symm)) s = 0
    rw [Equiv.symm_comp_self]
    ext y
    rw [funext_iff] at hss
    specialize hss ⟨(e.image Y).symm y, (Set.mem_image_equiv).→ y.prop⟩
    rw [Pi.zero_apply] at hss ⊢
    rw [←hss, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum.eq_1, Finsupp.sum.eq_1]
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.submatrix_apply, id_eq,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_id_id, Equiv.image_symm_apply_coe]
    rfl
  on_goal 2 =>
    rw [Finsupp.linearCombination_embDomain]
    ext y
    rw [funext_iff] at hss
    specialize hss ⟨e.image Y y, Subtype.coe_prop ((e.image Y) y)⟩
    rw [Pi.zero_apply] at hss ⊢
    rw [←hss, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum.eq_1, Finsupp.sum.eq_1]
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, smul_eq_mul, id_eq,
      Equiv.image_apply_coe,
      show ((e.image Y).symm ⟨e y, by simp⟩) = y by
        apply_fun e.image Y
        rw [Equiv.apply_symm_apply]
        rfl]
    rfl
  all_goals
    rw [Finsupp.mem_supported] at hs ⊢
    simp_rw [Finsupp.support_embDomain, Finset.coe_map, Set.image_subset_iff] at hs ⊢
    apply subset_of_subset_of_eq hs
    ext y
    simp_rw [Set.mem_preimage, Set.mem_image_equiv, Equiv.symm_symm]
  · rw [show ((e.image X).symm.toEmbedding y) = ⟨e.symm y, Set.mem_image_equiv.→ y.prop⟩
        by apply_fun (Equiv.Set.image e X e.injective); simp,
      Equiv.apply_symm_apply]
  · rfl


-- ## Vector matroid given by a full representation matrix is the same as the one given by the support matrix

private lemma Matrix.IsTotallyUnimodular.intCast_det_eq_support_det {X : Type} [DecidableEq X] [Fintype X] {A : Matrix X X ℤ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.support.det := by
  rw [Matrix.det_int_coe]
  congr
  ext i j
  simp only [Matrix.support, Matrix.map, Matrix.of_apply]
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [←hs, SignType.intCast_cast]
  cases s <;> rfl

private lemma Matrix.IsTotallyUnimodular.ratCast_det_eq_support_det {X : Type} [DecidableEq X] [Fintype X] {A : Matrix X X ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.support.det := by
  rw [hA.det_eq_map_ratFloor_det, Rat.cast_intCast, hA.map_ratFloor.intCast_det_eq_support_det]
  congr
  ext i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.support, Matrix.of_apply, Matrix.of_apply, Matrix.map_apply, ←hs]
  cases s <;> rfl

private lemma Matrix.IsTotallyUnimodular.det_eq_zero_iff_support {X : Type} [DecidableEq X] [Fintype X] {A : Matrix X X ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det = (0 : ℚ) ↔ A.support.det = (0 : Z2) := by
  rw [←hA.ratCast_det_eq_support_det]
  apply zero_iff_ratCast_zero_of_in_signTypeCastRange
  exact hA.det id id

private lemma Matrix.IsTotallyUnimodular.det_ne_zero_iff_support {X : Type} [DecidableEq X] [Fintype X] {A : Matrix X X ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det ≠ (0 : ℚ) ↔ A.support.det ≠ (0 : Z2) :=
  hA.det_eq_zero_iff_support.ne

private def Matrix.AllColsIn {X Y R : Type} (A : Matrix X Y R) (Y' : Set Y) : Prop :=
  ∀ y : Y, ∃ y' : Y', (A · y) = (A · y')

@[app_unexpander Matrix.AllColsIn]
private def Matrix.AllColsIn_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `AllColsIn))
  | _ => throw ()

private lemma Matrix.exists_finite_allColsIn {X Y R : Type} [Fintype X] [DecidableEq Y] (A : Matrix X Y R) (V : Finset R)
    (hAV : ∀ i : X, ∀ j : Y, A i j ∈ V) :
    ∃ Y' : Set Y, Finite Y' ∧ A.AllColsIn Y' := by
  let C : Set (X → R) := { (A · y) | y : Y }
  let Y' : Set Y := { Classical.choose hc | (c : X → R) (hc : c ∈ C) }
  use Y'
  constructor
  · let S : Set (X → V) := Set.univ
    let S' : Set (X → R) := (fun v : X → V => fun x : X => (v x).val) '' S
    have hCS' : C ⊆ S' := by
      rintro - ⟨w, rfl⟩
      exact ⟨(fun j => ⟨(A · w) j, hAV j w⟩), trivial, rfl⟩
    let e : Y' ↪ C := ⟨fun i : Y' => ⟨(A · i), by use i⟩, fun ⟨_, w₁, ⟨y₁, hy₁⟩, _⟩ ⟨_, w₂, ⟨y₂, hy₂⟩, _⟩ _ => by
      simp_all only [Subtype.mk.injEq, C, Y']
      subst hy₁ hy₂
      have := Classical.choose_spec (⟨y₁, rfl⟩ : ∃ y : Y, (A · y) = (A · y₁))
      have := Classical.choose_spec (⟨y₂, rfl⟩ : ∃ y : Y, (A · y) = (A · y₂))
      simp_all only⟩
    have S_finite : S.Finite := Subtype.finite
    have S'_finite : S'.Finite := S_finite.image (fun i : X => · i |>.val)
    exact (S'_finite.subset hCS').finite_of_encard_le e.encard_le
  · intro i
    have hi : (A · i) ∈ C := by use i
    use ⟨hi.choose, by aesop⟩
    exact hi.choose_spec.symm

private lemma Matrix.linearIndependent_if_LinearIndependent_subset_cols {X Y R : Type} [Ring R] {Y' : Set Y}
    (A : Matrix X Y R) (hA : LinearIndependent R (A.submatrix id (fun y' : Y' => y'.val))) :
    LinearIndependent R A := by
  by_contra lin_dep
  absurd hA
  rw [not_linearIndependent_iff] at lin_dep ⊢
  obtain ⟨s, c, hscA, hsc⟩ := lin_dep
  refine ⟨s, c, ?_, hsc⟩
  ext j
  convert congr_fun hscA j
  simp

private lemma Matrix.linearIndependent_iff_allColsSubmatrix_linearIndependent {X Y R : Type} [Ring R] {Y' : Set Y}
    (A : Matrix X Y R) (hAY' : A.AllColsIn Y') :
    LinearIndependent R A ↔ LinearIndependent R (A.submatrix id (fun y' : Y' => y'.val)) := by
  constructor
  · intro lin_indep
    by_contra lin_dep
    absurd lin_indep
    rw [not_linearIndependent_iff] at lin_dep ⊢
    obtain ⟨s, c, hscA, hsc⟩ := lin_dep
    refine ⟨s, c, ?_, hsc⟩
    ext j
    obtain ⟨y', hy'⟩ := hAY' j
    convert congr_fun hscA y'
    convert_to (∑ i ∈ s, c i • A i j) = (∑ i ∈ s, c i • A.submatrix id (·.val) i y')
    · apply Finset.sum_apply
    · apply Finset.sum_apply
    congr
    ext i
    rw [congr_fun hy' i]
    simp
  · exact A.linearIndependent_if_LinearIndependent_subset_cols

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_support_linearIndependent_of_finite_of_finite
    {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] (A : Matrix X Y ℚ) (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.support := by
  constructor
  <;> intro lin_indep
  <;> rw [Matrix.linearIndependent_iff_exists_submatrix_det] at lin_indep ⊢
  <;> obtain ⟨g, hAg⟩ := lin_indep
  <;> use g
  <;> have result := (hA.submatrix id g).det_ne_zero_iff_support
  · exact A.support_submatrix id g ▸ (result.→ hAg)
  · exact result.← (A.support_submatrix id g ▸ hAg)

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_support_linearIndependent_of_finite
    {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.support := by
  constructor
  <;> intro lin_indep
  · obtain ⟨Y', hY', hAY'⟩ := A.exists_finite_allColsIn {-1, 0, 1} (by have ⟨s, hs⟩ := hA.apply · · ; cases s <;> aesop)
    rw [A.linearIndependent_iff_allColsSubmatrix_linearIndependent hAY'] at lin_indep
    have := Set.Finite.fintype hY'
    rw [(hA.submatrix id Subtype.val).linearIndependent_iff_support_linearIndependent_of_finite_of_finite] at lin_indep
    exact A.support.linearIndependent_if_LinearIndependent_subset_cols lin_indep
  · obtain ⟨Y', hY', hAY'⟩ := A.support.exists_finite_allColsIn Finset.univ (Finset.mem_univ <| A.support · ·)
    rw [A.support.linearIndependent_iff_allColsSubmatrix_linearIndependent hAY'] at lin_indep
    rw [Matrix.support_submatrix] at lin_indep
    have := Set.Finite.fintype hY'
    rw [←(hA.submatrix id Subtype.val).linearIndependent_iff_support_linearIndependent_of_finite_of_finite] at lin_indep
    exact A.linearIndependent_if_LinearIndependent_subset_cols lin_indep

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_support_linearIndependent
    {X Y : Type} [DecidableEq X] [DecidableEq Y] {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.support := by
  constructor
  <;> intro lin_indep
  <;> rw [linearIndependent_iff_finset_linearIndependent] at lin_indep ⊢
  <;> intro s
  <;> specialize lin_indep s
  <;> have result := (hA.submatrix (@Subtype.val X (· ∈ s)) id).linearIndependent_iff_support_linearIndependent_of_finite
  · exact result.→ lin_indep
  · exact result.← lin_indep

/-- Vector matroids defined by a full representation matrix and its support are the same. -/
lemma Matrix.IsTotallyUnimodular.toMatroid_eq_support_toMatroid {α : Type} {X Y : Set α} [DecidableEq X] [DecidableEq Y]
    {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    A.toMatroid = A.support.toMatroid := by
  ext I hI
  · simp only [Matrix.toMatroid_E, Matrix.support]
  simp_rw [Matrix.toMatroid_indep, Matrix.linearIndepRows_iff_submatrix, Matrix.support_submatrix]
  have : DecidableEq I := Classical.typeDecidableEq I
  constructor <;> intro ⟨hIY, hAI⟩ <;> use hIY
  · rwa [(hA.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent] at hAI
  · rwa [(hA.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent]
