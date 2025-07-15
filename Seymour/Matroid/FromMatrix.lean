import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual
import Mathlib.Data.Matroid.Map
import Mathlib.Data.Matroid.Sum
import Seymour.Basic.Sets
import Seymour.Matrix.LinearIndependence

/-!
# Vector Matroids

Here we study vector matroids with emphasis on binary matroids.
-/

open scoped Matrix Set.Notation


variable {α R : Type*} {X Y : Set α}

/-- A set is independent in a vector matroid iff it corresponds to a linearly independent submultiset of columns. -/
def Matrix.IndepCols [Semiring R] (A : Matrix X Y R) (I : Set α) : Prop :=
  I ⊆ Y ∧ LinearIndepOn R Aᵀ (Y ↓∩ I)

/-- Our old (equivalent) definition. -/
private def Matrix.IndepColsOld [Semiring R] (A : Matrix X Y R) (I : Set α) : Prop :=
  ∃ hI : I ⊆ Y, LinearIndependent R (fun i : I => (A · (hI.elem i)))

private lemma Matrix.indepCols_eq_indepColsOld [Semiring R] (A : Matrix X Y R) :
    A.IndepCols = A.IndepColsOld := by
  ext I
  constructor <;> intro ⟨hI, hAI⟩ <;> use hI <;> let e : I ≃ Y ↓∩ I :=
      (Equiv.ofInjective hI.elem hI.elem_injective).trans hI.elem_range.≃
  · exact (linearIndependent_equiv' e (by aesop)).← hAI
  · exact (linearIndependent_equiv' e (by aesop)).→ hAI

lemma Matrix.indepCols_iff_elem [Semiring R] (A : Matrix X Y R) (I : Set α) :
    A.IndepCols I ↔ ∃ hI : I ⊆ Y, LinearIndepOn R Aᵀ hI.elem.range := by
  unfold Matrix.IndepCols HasSubset.Subset.elem
  aesop

lemma Matrix.indepCols_iff_submatrix [Semiring R] (A : Matrix X Y R) (I : Set α) :
    A.IndepCols I ↔ ∃ hI : I ⊆ Y, LinearIndependent R (A.submatrix id hI.elem)ᵀ :=
  A.indepCols_eq_indepColsOld ▸ Iff.rfl

lemma Matrix.indepCols_iff_submatrix' [Semiring R] (A : Matrix X Y R) (I : Set α) :
    A.IndepCols I ↔ ∃ hI : I ⊆ Y, LinearIndependent R (Aᵀ.submatrix hI.elem id) :=
  A.indepCols_eq_indepColsOld ▸ Iff.rfl


/-- Empty set is independent (old version). -/
private theorem Matrix.indepColsOld_empty [Semiring R] (A : Matrix X Y R) :
    A.IndepColsOld ∅ :=
  ⟨Y.empty_subset, linearIndependent_empty_type⟩

/-- Empty set is independent. -/
theorem Matrix.indepCols_empty [Semiring R] (A : Matrix X Y R) :
    A.IndepCols ∅ :=
  A.indepCols_eq_indepColsOld ▸ A.indepColsOld_empty

/-- A subset of a independent set of columns is independent (old version). -/
private theorem Matrix.indepColsOld_subset [Semiring R] (A : Matrix X Y R) (I J : Set α)
    (hAJ : A.IndepColsOld J) (hIJ : I ⊆ J) :
    A.IndepColsOld I :=
  have ⟨hJ, hA⟩ := hAJ
  ⟨hIJ.trans hJ, hA.comp hIJ.elem hIJ.elem_injective⟩

/-- A subset of an independent set of columns is independent. -/
theorem Matrix.indepCols_subset [Semiring R] (A : Matrix X Y R) (I J : Set α) (hAJ : A.IndepCols J) (hIJ : I ⊆ J) :
    A.IndepCols I :=
  A.indepCols_eq_indepColsOld ▸ A.indepColsOld_subset I J (A.indepCols_eq_indepColsOld ▸ hAJ) hIJ

/-- A non-maximal independent set of columns can be augmented with another independent column. To see why `DivisionRing` is
    necessary, consider `(!![0, 1, 2, 3; 1, 0, 3, 2] : Matrix (Fin 2) (Fin 4) (ZMod 6))` as a counterexample.
    The set `{0}` is nonmaximal independent.
    The set `{2, 3}` is maximal independent.
    However, neither of the sets `{0, 2}` or `{0, 3}` is independent. -/
theorem Matrix.indepCols_aug [DivisionRing R] (A : Matrix X Y R) (I J : Set α)
    (hAI : A.IndepCols I) (hAI' : ¬Maximal A.IndepCols I) (hAJ : Maximal A.IndepCols J) :
    ∃ x ∈ J \ I, A.IndepCols (x ᕃ I) := by
  by_contra! non_aug
  rw [Maximal] at hAI'
  push_neg at hAI'
  obtain ⟨hI, I_indep⟩ := hAI
  obtain ⟨⟨hJ, J_indep⟩, hJ'⟩ := hAJ
  obtain ⟨K, hAK, IK, nKI⟩ := hAI' ⟨hI, I_indep⟩
  let I' : Set Y := { x : Y.Elem | x.val ∈ I }
  let J' : Set Y := { x : Y.Elem | x.val ∈ J }
  let Iᵥ : Set (X → R) := Aᵀ '' I'
  let Jᵥ : Set (X → R) := Aᵀ '' J'
  let Iₛ : Submodule R (X → R) := Submodule.span R Iᵥ
  let Jₛ : Submodule R (X → R) := Submodule.span R Jᵥ
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
        exact hvI _ hI' (hI hI') hxv
      have x_in_JwoI : ↑x ∈ J \ I := Set.mem_diff_of_mem x_in_J x_ni_I
      have hAxI : ¬A.IndepCols (↑x ᕃ I) := non_aug ↑x x_in_JwoI
      rw [Matrix.IndepCols] at hAxI
      push_neg at hAxI
      have hnMxI : ¬LinearIndepOn R Aᵀ (Y ↓∩ (↑x ᕃ I)) := hAxI (Set.insert_subset (hJ hxJ) hI)
      have hYxI : Y ↓∩ (↑x ᕃ I) = x ᕃ I'
      · aesop
      rw [hYxI] at hnMxI
      have I'_indep : LinearIndepOn R Aᵀ I' := I_indep
      by_contra! v_ni_Iₛ
      have : v ∉ Submodule.span R Iᵥ := v_ni_Iₛ
      have hx_ni_I : x ∉ I' := x_ni_I
      have Mx_ni_span_I : Aᵀ x ∉ Submodule.span R (Aᵀ '' I')
      · simp [*, I', J', Iₛ, Iᵥ, Jᵥ]
      have xI_indep : LinearIndepOn R Aᵀ (x ᕃ I') := (linearIndepOn_insert hx_ni_I).← ⟨I'_indep, Mx_ni_span_I⟩
      exact hnMxI xI_indep
  have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  · intro v ⟨x, hxI, hxv⟩
    by_contra! v_ni_Jₛ
    have Mx_ni_span_J' : Aᵀ x ∉ Submodule.span R (Aᵀ '' J') := congr_arg (· ∈ Submodule.span R Jᵥ) hxv ▸ v_ni_Jₛ
    have x_ni_J' : x ∉ J'
    · by_contra! hx_in_J'
      have Mx_in_MJ' : Aᵀ x ∈ (Aᵀ '' J') := Set.mem_image_of_mem Aᵀ hx_in_J'
      have v_in_MJ' : v ∈ (Aᵀ '' J') := Set.mem_of_eq_of_mem hxv.symm Mx_in_MJ'
      exact v_ni_Jₛ (Submodule.mem_span.← (fun p a => a v_in_MJ'))
    have J'_indep : LinearIndepOn R Aᵀ J' := J_indep
    have xJ'_indep : LinearIndepOn R Aᵀ (x ᕃ J') := (linearIndepOn_insert x_ni_J').← ⟨J'_indep, Mx_ni_span_J'⟩
    have M_indep_xJ : A.IndepCols (↑x ᕃ J)
    · rw [Matrix.IndepCols]
      constructor
      · exact Set.insert_subset (hI hxI) hJ
      · have hxJ' : Y ↓∩ (↑x ᕃ J) = x ᕃ J'
        · aesop
        rw [hxJ']
        exact xJ'_indep
    have xJ_ss_J : ↑x ᕃ J ⊆ J := by simp_all
    exact x_ni_J' (xJ_ss_J (J.mem_insert ↑x))
  have Iₛ_eq_Jₛ : Iₛ = Jₛ := Submodule.span_eq_span Iᵥ_ss_Jₛ Jᵥ_ss_Iₛ
  obtain ⟨k, k_in_K, k_ni_I⟩ := Set.not_subset.→ nKI
  have kI_ss_K : (k ᕃ I) ⊆ K := Set.insert_subset k_in_K IK
  have M_indep_kI : A.IndepCols (k ᕃ I) := A.indepCols_subset (k ᕃ I) K hAK kI_ss_K
  have kI_ss_Y : k ᕃ I ⊆ Y := M_indep_kI.left
  have k_in_Y : k ∈ Y := kI_ss_Y (I.mem_insert k)
  let k' : Y.Elem := ⟨k, k_in_Y⟩
  by_cases hkJ' : k' ∈ J'
  · have k_in_JwoI : k ∈ J \ I := Set.mem_diff_of_mem hkJ' k_ni_I
    exact non_aug k k_in_JwoI M_indep_kI
  . have hkI' : Y ↓∩ (k ᕃ I) = ↑k' ᕃ I'
    · aesop
    have k'_ni_I' : k' ∉ I' := k_ni_I
    rw [Matrix.IndepCols, hkI'] at M_indep_kI
    obtain ⟨_, M_indep_kI⟩ := M_indep_kI
    have Mk'_ni_span_I' : Aᵀ k' ∉ Submodule.span R (Aᵀ '' I') := ((linearIndepOn_insert k'_ni_I').→ M_indep_kI).right
    have Mk'_ni_span_J' : Aᵀ k' ∉ Submodule.span R (Aᵀ '' J')
    · have span_I'_eq_span_J' : Submodule.span R (Aᵀ '' I') = Submodule.span R (Aᵀ '' J') := Iₛ_eq_Jₛ
      rw [←span_I'_eq_span_J']
      exact Mk'_ni_span_I'
    have J'_indep : LinearIndepOn R Aᵀ J' := J_indep
    have kJ'_indep : LinearIndepOn R Aᵀ (k' ᕃ J') := (linearIndepOn_insert hkJ').← ⟨J'_indep, Mk'_ni_span_J'⟩
    have hAkJ : A.IndepCols (k ᕃ J)
    · rw [Matrix.IndepCols]
      constructor
      · exact Set.insert_subset k_in_Y hJ
      · have hkJ : Y ↓∩ (k ᕃ J) = k' ᕃ J'
        · aesop
        rw [hkJ]
        exact kJ'_indep
    have kJ_ss_J : k ᕃ J ⊆ J := by simp_all
    exact hkJ' (kJ_ss_J (J.mem_insert k))

lemma linearIndepOn_sUnion_of_directedOn [Semiring R] {A : Matrix Y X R} {s : Set (Set α)}
    (hs : DirectedOn (· ⊆ ·) s)
    (hA : ∀ a ∈ s, LinearIndepOn R A (Y ↓∩ a)) :
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

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem Matrix.indepCols_maximal [Semiring R] (A : Matrix X Y R) (I : Set α) :
    Matroid.ExistsMaximalSubsetProperty A.IndepCols I :=
  fun J hAJ hJI =>
    zorn_subset_nonempty
      { K : Set α | A.IndepCols K ∧ K ⊆ I }
      (fun c hcS chain_c _ =>
        ⟨⋃₀ c,
        ⟨⟨Set.sUnion_subset ↓(hcS ·|>.left.left),
          linearIndepOn_sUnion_of_directedOn chain_c.directedOn ↓(hcS ·|>.left.right)⟩,
          Set.sUnion_subset ↓(hcS ·|>.right)⟩,
        ↓Set.subset_sUnion_of_mem⟩)
      J ⟨hAJ, hJI⟩

/-- `Matrix` (interpreted as a full representation) converted to `IndepMatroid`. -/
def Matrix.toIndepMatroid [DivisionRing R] (A : Matrix X Y R) : IndepMatroid α where
  E := Y
  Indep := A.IndepCols
  indep_empty := A.indepCols_empty
  indep_subset := A.indepCols_subset
  indep_aug := A.indepCols_aug
  indep_maximal S _ := A.indepCols_maximal S
  subset_ground _ := And.left

/-- `Matrix` (interpreted as a full representation) converted to `Matroid`. -/
def Matrix.toMatroid [DivisionRing R] (A : Matrix X Y R) : Matroid α :=
  A.toIndepMatroid.matroid

@[simp]
lemma Matrix.toMatroid_E [DivisionRing R] (A : Matrix X Y R) : A.toMatroid.E = Y :=
  rfl

lemma Matrix.toMatroid_indep [DivisionRing R] (A : Matrix X Y R) : A.toMatroid.Indep = A.IndepCols :=
  rfl

lemma Matrix.toMatroid_indep_iff [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
    A.toMatroid.Indep I ↔ I ⊆ Y ∧ LinearIndepOn R Aᵀ (Y ↓∩ I) := by
  rfl

@[simp]
lemma Matrix.toMatroid_indep_iff_elem [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
    A.toMatroid.Indep I ↔ ∃ hI : I ⊆ Y, LinearIndepOn R Aᵀ hI.elem.range :=
  A.indepCols_iff_elem I

lemma Matrix.toMatroid_indep_iff_submatrix [DivisionRing R] (A : Matrix X Y R) (I : Set α) :
    A.toMatroid.Indep I ↔ ∃ hI : I ⊆ Y, LinearIndependent R (Aᵀ.submatrix hI.elem id) :=
  A.indepCols_iff_submatrix' I

lemma Matrix.fromRows_zero_reindex_toMatroid [DivisionRing R] {G : Set α} [Fintype G]
    [∀ a, Decidable (a ∈ G)] [∀ a, Decidable (a ∈ Y)]
    (A : Matrix G (G ⊕ (Y \ G).Elem) R) (hGY : G ⊆ Y) {Z : Type*} (e : G ⊕ Z ≃ X) :
    (Matrix.of (fun i : G => A i ∘ Subtype.toSum)).toMatroid =
    (Matrix.of ((A ⊟ 0).reindex e hGY.equiv)).toMatroid := by
  apply Matroid.ext_indep
  · simp [Set.union_diff_cancel' (by rfl) hGY]
  intro I hI
  have hIGYG : I ⊆ G ∪ Y \ G := by assumption
  have hIY : I ⊆ Y := Set.union_diff_cancel' (by rfl) hGY ▸ hIGYG
  simp only [Matrix.toMatroid_indep_iff_submatrix, Matrix.reindex_apply]
  constructor
  · intro ⟨_, hAI⟩
    use hIY
    suffices lin_indep : LinearIndependent R ((Aᵀ ◫ 0).submatrix (hGY.equiv.symm ∘ hIY.elem) e.symm)
    · convert lin_indep
      ext i j
      simp
      cases e.symm j <;> simp
    have hA0I : LinearIndependent R ((Aᵀ.submatrix (Subtype.toSum ∘ hIGYG.elem) id) ◫ (0 : Matrix I Z R)) :=
      ((Aᵀ.submatrix (Subtype.toSum ∘ hIGYG.elem) id).linearIndependent_iff_fromCols_zero Z).→ hAI
    let f : (X → R) →ₗ[R] (G ⊕ Z → R) := ⟨⟨(· <| e ·), ↓↓rfl⟩, ↓↓rfl⟩
    apply LinearIndependent.of_comp f
    convert hA0I
    ext i j
    if hi : i.val ∈ G then
      cases j <;> simp [hi, f, HasSubset.Subset.equiv]
    else
      have hiY : i.val ∈ Y \ G := Set.mem_diff_of_mem (hIY i.property) hi
      cases j <;> simp [hi, hiY, f, HasSubset.Subset.equiv]
  · intro ⟨_, hAI⟩
    use hIGYG
    rw [Matrix.linearIndependent_iff_fromCols_zero _ Z]
    let f : (G ⊕ Z → R) →ₗ[R] (X → R) := ⟨⟨(· <| e.symm ·), ↓↓rfl⟩, ↓↓rfl⟩
    apply LinearIndependent.of_comp f
    convert hAI
    ext i j
    if hi : i.val ∈ G then
      cases hj : e.symm j <;> simp [hi, hj, f, HasSubset.Subset.equiv]
    else
      have hiY : i.val ∈ Y \ G := Set.mem_diff_of_mem (hIY i.property) hi
      cases hj : e.symm j <;> simp [hi, hiY, hj, f, HasSubset.Subset.equiv]

/-- Every vector matroid is finitary. -/
lemma Matrix.toMatroid_isFinitary [DivisionRing R] (A : Matrix X Y R) : A.toMatroid.Finitary := by
  constructor
  intro I hI
  simp
  wlog hIY : I ⊆ A.toMatroid.E
  · exfalso
    rw [Set.not_subset_iff_exists_mem_not_mem] at hIY
    obtain ⟨x, hx, hxE⟩ := hIY
    exact hxE ((hI _ (Set.singleton_subset_iff.← hx) (Set.finite_singleton x)).subset_ground rfl)
  use hIY
  rw [linearIndepOn_iff]
  intro s hs hAs
  rw [Finsupp.mem_supported] at hs
  specialize hI s.support.toSet (by rw [Set.image_subset_iff]; convert hs; aesop) (Subtype.val '' s.support).toFinite
  simp [Matrix.toMatroid_indep_iff_elem] at hI
  rw [linearIndepOn_iff] at hI
  exact hI s (⟨⟨·.val, Set.mem_image_of_mem Subtype.val ·⟩, by simp⟩) hAs
