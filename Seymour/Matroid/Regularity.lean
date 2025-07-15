import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.Signing
import Seymour.Matrix.TotalUnimodularity
import Seymour.Matroid.StandardRepresentation

/-!
# Regularity

Here we study regular matroids.
-/

/-! ## Definition of regularity (LI & TU over ℚ) -/

/-- Matroid is regular iff it can be constructed from a rational TU matrix. -/
def Matroid.IsRegular {α : Type*} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ A.toMatroid = M


/-! ## Characterization of regularity (LI over Z2 while TU over ℚ) -/

/-- Rational matrix `A` is a TU signing of `U` (matrix of the same size but different type) iff `A` is TU and its entries are
    the same as entries in `U` on respective positions up to signs.
    Do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example! -/
def Matrix.IsTuSigningOf {X Y : Type*} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) : Prop :=
  A.IsTotallyUnimodular ∧ A.IsSigningOf U

/-- Matrix `U` has a TU signing iff there is a rational TU matrix whose entries are the same as those in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type*} (U : Matrix X Y Z2) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U


/-! ## Auxiliary stuff -/

lemma Matrix.IsTotallyUnimodular.isTuSigningOf_support {X Y : Type*} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    A.IsTuSigningOf A.support :=
  ⟨hA, hA.abs_eq_support_val⟩

lemma Matrix.isTuSigningOf_iff {X Y : Type*} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) :
    A.IsTuSigningOf U ↔ A.IsTotallyUnimodular ∧ A.support = U := by
  constructor
  · intro ⟨hA, hAU⟩
    constructor
    · exact hA
    · ext i j
      specialize hAU i j
      rw [hA.abs_eq_support_val] at hAU
      exact Z2_ext (Rat.natCast_inj.→ hAU)
  · intro ⟨hA, hAU⟩
    exact hAU ▸ hA.isTuSigningOf_support

private lemma Matrix.toMatroid_mapEquiv {α β : Type*} {X Y : Set α} (A : Matrix X Y ℚ) (e : α ≃ β) :
    (A.submatrix (e.image X).symm (e.image Y).symm).toMatroid = A.toMatroid.mapEquiv e := by
  let Aₑ := (A.submatrix (e.image X).symm (e.image Y).symm)
  apply Matroid.ext_indep (A.toMatroid.mapEquiv_ground_eq e)
  intro I hI
  rw [A.toMatroid.mapEquiv_indep_iff, Aₑ.toMatroid_indep, A.toMatroid_indep, Matrix.IndepCols, Matrix.IndepCols,
    Equiv.symm_image_subset]
  constructor
  all_goals
    apply And.imp_right
    intro hI
    rw [linearIndepOn_iff] at hI ⊢
    intro l hl hll
  on_goal 1 => refine Finsupp.embDomain_eq_zero.→ (hI (Finsupp.embDomain (e.image Y) l) ?_ ?_)
  on_goal 3 => refine Finsupp.embDomain_eq_zero.→ (hI (Finsupp.embDomain (e.image Y).symm l) ?_ ?_)
  on_goal 2 =>
    rw [Finsupp.linearCombination_embDomain, Matrix.transpose_submatrix]
    show (Finsupp.linearCombination ℚ (A.transpose.submatrix ((e.image Y).symm ∘ e.image Y) (e.image X).symm)) l = 0
    rw [Equiv.symm_comp_self]
    ext x
    rw [funext_iff] at hll
    specialize hll ⟨(e.image X).symm x, (Set.mem_image_equiv).→ x.prop⟩
    rw [Pi.zero_apply] at hll ⊢
    rw [←hll, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum.eq_1, Finsupp.sum.eq_1]
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.submatrix_apply, id_eq,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_id_id, Equiv.image_symm_apply_coe]
    rfl
  on_goal 3 =>
    rw [Finsupp.linearCombination_embDomain]
    rw [Matrix.transpose_submatrix] at hll
    ext x
    rw [funext_iff] at hll
    specialize hll ⟨e.image X x, Subtype.coe_prop ((e.image X) x)⟩
    rw [Pi.zero_apply] at hll ⊢
    rw [←hll, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum.eq_1, Finsupp.sum.eq_1]
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, smul_eq_mul, id_eq,
      Equiv.image_apply_coe,
      show ((e.image X).symm ⟨e x, by simp⟩) = x by
        apply_fun e.image X
        rw [Equiv.apply_symm_apply]
        rfl]
    rfl
  all_goals
    rw [Finsupp.mem_supported] at hl ⊢
    simp_rw [Finsupp.support_embDomain, Finset.coe_map, Set.image_subset_iff] at hl ⊢
    apply subset_of_subset_of_eq hl
    ext x
    simp_rw [Set.mem_preimage, Set.mem_image_equiv, Equiv.symm_symm]
  · rfl
  · rw [show ((e.image Y).symm.toEmbedding x) = ⟨e.symm x, Set.mem_image_equiv.→ x.prop⟩
        by apply_fun (Equiv.Set.image e Y e.injective); simp,
      Equiv.apply_symm_apply]

/-- Regularity of matroids is preserved under remapping. -/
@[simp]
lemma Matroid.isRegular_mapEquiv_iff {α β : Type*} (M : Matroid α) (e : α ≃ β) : (M.mapEquiv e).IsRegular ↔ M.IsRegular := by
  constructor
  <;> intro ⟨X, Y, A, hA, hAM⟩
  · use e.symm '' X, e.symm '' Y, A.submatrix (e.symm.image X).symm (e.symm.image Y).symm, hA.submatrix _ _
    rw [A.toMatroid_mapEquiv e.symm]
    aesop
  · use e '' X, e '' Y, A.submatrix (e.image X).symm (e.image Y).symm, hA.submatrix _ _
    rw [A.toMatroid_mapEquiv e]
    aesop

variable {α : Type*} [DecidableEq α]

private lemma Matrix.IsTotallyUnimodular.intCast_det_eq_support_det [Fintype α] {A : Matrix α α ℤ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.support.det := by
  rw [Matrix.det_int_coe]
  congr
  ext i j
  simp only [Matrix.support, Matrix.map, Matrix.of_apply]
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [←hs, SignType.intCast_cast]
  cases s <;> rfl

private lemma Matrix.IsTotallyUnimodular.ratCast_det_eq_support_det [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.support.det := by
  rw [hA.det_eq_map_ratFloor_det, Rat.cast_intCast, hA.map_ratFloor.intCast_det_eq_support_det]
  congr
  ext i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.support, Matrix.of_apply, Matrix.of_apply, Matrix.map_apply, ←hs]
  cases s <;> rfl

private lemma Matrix.IsTotallyUnimodular.det_eq_zero_iff_support [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det = (0 : ℚ) ↔ A.support.det = (0 : Z2) := by
  rw [←hA.ratCast_det_eq_support_det]
  apply zero_iff_ratCast_zero_of_in_signTypeCastRange
  exact hA.det id id

private def Matrix.AllColsIn {X Y R : Type*} (A : Matrix X Y R) (Y' : Set Y) : Prop :=
  ∀ y : Y, ∃ y' : Y', (A · y) = (A · y')

@[app_unexpander Matrix.AllColsIn]
private def Matrix.AllColsIn_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($(A).$(Lean.mkIdent `AllColsIn))
  | _ => throw ()

private lemma Matrix.exists_finite_allColsIn {X Y R : Type*} [Fintype X] [DecidableEq Y] (A : Matrix X Y R) (V : Finset R)
    (hAV : ∀ i j, A i j ∈ V) :
    ∃ Y' : Set Y, Finite Y' ∧ A.AllColsIn Y' := by
  let C : Set (X → R) := { (A · y) | y : Y }
  let Y' : Set Y := { Classical.choose hc | (c : X → R) (hc : c ∈ C) }
  use Y'
  constructor
  · let S : Set (X → V) := Set.univ
    let S' : Set (X → R) := (· · |>.val) '' S
    have hCS' : C ⊆ S'
    · rintro - ⟨w, rfl⟩
      exact ⟨(⟨_, hAV · w⟩), trivial, rfl⟩
    let e : Y' ↪ C := ⟨fun j : Y' => ⟨(A · j), by use j⟩, fun ⟨_, w₁, ⟨y₁, hy₁⟩, _⟩ ⟨_, w₂, ⟨y₂, hy₂⟩, _⟩ _ => by
      simp_all only [Subtype.mk.injEq, C, Y']
      subst hy₁ hy₂
      have := Classical.choose_spec (⟨y₁, rfl⟩ : ∃ y : Y, (A · y) = (A · y₁))
      have := Classical.choose_spec (⟨y₂, rfl⟩ : ∃ y : Y, (A · y) = (A · y₂))
      simp_all only⟩
    have S_finite : S.Finite := Subtype.finite
    have S'_finite : S'.Finite := S_finite.image (fun i : X => · i |>.val)
    exact (S'_finite.subset hCS').finite_of_encard_le e.encard_le
  · intro j
    have hj : (A · j) ∈ C := by use j
    exact ⟨⟨hj.choose, by aesop⟩, hj.choose_spec.symm⟩

private lemma Matrix.linearIndependent_if_LinearIndependent_subset_cols {X Y R : Type*} [Ring R]
    (A : Matrix X Y R) {Y' : Set Y} (hA : LinearIndependent R (A.submatrix id (fun y' : Y' => y'.val))) :
    LinearIndependent R A := by
  by_contra lin_dep
  absurd hA
  rw [not_linearIndependent_iff] at lin_dep ⊢
  obtain ⟨s, c, hscA, hsc⟩ := lin_dep
  refine ⟨s, c, ?_, hsc⟩
  ext j
  convert congr_fun hscA j
  simp

private lemma Matrix.linearIndependent_iff_allColsSubmatrix_linearIndependent {X Y R : Type*} [Ring R] {Y' : Set Y}
    (A : Matrix X Y R) (hAY' : A.AllColsIn Y') :
    LinearIndependent R A ↔ LinearIndependent R (A.submatrix id (·.val) : Matrix X Y' R) := by
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
    {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.support := by
  constructor
  <;> intro lin_indep
  <;> rw [Matrix.linearIndependent_iff_exists_submatrix_det] at lin_indep ⊢
  <;> obtain ⟨g, hAg⟩ := lin_indep
  <;> use g
  <;> have result := (hA.submatrix id g).det_eq_zero_iff_support.ne
  · exact A.support_submatrix id g ▸ (result.→ hAg)
  · exact result.← (A.support_submatrix id g ▸ hAg)

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_support_linearIndependent_of_finite
    {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
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
    {X Y : Type*} [DecidableEq X] [DecidableEq Y] {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.support := by
  constructor
  <;> intro lin_indep
  <;> rw [linearIndependent_iff_finset_linearIndependent] at lin_indep ⊢
  <;> intro s
  <;> specialize lin_indep s
  <;> have result := (hA.submatrix (@Subtype.val X (· ∈ s)) id).linearIndependent_iff_support_linearIndependent_of_finite
  · exact result.→ lin_indep
  · exact result.← lin_indep

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_support_toMatroid {X Y : Set α} {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.toMatroid = A.support.toMatroid := by
  ext I hI
  · simp
  simp_rw [Matrix.toMatroid_indep_iff_submatrix, Matrix.support_transpose, Matrix.support_submatrix]
  constructor <;> intro ⟨hIY, hAI⟩ <;> use hIY
  · rwa [(hA.transpose.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent] at hAI
  · rwa [(hA.transpose.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent]

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_of_support {X Y : Set α} {A : Matrix X Y ℚ} {U : Matrix X Y Z2}
    (hA : A.IsTotallyUnimodular) (hAU : A.support = U) :
    A.toMatroid = U.toMatroid :=
  hAU ▸ hA.toMatroid_eq_support_toMatroid

/-- Binary matroid constructed from a full representation is regular if the binary matrix has a TU signing. -/
private lemma Matrix.toMatroid_isRegular_if_hasTuSigning {X Y : Set α} (A : Matrix X Y Z2) :
    A.HasTuSigning → A.toMatroid.IsRegular := by
  intro ⟨S, hS, hSV⟩
  use X, Y, S, hS
  apply hS.toMatroid_eq_of_support
  ext i j
  specialize hSV i j
  simp
  if h0 : A i j = 0 then
    simp_all
  else
    have h1 := Z2_eq_1_of_ne_0 h0
    simp_all
    intro hS0
    rw [hS0, abs_zero] at hSV
    exact Rat.zero_ne_one hSV


/-! ## Main results of this file -/

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary {M : Matroid α} (hM : M.IsRegular) :
    ∃ X : Set α, ∃ Y : Set α, ∃ A : Matrix X Y Z2, A.toMatroid = M := by
  obtain ⟨X, Y, A, hA, rfl⟩ := hM
  exact ⟨X, Y, A.support, hA.toMatroid_eq_support_toMatroid.symm⟩

/-- Binary matroid constructed from a standard representation is regular iff the binary matrix has a TU signing. -/
lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning (S : StandardRepr α Z2) [Finite S.X] :
    S.toMatroid.IsRegular ↔ S.B.HasTuSigning := by
  constructor
  · have : Fintype S.X
    · apply Set.Finite.fintype
      assumption
    have hX := S.toMatroid_isBase_X
    obtain ⟨X, Y, hXY, B, _, _⟩ := S
    dsimp only at hX ⊢
    intro ⟨X', Y', A, hA, hAB⟩
    obtain ⟨S', hXX, hSA, hB'⟩ := A.exists_standardRepr_isBase_isTotallyUnimodular (hAB ▸ hX) hA
    have : Fintype S'.X
    · subst hXX
      assumption
    have hBB := support_eq_support_of_same_matroid_same_X (hSA.trans hAB) hXX
    simp only [Matrix.support_Z2] at hBB
    have hYY : S'.Y = Y := right_eq_right_of_union_eq_union hXX S'.hXY hXY (congr_arg Matroid.E (hSA.trans hAB))
    use hXX ▸ hYY ▸ S'.B
    have := hB'.isTuSigningOf_support
    cc
  · intro ⟨B, hB, hBS⟩
    apply S.toFull.toMatroid_isRegular_if_hasTuSigning
    use ((1 ◫ B) · ∘ Subtype.toSum), (hB.one_fromCols).comp_cols Subtype.toSum
    intro i j
    cases hj : j.toSum with
    | inl x =>
      simp [hj]
      if hi : i = x then
        rw [hi, Matrix.one_apply_eq]
        simp [hj, StandardRepr.toFull]
      else
        simp [hj, StandardRepr.toFull, Matrix.one_apply_ne hi]
    | inr y =>
      have hjX : j.val ∉ S.X := (by simp [·] at hj)
      have hjY : j.val ∈ S.Y := by have : j.val ∈ S.X ∪ S.Y := j.property; tauto_set
      convert hBS i y <;> simp_all [StandardRepr.toFull]
