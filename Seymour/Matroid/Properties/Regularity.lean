import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.TotalUnimodularity
import Seymour.Matroid.Constructors.StandardRepresentation


-- ## Primary definition of regularity (LI & TU over ℚ)

/-- Matroid is regular iff it can be constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M


-- ## Secondary definition of regularity (LI over Z2 while TU over ℚ)

/-- `LinearOrderedRing`-valued matrix `A` is a signing of `U` (matrix of the same size but different type) iff `A` has
    the same as entries in `U` on respective positions up to signs. -/
def Matrix.IsSigningOf {X Y R : Type} [LinearOrderedRing R] (A : Matrix X Y R) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  ∀ i : X, ∀ j : Y, |A i j| = (U i j).val

/-- Rational matrix `A` is a TU signing of `U` (matrix of the same size but different type) iff `A` is TU and its entries are
    the same as entries in `U` on respective positions up to signs.
    Do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example! -/
def Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) : Prop :=
  A.IsTotallyUnimodular ∧ A.IsSigningOf U

/-- Matrix `U` has a TU signing iff there is a rational TU matrix whose entries are the same as those in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} (U : Matrix X Y Z2) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U


-- ## Auxiliary stuff

lemma Matrix.IsTotallyUnimodular.abs_eq_support_val {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j| = (A.support i j).val := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ZMod.natCast_val, ←hs]
  cases s <;> rfl

lemma Matrix.IsTotallyUnimodular.abs_cast_eq_support {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j|.cast = A.support i j := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ←hs]
  cases s <;> simp

lemma Matrix.IsTotallyUnimodular.isTuSigningOf_support {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    A.IsTuSigningOf A.support :=
  ⟨hA, hA.abs_eq_support_val⟩

lemma Matrix.isTuSigningOf_iff {X Y : Type} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) :
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

variable {α : Type}

lemma VectorMatroid_mapEquiv_eq {α β : Type} (X Y : Set α) (A : Matrix X Y ℚ) (e : α ≃ β) : (VectorMatroid.mk (e '' X) (e '' Y) (A.submatrix ⇑(e.image X).symm ⇑(e.image Y).symm)).toMatroid = (VectorMatroid.mk X Y A).toMatroid.mapEquiv e := by
  let Ma := VectorMatroid.mk X Y A
  let Mb := VectorMatroid.mk (e '' X) (e '' Y) (A.submatrix ⇑(e.image X).symm ⇑(e.image Y).symm)
  apply Matroid.ext_indep <| Ma.toMatroid.mapEquiv_ground_eq e
  intro I hI
  rw [Ma.toMatroid.mapEquiv_indep_iff, Mb.toMatroid_indep, Ma.toMatroid_indep,
    VectorMatroid.IndepCols, VectorMatroid.IndepCols]
  simp_rw [Equiv.symm_image_subset]
  have MaY : Ma.Y = Y := rfl
  have MbY : Mb.Y = e '' Y := rfl
  have MaA : Ma.A.transpose = A.transpose := rfl
  have MbA : Mb.A.transpose = (A.submatrix ⇑(e.image X).symm ⇑(e.image Y).symm).transpose := rfl
  rw [MaA, MbA]
  constructor
  all_goals
    intro ⟨hI, hIndep⟩
    refine ⟨hI, ?_⟩
    rw [linearIndepOn_iff] at hIndep ⊢
    intro l hl hll
  · refine Finsupp.embDomain_eq_zero.→ <| hIndep (Finsupp.embDomain (e.image Y) l) ?_ ?_
    · rw [Finsupp.mem_supported] at hl ⊢
      simp_rw [Finsupp.support_embDomain, Finset.coe_map, Set.image_subset_iff, Ma] at hl ⊢
      suffices ⇑(e.image Y).toEmbedding ⁻¹' (Subtype.val ⁻¹' I) = Subtype.val ⁻¹' (e.symm '' I) by rwa [this]
      ext x
      simp
    · rw [Finsupp.linearCombination_embDomain, Matrix.transpose_submatrix]
      sorry
  · refine Finsupp.embDomain_eq_zero.→ <| hIndep (Finsupp.embDomain (e.image Y).symm l) ?_ ?_
    · rw [Finsupp.mem_supported] at hl ⊢
      simp_rw [Finsupp.support_embDomain, Finset.coe_map, Set.image_subset_iff, Ma] at hl ⊢
      suffices ⇑(e.image Y).symm.toEmbedding ⁻¹' (Subtype.val ⁻¹' (⇑e.symm '' I)) = Subtype.val ⁻¹' I by rwa [this]
      ext x
      simp [show ((e.image Y).symm x) = ⟨e.symm x, (Set.mem_image_equiv).→ x.prop⟩ by
        apply_fun (Equiv.Set.image e Y e.injective)
        simp]
    · rw [Finsupp.linearCombination_embDomain]
      rw [Matrix.transpose_submatrix] at hll
      sorry

/-- Matroids are regular up to map equivalence. -/
@[simp]
lemma Matroid.isRegular_mapEquiv_iff {β : Type} (M : Matroid α) (e : α ≃ β) : (M.mapEquiv e).IsRegular ↔ M.IsRegular := by
  constructor <;> intro ⟨X, Y, A, hA, hAM⟩
  on_goal 1 => let f := e.symm
  on_goal 2 => let f := e
  all_goals
    use f '' X
    use f '' Y
    use A.submatrix (f.image X).symm (f.image Y).symm, hA.submatrix _ _
    rw [VectorMatroid_mapEquiv_eq X Y A f]
    aesop

variable [DecidableEq α]

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

private lemma Matrix.IsTotallyUnimodular.det_ne_zero_iff_support [Fintype α] {A : Matrix α α ℚ}
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
    (hAV : ∀ i j, A i j ∈ V) :
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

private lemma Matrix.linearIndependent_if_LinearIndependent_subset_cols {X Y R : Type} [Ring R]
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

private lemma Matrix.linearIndependent_iff_allColsSubmatrix_linearIndependent {X Y R : Type} [Ring R] {Y' : Set Y}
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
    convert_to (∑ i ∈ s, c i • A i j) = (∑ i ∈ s, c i • A.submatrix id (·.val) i  y')
    · apply Finset.sum_apply
    · apply Finset.sum_apply
    congr
    ext i
    rw [congr_fun hy' i]
    simp
  · exact A.linearIndependent_if_LinearIndependent_subset_cols

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_support_linearIndependent_of_finite_of_finite
    {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
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
    {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] {A : Matrix X Y ℚ}
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
    {X Y : Type} [DecidableEq X] [DecidableEq Y] {A : Matrix X Y ℚ}
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
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y A.support).toMatroid := by
  ext I hI
  · simp
  simp_rw [VectorMatroid.toMatroid_indep_iff_submatrix', Matrix.support_transpose, Matrix.support_submatrix]
  constructor <;> intro ⟨hIY, hAI⟩ <;> use hIY
  · rwa [(hA.transpose.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent] at hAI
  · rwa [(hA.transpose.submatrix hIY.elem id).linearIndependent_iff_support_linearIndependent]

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary {M : Matroid α} (hM : M.IsRegular) :
    ∃ V : VectorMatroid α Z2, V.toMatroid = M := by
  obtain ⟨X, Y, A, hA, rfl⟩ := hM
  exact ⟨⟨X, Y, A.support⟩, hA.toMatroid_eq_support_toMatroid.symm⟩

/-- Every regular matroid has a standard binary representation. -/
lemma Matroid.IsRegular.hasBinaryStandardRepr {M : Matroid α} (hM : M.IsRegular) :
    ∃ S : StandardRepr α Z2, S.toMatroid = M := by
  obtain ⟨V, hV⟩ := hM.isBinary
  obtain ⟨S, hSV⟩ := V.exists_standardRepr
  exact ⟨S, hSV ▸ hV⟩

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_of_support {X Y : Set α} {A : Matrix X Y ℚ} {U : Matrix X Y Z2}
    (hA : A.IsTotallyUnimodular) (hAU : A.support = U) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y U).toMatroid :=
  hAU ▸ hA.toMatroid_eq_support_toMatroid

/-- Binary matroid constructed from a full representation is regular if the binary matrix has a TU signing. -/
private lemma VectorMatroid.toMatroid_isRegular_if_hasTuSigning (V : VectorMatroid α Z2) :
    V.A.HasTuSigning → V.toMatroid.IsRegular := by
  intro ⟨S, hS, hSV⟩
  use V.X, V.Y, S, hS
  apply hS.toMatroid_eq_of_support
  ext i j
  specialize hSV i j
  simp
  if h0 : V.A i j = 0 then
    simp_all
  else
    have h1 := Z2_eq_1_of_ne_0 h0
    simp_all
    intro hS0
    rw [hS0, abs_zero, ZMod.cast] at hSV
    simp only [ZMod.val_one_eq_one_mod] at hSV
    norm_num at hSV

-- ## Main result of this file

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
    obtain ⟨S', hXX, hSA, hB'⟩ := (VectorMatroid.mk X' Y' A).exists_standardRepr_isBase_isTotallyUnimodular (hAB ▸ hX) hA
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
    apply S.toVectorMatroid.toMatroid_isRegular_if_hasTuSigning
    use ((1 ◫ B) · ∘ Subtype.toSum), (hB.one_fromCols).comp_cols Subtype.toSum
    intro i j
    cases hj : j.toSum with
    | inl x =>
      simp [hj]
      if hi : i = x then
        rewrite [hi, Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      else
        rewrite [Matrix.one_apply_ne hi, Matrix.one_apply_ne hi]
        rfl
    | inr y =>
      have hjX : j.val ∉ S.X := (by simp [·] at hj)
      have hjY : j.val ∈ S.Y := by have : j.val ∈ S.X ∪ S.Y := j.property; tauto_set
      convert hBS i y <;> simp_all
