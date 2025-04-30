import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.TotalUnimodularity
import Seymour.Matroid.Constructors.StandardRepresentation


-- ## Primary definition of regularity (LI & TU over ℚ)

/-- Matroid is regular iff it can be constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M


-- ## Secondary definition of regularity (LI over Z2 while TU over ℚ)

/-- Rational matrix `A` is a TU signing of `U` (matrix of the same size but different type) iff `A` is TU and its entries are
    the same as entries in `U` on respective positions up to signs.
    Do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example! -/
def Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) : Prop :=
  A.IsTotallyUnimodular ∧ ∀ i : X, ∀ j : Y, |A i j| = (U i j).val

/-- Matrix `U` has a TU signing iff there is a rational TU matrix whose entries are the same as those in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} (U : Matrix X Y Z2) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U


-- ## Auxiliary stuff

@[simp]
def Matrix.support {X Y R : Type} [Zero R] [DecidableEq R] (A : Matrix X Y R) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

lemma Matrix.support_transpose {X Y R : Type} [Zero R] [DecidableEq R] (A : Matrix X Y R) :
    A.support.transpose = A.transpose.support :=
  rfl

lemma Matrix.support_submatrix {X X' Y Y' R : Type} [Zero R] [DecidableEq R] (A : Matrix X Y R) (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl

@[simp]
lemma Matrix.support_Z2 {X Y : Type} (A : Matrix X Y Z2) : A.support = A := by
  aesop

lemma Matrix.IsTotallyUnimodular.abs_eq_support_cast {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j| = (A.support i j).val := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, of_apply, ZMod.natCast_val, ←hs]
  cases s <;> rfl

lemma Matrix.IsTotallyUnimodular.abs_cast_eq_support {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j|.cast = A.support i j := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, of_apply, ←hs]
  cases s <;> simp

lemma Matrix.IsTotallyUnimodular.support {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    A.IsTuSigningOf A.support :=
  ⟨hA, abs_eq_support_cast hA⟩

lemma Z2_eq_iff_ZMod_val_eq {a b : Z2} : a = b ↔ a.val = b.val := by
  constructor
  <;> intro hab
  · exact congrArg ZMod.val hab
  · cases a
    cases b
    simp only [ZMod.val, Nat.reduceAdd] at hab
    simp only [hab]

lemma Matrix.isTuSigningOf_iff {X Y : Type} (A : Matrix X Y ℚ) (U : Matrix X Y Z2) :
    A.IsTuSigningOf U ↔ A.IsTotallyUnimodular ∧ A.support = U := by
  constructor
  · intro ⟨hA, hAU⟩
    constructor
    · exact hA
    · ext i j
      specialize hAU i j
      rw [hA.abs_eq_support_cast] at hAU
      exact Z2_eq_iff_ZMod_val_eq.← (Rat.natCast_inj.→ hAU)
  · intro ⟨hA, hAU⟩
    exact hAU ▸ hA.support

variable {α : Type}

/-- Matroids are regular up to map equivalence. -/
@[simp]
lemma Matroid.isRegular_mapEquiv_iff {β : Type} (M : Matroid α) (e : α ≃ β) : (M.mapEquiv e).IsRegular ↔ M.IsRegular := by
  constructor
  <;> intro ⟨X, Y, A, hA, hAM⟩
  on_goal 1 => let f := e.symm
  on_goal 2 => let f := e
  all_goals
    use f '' X
    use f '' Y
    use A.submatrix (f.image X).symm (f.image Y).symm, hA.submatrix _ _
    sorry

variable [DecidableEq α]

private lemma Matrix.IsTotallyUnimodular.intCast_det_eq_suppAux_det [Fintype α] {A : Matrix α α ℤ}
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
  rw [hA.det_eq_map_ratFloor_det, Rat.cast_intCast, hA.map_ratFloor.intCast_det_eq_suppAux_det]
  congr
  ext i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.support, of_apply, of_apply, map_apply, ←hs]
  cases s <;> rfl

private lemma Matrix.IsTotallyUnimodular.det_eq_zero_iff_support [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det = (0 : ℚ) ↔ A.support.det = (0 : Z2) := by
  rw [←hA.ratCast_det_eq_support_det]
  apply zero_iff_ratCast_zero_of_in_signTypeCastRange
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hA
  exact hA α id id

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
    let e : Y' ↪ C := ⟨fun i => ⟨(A · i), by use i⟩, fun ⟨_, w₁, ⟨y₁, hy₁⟩, _⟩ ⟨_, w₂, ⟨y₂, hy₂⟩, _⟩ hzz => by
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

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_of_support {X Y : Set α} {A : Matrix X Y ℚ} {U : Matrix X Y Z2}
    (hA : A.IsTotallyUnimodular) (hAU : A.support = U) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y U).toMatroid :=
  hAU ▸ hA.toMatroid_eq_support_toMatroid

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

open scoped Matrix in
private lemma support_eq_support_of_same_matroid_same_X' {F₁ F₂ : Type} [Field F₁] [Field F₂] [DecidableEq F₁] [DecidableEq F₂]
    {X Y : Set α} {hXY : X ⫗ Y} {B₁ : Matrix X Y F₁} {B₂ : Matrix X Y F₂}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
    (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
    B₁.support = B₂.support := by
  -- TODO generalize `B_eq_B_of_same_matroid_same_X`
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
  · sorry
  · sorry

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
  exact support_eq_support_of_same_matroid_same_X' hSS'

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
    have := hB'.support
    cc
  · intro ⟨B, hB, hBS⟩
    apply S.toVectorMatroid.toMatroid_isRegular_if_hasTuSigning
    use (B.prependId · ∘ Subtype.toSum), (hB.one_fromCols).comp_cols Subtype.toSum
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
