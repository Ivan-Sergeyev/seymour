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
def Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  A.IsTotallyUnimodular ∧ ∀ i j, |A i j| = (U i j).val

/-- Matrix `U` has a TU signing iff there is a rational TU matrix whose entries are the same as those in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U

/-- Vector matroid given by standard representation that can be represented by a matrix over `Z2` with a TU signing. -/
abbrev StandardRepr.HasTuSigning {α : Type} [DecidableEq α] (S : StandardRepr α Z2) : Prop :=
  S.B.HasTuSigning

-- ## Auxiliary stuff

def Matrix.support {X Y : Type} (A : Matrix X Y ℚ) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

lemma Matrix.support_transpose {X Y : Type} (A : Matrix X Y ℚ) :
    A.support.transpose = A.transpose.support :=
  rfl

lemma Matrix.support_submatrix {X X' Y Y' : Type} (A : Matrix X Y ℚ) (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl

private lemma Matrix.IsTotallyUnimodular.support {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    A.IsTuSigningOf A.support := by
  refine ⟨hA, fun i j => ?_⟩
  if hAij : A i j = 0 then
    simp [Matrix.support, hAij]
  else
    obtain ⟨s, hs⟩ := hA.apply i j
    cases s with
    | zero =>
      simp_all [Matrix.support]
    | pos =>
      rw [SignType.pos_eq_one, SignType.coe_one] at hs
      rw [←hs]
      simp [Matrix.support, hAij]
      rfl
    | neg =>
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      rw [←hs]
      simp [Matrix.support, hAij]
      rfl

private def Matrix.suppAux {X Y : Type} (A : Matrix X Y ℤ) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

@[app_unexpander Matrix.suppAux]
private def Matrix.suppAux_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `suppAux))
  | _ => throw ()

variable {α : Type}

/-- Matroids are regular up to map equivalence -/
@[simp]
lemma Matroid.isRegular_mapEquiv_iff {β : Type} (M : Matroid α) (f : α ≃ β) : (M.mapEquiv f).IsRegular ↔ M.IsRegular := by
  constructor <;> intro ⟨X, Y, A, hA, hAM⟩
  on_goal 1 => let f' := f.symm
  on_goal 2 => let f' := f
  all_goals
    use f' '' X
    use f' '' Y
    use A.submatrix (f'.image X).symm (f'.image Y).symm
    refine ⟨Matrix.IsTotallyUnimodular.submatrix _ _ hA, ?_⟩
    sorry

variable [DecidableEq α]

private lemma Matrix.IsTotallyUnimodular.intCast_det_eq_suppAux_det [Fintype α] {A : Matrix α α ℤ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.suppAux.det := by
  rw [Matrix.det_int_coe]
  congr
  ext i j
  simp [Matrix.suppAux]
  if h0 : A i j = 0 then
    rewrite [h0]
    rfl
  else if h1 : A i j = 1 then
    rewrite [h1]
    rfl
  else if h9 : A i j = -1 then
    rewrite [h9]
    rfl
  else
    exfalso
    obtain ⟨s, hs⟩ := hA.apply i j
    cases s <;> simp_all

private lemma Matrix.IsTotallyUnimodular.ratCast_det_eq_support_det [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.support.det := by
  rw [hA.det_eq_map_ratFloor_det, Rat.cast_intCast, hA.map_ratFloor.intCast_det_eq_suppAux_det]
  congr
  ext i j
  simp only [Matrix.support, Matrix.suppAux]
  if h0 : A i j = 0 then
    simp [h0]
    rfl
  else if h1 : A i j = 1 then
    simp [h1]
    exact Int.one_ne_zero
  else if h9 : A i j = -1 then
    simp [h9]
    exact Int.neg_one_ne_zero
  else
    exfalso
    obtain ⟨s, hs⟩ := hA.apply i j
    cases s <;> simp_all

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
      have hack_y₁ := Classical.choose_spec (⟨y₁, rfl⟩ : ∃ y : Y, (A · y) = (A · y₁))
      have hack_y₂ := Classical.choose_spec (⟨y₂, rfl⟩ : ∃ y : Y, (A · y) = (A · y₂))
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
  obtain ⟨S, hS⟩ := V.exists_standardRepr
  rw [←hS] at hV
  exact ⟨S, hV⟩

private lemma hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid {V W : VectorMatroid α Z2} [Finite V.X]
    (hVW : V.toMatroid = W.toMatroid) :
    V.A.HasTuSigning ↔ W.A.HasTuSigning := by
  sorry

/-- Binary matroid constructed from a full representation is regular iff the binary matrix has a TU signing. -/
private lemma VectorMatroid.toMatroid_isRegular_iff_hasTuSigning (V : VectorMatroid α Z2) [Finite V.X] :
    V.toMatroid.IsRegular ↔ V.A.HasTuSigning := by
  constructor
  · intro ⟨X, Y, A, hA, hAV⟩
    have hV : V.toMatroid = (VectorMatroid.mk X Y A.support).toMatroid
    · rw [←hAV, hA.toMatroid_eq_support_toMatroid]
    rw [hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid hV]
    use A, hA
    intro i j
    simp [Matrix.support]
    if h0 : A i j = 0 then
      simp [h0]
    else if h1 : A i j = 1 then
      rewrite [h1]
      rfl
    else if h9 : A i j = -1 then
      rewrite [h9]
      rfl
    else
      exfalso
      obtain ⟨s, hs⟩ := hA.apply i j
      cases s <;> simp_all
  · intro ⟨S, hS, hSV⟩
    use V.X, V.Y, S, hS
    apply hS.toMatroid_eq_of_support
    ext i j
    specialize hSV i j
    simp [Matrix.support]
    if h0 : V.A i j = 0 then
      simp_all
    else
      have h1 := Fin2_eq_1_of_ne_0 h0
      simp_all
      intro hS0
      rw [hS0, abs_zero, ZMod.cast] at hSV
      simp only [ZMod.val_one_eq_one_mod] at hSV
      norm_num at hSV

-- ## Main result of this file

/-- Binary matroid constructed from a standard representation is regular iff the binary matrix has a TU signing. -/
lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning (S : StandardRepr α Z2) [Finite S.X] :
    S.toMatroid.IsRegular ↔ S.HasTuSigning := by
  refine
    S.toVectorMatroid.toMatroid_isRegular_iff_hasTuSigning.trans ⟨
      fun ⟨A, hA, hAS⟩ => ⟨A.submatrix id (Sum.toUnion ∘ Sum.inr), hA.submatrix id (Sum.toUnion ∘ Sum.inr), fun i j => ?_⟩,
      fun ⟨B, hB, hBS⟩ => ⟨(B.prependId · ∘ Subtype.toSum), (hB.one_fromCols).comp_cols Subtype.toSum, fun i j => ?_⟩⟩
  · convert hAS i (◪j).toUnion
    have hjY : ((◪j).toUnion : (S.X ∪ S.Y).Elem).val ∈ S.Y := by simp
    have hjX : ((◪j).toUnion : (S.X ∪ S.Y).Elem).val ∉ S.X := by simp; have := S.hXY; tauto_set
    simp_all
  · cases hj : j.toSum with
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
