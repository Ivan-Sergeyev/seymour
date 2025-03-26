import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.TotalUnimodularity
import Seymour.Matroid.Constructors.StandardRepresentation


-- ## Primary definition (LI over ℚ while TU over ℚ)

/-- The main definition of regularity: `M` is regular iff it is constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

-- ## Secondary definition (LI over Z2 while TU over ℚ)

/-- Matrix `A` is a TU signing of `U` iff `A` is TU and its entries are the same as in `U` up to signs.
    Do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example! -/
def Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  A.IsTotallyUnimodular ∧ ∀ i j, |A i j| = (U i j).val

/-- Matrix `U` has a TU signing if there is a TU matrix whose entries are the same as in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U

/-- Vector matroid given by standard representation that can be represented by a matrix over `Z2` with a TU signing. -/
abbrev StandardRepr.HasTuSigning {α : Type} [DecidableEq α] (S : StandardRepr α Z2) : Prop :=
  S.B.HasTuSigning

-- ## Auxiliary stuff

private def Matrix.discretize {X Y : Type} (A : Matrix X Y ℚ) (n : ℕ := 2) : Matrix X Y (ZMod n) :=
  Matrix.of (if A · · = 0 then 0 else 1)

@[app_unexpander Matrix.discretize]
private def Matrix.discretize_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `discretize))
  | _ => throw ()

private lemma Matrix.discretize_transpose {X Y : Type} (A : Matrix X Y ℚ) :
    A.discretize.transpose = A.transpose.discretize :=
  rfl

private lemma Matrix.discretize_submatrix {X X' Y Y' : Type} (A : Matrix X Y ℚ) (f : X' → X) (g : Y' → Y) :
    A.discretize.submatrix f g = (A.submatrix f g).discretize :=
  rfl

private lemma Matrix.IsTotallyUnimodular.discretize {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular)
    {n : ℕ} (hn : 1 < n) :
    A.IsTuSigningOf (A.discretize n) := by
  refine ⟨hA, fun i j => ?_⟩
  if hAij : A i j = 0 then
    simp [Matrix.discretize, hAij]
  else
    obtain ⟨s, hs⟩ := hA.apply i j
    cases s with
    | zero =>
      simp_all [Matrix.discretize]
    | pos =>
      rw [SignType.pos_eq_one, SignType.coe_one] at hs
      rw [←hs]
      simp [Matrix.discretize, hAij]
      rewrite [ZMod.val_one'' (· ▸ hn |>.false)]
      rfl
    | neg =>
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      rw [←hs]
      simp [Matrix.discretize, hAij]
      rewrite [ZMod.val_one'' (· ▸ hn |>.false)]
      rfl

private def Matrix.auxZ2 {X Y : Type} (A : Matrix X Y ℤ) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)

@[app_unexpander Matrix.auxZ2]
private def Matrix.auxZ2_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `auxZ2))
  | _ => throw ()

variable {α : Type} [DecidableEq α]

private lemma Matrix.IsTotallyUnimodular.intCast_det_eq_auxZ2_det [Fintype α] {A : Matrix α α ℤ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.auxZ2.det := by
  rw [Matrix.det_int_coe]
  congr
  ext i j
  simp [Matrix.auxZ2]
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

private lemma Matrix.IsTotallyUnimodular.ratCast_det_eq_discretize_det [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det.cast = A.discretize.det := by
  rw [hA.det_eq_map_ratFloor_det, Rat.cast_intCast, hA.map_ratFloor.intCast_det_eq_auxZ2_det]
  congr
  ext i j
  simp only [Matrix.discretize, Matrix.auxZ2]
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

private lemma Matrix.IsTotallyUnimodular.det_eq_zero_iff_discretize [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det = (0 : ℚ) ↔ A.discretize.det = (0 : Z2) := by
  rw [←hA.ratCast_det_eq_discretize_det]
  apply zero_iff_ratCast_zero_of_in_signTypeCastRange
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hA
  exact hA α id id

private lemma Matrix.IsTotallyUnimodular.det_ne_zero_iff_discretize [Fintype α] {A : Matrix α α ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det ≠ (0 : ℚ) ↔ A.discretize.det ≠ (0 : Z2) :=
  hA.det_eq_zero_iff_discretize.ne

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_discretize_linearIndependent_aux {Y : Set α} [Fintype Y]
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I Y ℚ} (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.discretize := by
  constructor <;>
      intro hAI <;> rw [Matrix.linearIndependent_iff_exists_submatrix_det] at hAI ⊢ <;> obtain ⟨g, hAg⟩ := hAI <;> use g
  · exact A.discretize_submatrix id g ▸ ((hA.submatrix id g).det_ne_zero_iff_discretize.→ hAg)
  · exact (hA.submatrix id g).det_ne_zero_iff_discretize.← (A.discretize_submatrix id g ▸ hAg)

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
      intro x _
      use (fun j => ⟨x j, by aesop⟩)
      exact ite_some_none_eq_some.→ rfl
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
    have := hi.choose_spec
    gcongr

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

private lemma Matrix.IsTotallyUnimodular.linearIndependent_iff_discretize_linearIndependent {Y : Set α}
    {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I Y ℚ} (hA : A.IsTotallyUnimodular) :
    LinearIndependent ℚ A ↔ LinearIndependent Z2 A.discretize := by
  constructor
  · intro lin_indep
    obtain ⟨Y', hY', hAY'⟩ := A.exists_finite_allColsIn {-1, 0, 1} (by have ⟨s, hs⟩ := hA.apply · · ; cases s <;> aesop)
    rw [A.linearIndependent_iff_allColsSubmatrix_linearIndependent hAY'] at lin_indep
    have := Set.Finite.fintype hY'
    rw [(hA.submatrix id (fun y : Y' => y.val)).linearIndependent_iff_discretize_linearIndependent_aux] at lin_indep
    exact A.discretize.linearIndependent_if_LinearIndependent_subset_cols lin_indep
  · intro lin_indep
    obtain ⟨Y', hY', hAY'⟩ := A.discretize.exists_finite_allColsIn Finset.univ (Finset.mem_univ <| A.discretize 2 · ·)
    rw [A.discretize.linearIndependent_iff_allColsSubmatrix_linearIndependent hAY'] at lin_indep
    rw [Matrix.discretize_submatrix] at lin_indep
    have := Set.Finite.fintype hY'
    rw [←(hA.submatrix id (fun y : Y' => y.val)).linearIndependent_iff_discretize_linearIndependent_aux] at lin_indep
    exact A.linearIndependent_if_LinearIndependent_subset_cols lin_indep

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_discretize_toMatroid {X Y : Set α} {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y A.discretize).toMatroid := by
  ext I hI
  · simp
  simp only [VectorMatroid.toMatroid_indep, VectorMatroid.indepCols_iff_submatrix']
  rw [Matrix.discretize_transpose]
  constructor <;> intro ⟨hIY, hAI⟩ <;> use hIY <;>
      rw [linearIndependent_iff_finset_linearIndependent] at hAI ⊢ <;> intro s <;> specialize hAI s <;>
      have result :=
        (hA.transpose.submatrix (hIY.elem ∘ @Subtype.val I (· ∈ s)) id).linearIndependent_iff_discretize_linearIndependent
  · exact result.→ hAI
  · exact result.← hAI

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_of_discretize {X Y : Set α} {A : Matrix X Y ℚ} {U : Matrix X Y Z2}
    (hA : A.IsTotallyUnimodular) (hAU : A.discretize = U) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y U).toMatroid :=
  hAU ▸ hA.toMatroid_eq_discretize_toMatroid

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary {M : Matroid α} (hM : M.IsRegular) :
    ∃ V : VectorMatroid α Z2, V.toMatroid = M := by
  obtain ⟨X, Y, A, hA, rfl⟩ := hM
  exact ⟨⟨X, Y, A.discretize⟩, hA.toMatroid_eq_discretize_toMatroid.symm⟩

/-- Every regular matroid has a standard binary representation. -/
lemma Matroid.IsRegular.isBinaryStandardRepr {M : Matroid α} (hM : M.IsRegular) :
    ∃ S : StandardRepr α Z2, S.toMatroid = M := by
  obtain ⟨V, hV⟩ := hM.isBinary
  obtain ⟨S, hS⟩ := V.exists_standardRepr
  rw [←hS] at hV
  exact ⟨S, hV⟩

private lemma hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid {V W : VectorMatroid α Z2} [Finite V.X]
    (hVW : V.toMatroid = W.toMatroid) :
    V.A.HasTuSigning ↔ W.A.HasTuSigning := by
  obtain ⟨S, rfl⟩ := V.exists_standardRepr
  have : Fintype S.X := Set.Finite.fintype (by assumption)
  have hS := S.toMatroid_isBase_X
  rw [show S.toMatroid = W.toMatroid from hVW] at hS
  obtain ⟨S', hS', rfl⟩ := W.exists_standardRepr_isBase hS
  rw [ext_standardRepr_of_same_matroid_same_X hVW hS'.symm]

/-- Binary matroid constructed from a full representation is regular iff the binary matrix has a TU signing. -/
private lemma VectorMatroid.toMatroid_isRegular_iff_hasTuSigning (V : VectorMatroid α Z2) [Finite V.X] :
    V.toMatroid.IsRegular ↔ V.A.HasTuSigning := by
  constructor
  · intro ⟨X, Y, A, hA, hAV⟩
    have hV : V.toMatroid = (VectorMatroid.mk X Y A.discretize).toMatroid
    · rw [←hAV, hA.toMatroid_eq_discretize_toMatroid]
    rw [hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid hV]
    use A, hA
    intro i j
    simp [Matrix.discretize]
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
    apply hS.toMatroid_eq_of_discretize
    ext i j
    specialize hSV i j
    simp [Matrix.discretize]
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
