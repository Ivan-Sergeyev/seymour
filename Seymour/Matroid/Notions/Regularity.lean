import Seymour.Matroid.Constructors.StandardRepresentation
import Seymour.ForMathlib.MatrixLI


-- ## Main definition of this file

/-- The main definition of regularity: `M` is regular iff it is constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

-- ## Secondary definitions

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

variable {α : Type}

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_discretize {X Y : Set α} {A : Matrix X Y ℚ}
    (hA : A.IsTotallyUnimodular) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y A.discretize).toMatroid := by
  sorry

private lemma Matrix.IsTotallyUnimodular.toMatroid_eq_of_discretize {X Y : Set α} {A : Matrix X Y ℚ} {U : Matrix X Y Z2}
    (hA : A.IsTotallyUnimodular) (hAU : A.discretize = U) :
    (VectorMatroid.mk X Y A).toMatroid = (VectorMatroid.mk X Y U).toMatroid :=
  hAU ▸ hA.toMatroid_eq_discretize

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary {M : Matroid α} [hE : Finite M.E] (hM : M.IsRegular) :
    ∃ V : VectorMatroid α Z2, V.toMatroid = M := by
  obtain ⟨X, Y, A, hA, rfl⟩ := hM
  have : Fintype X := sorry
  exact ⟨⟨X, Y, A.discretize⟩, hA.toMatroid_eq_discretize.symm⟩

/-- Vector matroid given by full representation that can be represented by a matrix over `Z2` with a TU signing. -/
private abbrev VectorMatroid.HasTuSigning (V : VectorMatroid α Z2) : Prop :=
  V.A.HasTuSigning

variable [DecidableEq α]

/-- Every regular matroid has a standard binary representation. -/
lemma Matroid.IsRegular.isBinaryStd {M : Matroid α} [Finite M.E] (hM : M.IsRegular) :
    ∃ S : StandardRepr α Z2, S.toMatroid = M := by
  obtain ⟨V, hV⟩ := hM.isBinary
  obtain ⟨S, hS⟩ := V.exists_standardRepr
  rw [←hS] at hV
  exact ⟨S, hV⟩

private lemma hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid {V W : VectorMatroid α Z2}
    (hVW : V.toMatroid = W.toMatroid) :
    V.HasTuSigning ↔ W.HasTuSigning := by
  obtain ⟨S, rfl⟩ := V.exists_standardRepr
  have based := S.toMatroid_isBase
  rw [show S.toMatroid = W.toMatroid from hVW] at based
  obtain ⟨S', hS', rfl⟩ := W.exists_standardRepr_isBase based
  rw [ext_standardRepr_of_same_matroid_same_X hVW hS'.symm]

/-- Binary matroid constructed from a full representation is regular iff the binary matrix has a TU signing. -/
private lemma VectorMatroid.toMatroid_isRegular_iff_hasTuSigning (V : VectorMatroid α Z2) : -- TODO `S` finite?
    V.toMatroid.IsRegular ↔ V.HasTuSigning := by
  constructor
  · intro ⟨X, Y, A, hA, hAV⟩
    have hV : V.toMatroid = (VectorMatroid.mk X Y A.discretize).toMatroid
    · rw [←hAV, hA.toMatroid_eq_discretize]
    rw [hasTuSigning_iff_hasTuSigning_of_toMatroid_eq_toMatroid hV]
    use A, hA
    intro i j
    simp [Matrix.discretize]
    if h0 : A i j = 0 then
      simp [h0]
    else if h1 : A i j = 1 then
      rewrite [h1]
      rfl
    else if h1 : A i j = -1 then
      rewrite [h1]
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
      simp only at hSV
      sorry

-- ## Main result of this file

/-- Binary matroid constructed from a standard representation is regular iff the binary matrix has a TU signing. -/
lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning (S : StandardRepr α Z2) :
    S.toMatroid.IsRegular ↔ S.HasTuSigning := by
  refine
    S.toVectorMatroid.toMatroid_isRegular_iff_hasTuSigning.trans ⟨
      fun ⟨A, hA, hAS⟩ => ⟨A.submatrix id (Sum.toUnion ∘ Sum.inr), hA.submatrix id (Sum.toUnion ∘ Sum.inr), fun i j => ?_⟩,
      fun ⟨B, hB, hBS⟩ => ⟨(B.prependId · ∘ Subtype.toSum), (hB.one_fromCols).comp_cols Subtype.toSum, fun i j => ?_⟩⟩
  · convert hAS i (Sum.inr j).toUnion
    have hjY : ((Sum.inr j).toUnion : (S.X ∪ S.Y).Elem).val ∈ S.Y := by simp [Sum.toUnion]
    have hjX : ((Sum.inr j).toUnion : (S.X ∪ S.Y).Elem).val ∉ S.X := by simp [Sum.toUnion]; have := S.hXY; tauto_set
    simp [Subtype.toSum, hjX, hjY]
    rfl
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
      have hjX : j.val ∉ S.X := (by simp [·, Subtype.toSum] at hj)
      have hjY : j.val ∈ S.Y := by have : j.val ∈ S.X ∪ S.Y := j.property; tauto_set
      convert hBS i y <;> simp_all [Subtype.toSum]
