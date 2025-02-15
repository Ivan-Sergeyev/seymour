import Seymour.Matroid.Constructors.StandardRepresentation
import Seymour.ForMathlib.MatrixLI


/-- Matrix `A` is a TU signing of `U` iff `A` is TU and its entries are the same as in `U` up to signs.
    Do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example! -/
def Matrix.IsTuSigningOf {X Y : Type} (A : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  A.IsTotallyUnimodular ∧ ∀ i j, |A i j| = (U i j).val

/-- Matrix `U` has a TU signing if there is a TU matrix whose entries are the same as in `U` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  ∃ A : Matrix X Y ℚ, A.IsTuSigningOf U

/-- The main definition of regularity: `M` is regular iff it is constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M


private def Matrix.discretize {X Y : Type} (A : Matrix X Y ℚ) (n : ℕ) : Matrix X Y (ZMod n) :=
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

private lemma todoZ [DecidableEq α] [Fintype α] (A : Matrix α α ℤ)
    (hA : ∀ i j, A i j ∈ Set.range SignType.cast) (hA' : A.det ∈ Set.range SignType.cast) :
    A.det = (0 : ℤ) ↔ (Matrix.of (if A · · = 0 then 0 else 1)).det = (0 : Z2) := by
  have h0 : A.det = (0 : ℤ) ↔ (A.det : Z2) = (0 : Z2)
  · obtain ⟨s, hs⟩ := hA'
    cases s with
    | zero => exact ⟨congrArg Int.cast, fun _ => hs.symm⟩
    | pos | neg =>
      simp at hs
      rw [←hs]
      simp
  rw [h0, A.det_coe]
  constructor -- TODO eliminate repeated code below (if kept at all)
  · intro foo
    convert foo
    ext i j
    simp
    if hij0 : A i j = 0 then
      simp_all
    else
      simp [*]
      symm
      apply Fin2_eq_1_of_ne_0
      intro contr
      apply hij0
      obtain ⟨s, hs⟩ := hA i j
      cases s with
      | zero => exact hs.symm
      | pos | neg =>
        exfalso
        simp at hs
        rw [←hs] at contr
        simp at contr
  · intro foo
    convert foo
    ext i j
    simp
    if hij0 : A i j = 0 then
      simp_all
    else
      simp [*]
      apply Fin2_eq_1_of_ne_0
      intro contr
      apply hij0
      obtain ⟨s, hs⟩ := hA i j
      cases s with
      | zero => exact hs.symm
      | pos | neg =>
        exfalso
        simp at hs
        rw [←hs] at contr
        simp at contr

private lemma todo [DecidableEq α] [Fintype α] {A : Matrix α α ℚ}
    (hA : ∀ i j, A i j ∈ Set.range SignType.cast) (hA' : A.det ∈ Set.range SignType.cast) :
    A.det = (0 : ℚ) ↔ (Matrix.of (if A · · = 0 then 0 else 1)).det = (0 : Z2) := by
  have key : (((Matrix.of (if A · · = 0 then 0 else 1)).det : ℤ) : ℚ) = A.det
  · convert (Matrix.of (if A · · = 0 then 0 else 1)).det_coe ℚ
    ext i j
    simp
    obtain ⟨s, hs⟩ := hA i j
    cases s with
    | zero => simp_all only [Set.mem_range, SignType.zero_eq_zero, SignType.coe_zero, ite_true]
    | pos => aesop
    | neg => sorry -- TODO does not work this way; preserving `-1` is necessary now.
  convert todoZ (Matrix.of (if A · · = 0 then 0 else 1)) (by sorry) (by sorry)
  · simp [←key]
  · simp

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary [DecidableEq α] {M : Matroid α} [Finite M.E] (hM : M.IsRegular) :
    ∃ V : VectorMatroid α Z2, V.toMatroid = M := by
  obtain ⟨X, Y, A, hA, rfl⟩ := hM
  use ⟨X, Y, Matrix.of (if A · · = 0 then 0 else 1)⟩
  ext I hI
  · simp
  have : Fintype I.Elem := Set.Finite.fintype (Finite.Set.subset (VectorMatroid.mk X Y A).toMatroid.E hI)
  clear hI
  simp only [VectorMatroid.toMatroid_indep, VectorMatroid.indepCols_iff_submatrix]
  constructor <;> intro ⟨hIY, hA'⟩ <;> use hIY <;>
      rw [Matrix.linearIndendent_iff_exists_submatrix_det] at hA' ⊢ <;>
      obtain ⟨f, hAf⟩ := hA' <;> use f <;> intro contr <;>
      rw [Matrix.transpose_submatrix, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at hAf contr <;>
      apply hAf <;> have hAT := hA.transpose <;> have hAf' := (hAT.submatrix hIY.elem f).apply <;>
      rw [Matrix.isTotallyUnimodular_iff_fintype] at hAT
  · rwa [todo hAf' (hAT ..)] at contr
  · rwa [todo hAf' (hAT ..)]

/-- Every regular matroid has a standard binary representation. -/
lemma Matroid.IsRegular.isBinaryStd [DecidableEq α] {M : Matroid α} [Finite M.E] (hM : M.IsRegular) :
    ∃ S : StandardRepr α Z2, S.toMatroid = M := by
  obtain ⟨V, hV⟩ := hM.isBinary
  obtain ⟨S, hS⟩ := V.exists_standardRepr
  rw [←hS] at hV
  exact ⟨S, hV⟩

/-- Matroid `M` that can be represented by a matrix over `Z2` with a TU signing -/
abbrev StandardRepr.HasTuSigning [DecidableEq α] (S : StandardRepr α Z2) : Prop :=
  S.B.HasTuSigning

/-- Matroid constructed from a standard representation is regular iff the binary matrix has a TU signing. -/
lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning [DecidableEq α] (S : StandardRepr α Z2) : -- TODO `S` finite ?
    S.toMatroid.IsRegular ↔ S.HasTuSigning := by
  constructor
  · intro ⟨X, Y, A, hA, hS⟩
    sorry
  · intro ⟨U, hU, hUS⟩
    use S.X, S.X ∪ S.Y, (U.prependId · ∘ Subtype.toSum)
    constructor
    · exact (hU.one_fromCols).comp_cols Subtype.toSum
    ext I hI <;> simp
    simp only [VectorMatroid.toMatroid_E] at hI
    constructor <;> intro linearlyI
    · use hI
      sorry
    · sorry
