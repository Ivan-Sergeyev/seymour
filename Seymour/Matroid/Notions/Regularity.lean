import Seymour.Matroid.Constructors.StandardRepresentation


/-- Matrix `S` is a TU signing of `U` iff `S` is TU and its entries are the same as in `U` up to signs. -/
def Matrix.IsTuSigningOf {X Y : Type} (S : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  S.IsTotallyUnimodular ∧ ∀ i j, |S i j| = (U i j).val
-- do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (A : Matrix X Y (ZMod n)) : Prop :=
  ∃ A' : Matrix X Y ℚ, A'.IsTuSigningOf A

variable {α : Type}

/-- The main definition of regularity: `M` is regular iff it is constructed from a `VectorMatroid` with a rational TU matrix. -/
def Matroid.IsRegular (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ (VectorMatroid.mk X Y A).toMatroid = M

/-- Every regular matroid is binary. -/
lemma Matroid.IsRegular.isBinary {M : Matroid α} (hM : M.IsRegular) :
    ∃ X Y : Set α, ∃ A : Matrix X Y Z2, (VectorMatroid.mk X Y A).toMatroid = M := by
  sorry

/-- Every regular matroid has a standard binary representation. -/
lemma Matroid.IsRegular.isBinaryStd [DecidableEq α] {M : Matroid α} (hM : M.IsRegular) :
    ∃ X Y : Set α, ∃ hXY : X ⫗ Y, ∃ A : Matrix X Y Z2,
      ∃ dinX : (∀ a, Decidable (a ∈ X)), ∃ dinY : (∀ a, Decidable (a ∈ Y)),
        (StandardRepr.mk X Y hXY A dinX dinY).toMatroid = M := by
  sorry

/-- Matroid `M` that can be represented by a matrix over `Z2` with a TU signing -/
abbrev StandardRepr.HasTuSigning [DecidableEq α] (S : StandardRepr α Z2) : Prop :=
  S.B.HasTuSigning

/-- Matroid constructed from a standard representation is regular iff the binary matrix has a TU signing. -/
lemma StandardRepr.toMatroid_isRegular_iff_hasTuSigning [DecidableEq α] (S : StandardRepr α Z2) :
    S.toMatroid.IsRegular ↔ S.HasTuSigning := by
  sorry
