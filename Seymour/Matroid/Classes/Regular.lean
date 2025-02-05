import Mathlib.Data.Matroid.Dual

import Seymour.Basic
import Seymour.Matroid.Classes.Representable
import Seymour.Matroid.Classes.Binary


variable {α : Type}

section TU_signing

/-- Matrix `S` is a TU signing of `U` if `S` is TU and its entries are the same as in `U` up to signs. -/
def Matrix.IsTuSigningOf {X Y : Type} (S : Matrix X Y ℚ) {n : ℕ} (U : Matrix X Y (ZMod n)) : Prop :=
  S.IsTotallyUnimodular ∧ ∀ i j, |S i j| = (U i j).val
-- do not ask `U.IsTotallyUnimodular` ... see `Matrix.overZ2_isTotallyUnimodular` for example

/-- Matrix `A` has a TU signing if there is a TU matrix whose entries are the same as in `A` up to signs. -/
def Matrix.HasTuSigning {X Y : Type} {n : ℕ} (A : Matrix X Y (ZMod n)) : Prop :=
  ∃ A' : Matrix X Y ℚ, A'.IsTuSigningOf A

end TU_signing


section Definitions

/-- Matroid `M` that can be represented over any field -/
def Matroid.IsRegular (M : Matroid α) : Prop :=
  ∀ F : Type, ∀ _F : Field F, M.IsRepresentableOver F

/-- Matroid `M` that can be represented by a matrix over `Z2` with a TU signing -/
def Matroid.HasTuSigning (M : Matroid α) : Prop :=
  ∃ X Y : Type, ∃ A : Matrix X Y Z2, A.HasTuSigning ∧ M.IsRepresentedBy A

/-- Matroid `M` that can be represented by a TU matrix -/
def Matroid.HasTuRepr (M : Matroid α) : Prop :=
  ∃ X Y : Type, ∃ A : Matrix X Y ℚ, A.IsTotallyUnimodular ∧ M.IsRepresentedBy A

end Definitions


section Equivalences

-- todo: prove equivalence of definitions above; see theorem 6.6.3 in Oxley

lemma Matroid.isRegular_iff_hasTuSigning (M : Matroid α) : M.IsRegular ↔ M.HasTuSigning := by
  sorry

lemma Matroid.isRegular_iff_hasTuRepr (M : Matroid α) : M.IsRegular ↔ M.HasTuRepr := by
  sorry

/-- Matroid `M` is regular iff it can be represented over both `Z2` and `Z3` -/
lemma Matroid.isRegular_iff_isRepresentableOver_Z2_and_Z3 (M : Matroid α) :
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ M.IsRepresentableOver Z3 := by
  sorry

/-- Matroid `M` is regular iff it can be represented over both `Z2` and over another field -/
lemma Matroid.isRegular.iff_representable_over_Z2_and_gt2 {M : Matroid α} :
    M.IsRegular ↔ M.IsRepresentableOver Z2 ∧ (∃ F : Type, ∃ hF : Field F, ringChar F > 2 ∧ M.IsRepresentableOver F) := by
  sorry

end Equivalences


section Corollaries

-- note: if M is regular, every minor of M is regular. however, matroid minors are not currently in mathlib

lemma Matroid.IsRegular.hasTuSigning_of_reprZ2 {X Y : Type} {M : Matroid α} {A : Matrix X Y Z2}
    (hM : M.IsRegular) (hMA : M.IsRepresentedBy A) :
    A.HasTuSigning := by
  sorry

/-- todo: desc -/
def Matroid.isRegular_iff_dual_isRegular (M : Matroid α) :
    M.IsRegular ↔ M✶.IsRegular := by
  sorry -- prop 2.2.22 in Oxley

-- todo: binary matroid is regular iff its standard representation matrix has a TU signing

end Corollaries
