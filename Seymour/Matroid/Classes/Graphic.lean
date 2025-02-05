import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Regular


section IsGraphic

/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic {α : Type} [DecidableEq α] (M : Matroid α) : Prop :=
  ∃ X Y : Type, ∃ A : Matrix X Y ℚ, M.IsRepresentedBy A ∧ A.IsGraphic

/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic {α X Y : Type} {M : Matroid α} {A : Matrix X Y ℚ}
    (hMA : M.IsRepresentedBy A) (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  sorry

/-- Graphic matroid is regular. -/
lemma Matroid.IsGraphic.isRegular {α : Type} [DecidableEq α] {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  rw [Matroid.isRegular_iff_hasTuRepr]
  obtain ⟨X, Y, A, hMA, hA⟩ := hM
  unfold Matroid.HasTuRepr
  exact ⟨X, Y, A, hMA.isTotallyUnimodular_of_isGraphic hA, hMA⟩

end IsGraphic


section IsCographic

/-- Matroid is cographic iff its dual is represented by an incidence matrix of a graph. -/
def Matroid.IsCographic {α : Type} [DecidableEq α] (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Cographic matroid is regular. -/
lemma Matroid.IsCographic.is_regular {α : Type} [DecidableEq α] {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  M.isRegular_iff_dual_isRegular.← hM.isRegular

end IsCographic
