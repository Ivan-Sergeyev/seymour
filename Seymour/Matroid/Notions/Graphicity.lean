import Seymour.Matroid.Notions.Regularity


-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops
/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic {α : Type} (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ M = (VectorMatroid.mk X Y A).toMatroid

/-- Matroid is cographic iff its dual is represented by an incidence matrix of a graph. -/
def Matroid.IsCographic {α : Type} (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic {α : Type} {X Y : Set α} {M : Matroid α} {A : Matrix X Y ℚ}
    (hMA : M = (VectorMatroid.mk X Y A).toMatroid) (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  sorry

/-- Graphic matroid is regular. -/
lemma Matroid.IsGraphic.isRegular {α : Type} {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  sorry

/-- Cographic matroid is regular. -/
lemma Matroid.IsCographic.is_regular {α : Type} {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  sorry
