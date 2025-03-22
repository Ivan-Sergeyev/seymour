import Seymour.Matroid.Notions.Regularity


/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops

variable {α : Type}

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic (M : Matroid α) : Prop :=
  ∃ X Y : Set α, ∃ A : Matrix X Y ℚ, A.IsGraphic ∧ (VectorMatroid.mk X Y A).toMatroid = M

/-- Matroid is cographic iff its dual is represented by an incidence matrix of a graph. -/
def Matroid.IsCographic (M : Matroid α) : Prop :=
  M✶.IsGraphic

/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matrix.IsGraphic.isTotallyUnimodular_of_represents {X Y : Set α} {A : Matrix X Y ℚ} {M : Matroid α}
    (hA : A.IsGraphic) (hAM : (VectorMatroid.mk X Y A).toMatroid = M) :
    A.IsTotallyUnimodular := by
  sorry

/-- Graphic matroid is regular. -/
lemma Matroid.IsGraphic.isRegular {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular := by
  peel hM with X Y A hM
  exact ⟨Matrix.IsGraphic.isTotallyUnimodular_of_represents hM.1 hM.2, hM.2⟩

/-- Cographic matroid is regular. -/
lemma Matroid.IsCographic.isRegular {M : Matroid α} (hM : M.IsCographic) :
    M.IsRegular :=
  sorry
