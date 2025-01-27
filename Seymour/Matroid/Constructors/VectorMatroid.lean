import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual

import Seymour.Basic
import Seymour.ForMathlib.MatrixManip


section Definition

/-- Vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (α R : Type) [Ring R] where
  /-- row index collection (it suffices to use `Set α` to produce any vector matroid) -/
  X : Type
  /-- column index set -/
  E : Set α
  /-- matrix defining a vector matroid -/
  A : Matrix X E R -- here `Set.Elem` is called

variable {α R : Type} [Ring R]

/-- Vector matroid corresponding to matrix `A`. -/
def Matrix.toVectorMatroid {X : Type} {E : Set α} (A : Matrix X E R) : VectorMatroid α R :=
  ⟨X, E, A⟩

/-- todo: desc -/
def Matrix.IndepCols {X : Type} {E : Set α} (A : Matrix X E R) (S : Set α) : Prop :=
  ∃ hS : S ⊆ E, LinearIndependent R (A.submatrix id hS.elem).transpose

/-- A set `S` is independent in `M[A]` iff `S` is a linearly independent subset of columns in `A`. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (S : Set α) : Prop :=
  M.A.IndepCols S

/-- Empty set is independent. -/
theorem VectorMatroid.indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ := by
  use Set.empty_subset M.E
  exact linearIndependent_empty_type

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.indepCols_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) :
    M.IndepCols I := by
  obtain ⟨hJ, hM⟩ := hMJ
  use hIJ.trans hJ
  show LinearIndependent R (fun i j => M.A j (hJ.elem (Subtype.map id hIJ i)))
  apply hM.comp
  intro _ _ hf
  apply Subtype.eq
  simpa [Subtype.map] using hf

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.indepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  sorry -- TODO important

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.indepCols_maximal (M : VectorMatroid α R) (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols S := by
  sorry -- TODO important

/-- Vector matroid expressed as `IndepMatroid`. -/
def VectorMatroid.toIndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.E
  Indep := M.IndepCols
  indep_empty := M.indepCols_empty
  indep_subset := M.indepCols_subset
  indep_aug := M.indepCols_aug
  indep_maximal S _ := M.indepCols_maximal S
  subset_ground _ := Exists.choose

end Definition


section API

variable {α R : Type} [Ring R]

/-- Vector matroid converted to `Matroid`. -/
def VectorMatroid.toMatroid (M : VectorMatroid α R) : Matroid α :=
  M.toIndepMatroid.matroid

@[simp]
lemma VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = M.E :=
  rfl

@[simp]
lemma VectorMatroid.toMatroid_indep (M : VectorMatroid α R) : M.toMatroid.Indep = M.IndepCols :=
  rfl

end API


section EquivalentTransformations

-- todo: section 2.2/6.3 from Oxley: Different matroid representations
-- the following operations on `A` do not change `M[A]`:
-- 2.2.1 Interchange two rows.  <-- can be generalized for free to reindexing of rows
-- 2.2.2 Multiply a row by non-zero.
-- 2.2.3 Replace a row by the sum of that row and another.
-- 2.2.4 Adjoin or remove a zero row.
-- 2.2.5 Interchange two columns (the labels moving with the columns).  <-- trivial in lean: indices are labeled and unordered
-- 2.2.6 Multiply a column by a non-zero member of F.
-- 2.2.7 Replace each matrix entry by its image under some automorphism of F.

-- todo: if A is non-zero, it can be reduced to [I | B] by a sequence of operations of types 2.2.1-2.2.5

end EquivalentTransformations


section StandardRepr

/-- Standard matrix representation of a vector matroid. -/
structure StandardRepr (α R : Type) [Ring R] where
  /-- row index set -/
  X : Set α
  /-- column index set -/
  Y : Set α
  /-- ability to check if an element belongs to `X` -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- ability to check if an element belongs to `Y` -/
  decmemY : ∀ a, Decidable (a ∈ Y)
  /-- `X` and `Y` are disjoint -/
  hXY : X ⫗ Y
  /-- standard representation matrix -/
  B : Matrix X Y R

variable {α R : Type} [Ring R]

-- Automatically infer decidability when `StandardRepr` is present.
attribute [instance] StandardRepr.decmemX
attribute [instance] StandardRepr.decmemY

variable [DecidableEq α]

/-- Vector matroid constructed from standard representation. -/
def StandardRepr.toVectorMatroid (S : StandardRepr α R) : VectorMatroid α R :=
  ⟨S.X, S.X ∪ S.Y, Matrix.fromColsSetUnion 1 S.B⟩

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.E = S.X ∪ S.Y :=
  rfl

/-- Full representation matrix of vector matroid is `[I | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A (S : StandardRepr α R) :
    S.toVectorMatroid.A = Matrix.fromColsSetUnion 1 S.B :=
  rfl

/-- Set is independent in vector matroid iff corresponding set of columns of `[I | B]` is linearly independent over `R`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_indep (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.Indep = S.toVectorMatroid.IndepCols :=
  rfl

/-- todo: desc -/
lemma VectorMatroid.exists_standardRepr (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, M = S.toVectorMatroid := by
  sorry

/-- todo: desc -/
lemma VectorMatroid.exists_standardRepr_base {B : Set α}
    (M : VectorMatroid α R) (hB : M.toMatroid.Base B) (hBE : B ⊆ M.E) :
    ∃ S : StandardRepr α R, M.X = B ∧ M = S.toVectorMatroid := by
  sorry

/-- Matroid constructed from standard representation. -/
def StandardRepr.toMatroid (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

/-- The identity matrix has linearly independent rows. -/
lemma Matrix.one_linearIndependent : LinearIndependent R (1 : Matrix α α R) := by
-- Riccardo Brasca proved:
  rw [linearIndependent_iff]
  intro l hl
  ext j
  simpa [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum_apply', Matrix.one_apply] using congr_fun hl j
-- TODO replace with Mathlib version when available

/-- todo: desc -/
lemma StandardRepr.toMatroid_base (S : StandardRepr α R) :
    S.toMatroid.Base S.X := by
  unfold StandardRepr.toMatroid StandardRepr.toVectorMatroid VectorMatroid.toMatroid
  apply Matroid.Indep.base_of_forall_insert
  · simp [Matrix.fromColsSetUnion, VectorMatroid.toIndepMatroid, VectorMatroid.IndepCols, Matrix.IndepCols]
    show LinearIndependent R ((Matrix.fromCols 1 S.B).transpose.submatrix _ id)
    rw [Matrix.transpose_fromCols, Matrix.transpose_one]
    simpa [Matrix.fromRows, Matrix.submatrix, Subtype.toSum, HasSubset.Subset.elem] using Matrix.one_linearIndependent
  · intro e he
    have e_in_Y : e ∈ S.Y
    · sorry
    -- TODO if you add anything extra to the identity matrix, it becomes singular.
    sorry

def StandardRepr.dual (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  decmemX := S.decmemY
  decmemY := S.decmemX
  hXY := S.hXY.symm
  B := - S.B.transpose

postfix:max "✶" => StandardRepr.dual

/-- todo: desc -/
lemma StandardRepr.toMatroid_dual (S : StandardRepr α R) :
    S.toMatroid✶ = S✶.toMatroid :=
  sorry -- Theorem 2.2.8 in Oxley

/-- todo: desc -/
lemma VectorMatroid.dual_exists_standardRepr (M : VectorMatroid α R) :
    ∃ S' : StandardRepr α R, M.toMatroid✶ = S'.toMatroid :=
  have ⟨S, hS⟩ := M.exists_standardRepr
  ⟨S✶, hS ▸ S.toMatroid_dual⟩

end StandardRepr
