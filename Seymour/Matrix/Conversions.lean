import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic.Conversions
import Seymour.Matrix.Signing


/-!
# Conversion between set-indexed block-like matrices and type-indexed block matrices

These conversions are used in 1-sum, 2-sum, and 3-sum of standard representations.
-/

variable {α R : Type} {T₁ T₂ S₁ S₂ : Set α}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (A : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) R) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem R :=
  ((A ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.IsTotallyUnimodular.toMatrixUnionUnion [CommRing R] {A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R}
    (hA : A.IsTotallyUnimodular) :
    A.toMatrixUnionUnion.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intros
  apply hA

/-- A signing block matrix stays a signing of a matrix after converting both matrices to be indexed by set unions. -/
lemma Matrix.IsSigningOf.toMatrixUnionUnion [LinearOrderedRing R]
    {A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R} {U : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) Z2}
    (hAU : A.IsSigningOf U) :
    A.toMatrixUnionUnion.IsSigningOf U.toMatrixUnionUnion :=
  (hAU ·.toSum ·.toSum)

variable {T S : Set α}

/-- Convert a block matrix to a matrix over set unions named as single indexing sets. -/
def Matrix.toMatrixElemElem (A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    Matrix T S R :=
  hT ▸ hS ▸ A.toMatrixUnionUnion

/-- Direct characterization of `Matrix.toMatrixElemElem` entries. -/
lemma Matrix.toMatrixElemElem_apply (A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) (i : T) (j : S) :
    A.toMatrixElemElem hT hS i j = A (hT ▸ i).toSum (hS ▸ j).toSum := by
  subst hT hS
  rfl

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions named as
    single indexing sets. -/
lemma Matrix.IsTotallyUnimodular.toMatrixElemElem [CommRing R] {A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R}
    (hA : A.IsTotallyUnimodular) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    (A.toMatrixElemElem hT hS).IsTotallyUnimodular :=
  hT ▸ hS ▸ hA.toMatrixUnionUnion

/-- A signing block matrix stays a signing of a matrix after converting both matrices to be indexed by set unions named as
    single indexing sets. -/
lemma Matrix.IsSigningOf.toMatrixElemElem [LinearOrderedRing R]
    {A : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) R} {U : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) Z2}
    (hAU : A.IsSigningOf U) (hT : T = T₁ ∪ T₂) (hS : S = S₁ ∪ S₂) :
    (A.toMatrixElemElem hT hS).IsSigningOf (U.toMatrixElemElem hT hS) :=
  hT ▸ hS ▸ hAU.toMatrixUnionUnion
