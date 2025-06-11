import Seymour.Basic.Basic

/-!
# Matrix is a signing of another matrix

This file defines when a matrix is a signing of another matrix.
-/

variable {X Y R : Type} [LinearOrderedRing R] {n : ℕ}

/-- `LinearOrderedRing`-valued matrix `A` is a signing of `U` (matrix of the same size but different type) iff `A` has
    the same entries as `U` on respective positions up to signs. -/
def Matrix.IsSigningOf (A : Matrix X Y R) (U : Matrix X Y (ZMod n)) : Prop :=
  ∀ i : X, ∀ j : Y, |A i j| = (U i j).val

lemma Matrix.IsSigningOf.submatrix {X' Y' : Type} {A : Matrix X Y R} {U : Matrix X Y (ZMod n)}
    (hAU : A.IsSigningOf U) (f : X' → X) (g : Y' → Y) :
    (A.submatrix f g).IsSigningOf (U.submatrix f g) :=
  fun i j => hAU (f i) (g j)
