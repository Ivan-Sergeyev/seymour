import Seymour.Matrix.Basic


lemma LinearEquiv.toMatrix'_inv {X R : Type} [Fintype X] [DecidableEq X] [CommRing R]
    (f : (X → R) ≃ₗ[R] (X → R)) :
    f.toMatrix'⁻¹ = f⁻¹.toMatrix' :=
  Matrix.inv_eq_right_inv (by simpa using (f.toLinearMap.toMatrix'_comp f.symm.toLinearMap).symm)
