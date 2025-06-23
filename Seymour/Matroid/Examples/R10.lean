import Seymour.Matroid.Properties.Graphicness
import Seymour.Matrix.TotalUnimodularityTest

/-!
# Matroid R10

This file studies the R10 matroid.
-/

def matrixR10auxZ2 : Matrix (Fin 5) (Fin 5) Z2 :=
  !![1, 0, 0, 1, 1; 1, 1, 0, 0, 1; 0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 1, 1, 1, 1, 1]

def matrixR10auxRat : Matrix (Fin 5) (Fin 5) ℚ :=
  matrixR10auxZ2.map (·.val)

lemma matrixR10auxRat_isTotallyUnimodular : matrixR10auxRat.IsTotallyUnimodular :=
  matrixR10auxRat.isTotallyUnimodular_of_testTotallyUnimodularFast (by decide +kernel)

def matrixR10Z2 : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } Z2 :=
  matrixR10auxZ2.submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩)

def matrixR10Rat : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } ℚ :=
  matrixR10Z2.map (·.val)

lemma matrixR10Rat_eq_coe_matrixR10auxRat :
    matrixR10Rat = matrixR10auxRat.submatrix (fun i => ⟨i.val, i.property⟩) (fun j => ⟨j.val - 5, by omega⟩) := by
  simp_all only [Set.coe_setOf, Set.mem_setOf_eq]
  rfl

/-- Matroid R10 (see Klaus Truemper, 9.2.13). -/
def matroidR10 : StandardRepr (Fin 10) Z2 where
  X := { x | x.val < 5 }
  Y := { x | 5 ≤ x.val }
  hXY := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext
    simp
  B := matrixR10Z2
  decmemX := (·.val.decLt 5)
  decmemY := Fin.decLe 5

@[simp] lemma matroidR10_X_eq : matroidR10.X = { x | x.val < 5 } := rfl
@[simp] lemma matroidR10_Y_eq : matroidR10.Y = { x | 5 ≤ x.val } := rfl
@[simp] lemma matroidR10_B_eq : matroidR10.B = matrixR10Z2 := rfl

@[simp]
lemma matroidR10.isRegular : matroidR10.toMatroid.IsRegular := by
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning]
  use matrixR10Rat
  simp_rw [Matrix.IsTuSigningOf]
  refine ⟨?_, fun i j => ?_⟩
  · rw [matrixR10Rat_eq_coe_matrixR10auxRat]
    apply matrixR10auxRat_isTotallyUnimodular.submatrix
  · rw [matrixR10Rat, matroidR10_B_eq]
    simp_rw [Set.coe_setOf, Matrix.map_apply, abs_eq_self]
    apply Nat.cast_nonneg
