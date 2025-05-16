import Seymour.Matrix.TotalUnimodularityTest
import Seymour.Matroid.Properties.Regularity


def matrixR10_Z2 : Matrix (Fin 5) (Fin 5) Z2 :=
  !![
    1, 0, 0, 1, 1;
    1, 1, 0, 0, 1;
    0, 1, 1, 0, 1;
    0, 0, 1, 1, 1;
    1, 1, 1, 1, 1
  ]

def matrixR10_Rat : Matrix (Fin 5) (Fin 5) ℚ :=
  matrixR10_Z2.map (·.val)

lemma matrixR10_Rat_isTotallyUnimodular : matrixR10_Rat.IsTotallyUnimodular :=
  matrixR10_Rat.isTotallyUnimodular_of_testTotallyUnimodularFast (by decide +kernel)

def matrixR10Z2 : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } Z2 :=
  matrixR10_Z2.submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩)

def matrixR10Rat : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } ℚ :=
  matrixR10Z2.map (·.val)

lemma matrixR10Rat_eq_coe_matrixR10_Rat :
    matrixR10Rat = matrixR10_Rat.submatrix (fun i => ⟨i.val, i.property⟩) (fun j => ⟨j.val - 5, by omega⟩) := by
  simp_all only [Set.coe_setOf, Set.mem_setOf_eq]
  rfl

/-- Matroid R10 (see Klaus Truemper, 9.2.13). -/
def matroidR10 : StandardRepr (Fin 10) Z2 where
  X := { x | x.val < 5 }
  Y := { x | 5 ≤ x.val }
  hXY := (by rw [Set.disjoint_iff_inter_eq_empty]; ext; simp)
  A := matrixR10Z2
  deqX := Subtype.instDecidableEq
  deqY := Subtype.instDecidableEq
  dmemX := (·.val.decLt 5)
  dmemY := Fin.decLe 5

@[simp] lemma matroidR10_X_eq : matroidR10.X = { x | x.val < 5 } := rfl
@[simp] lemma matroidR10_Y_eq : matroidR10.Y = { x | 5 ≤ x.val } := rfl
@[simp] lemma matroidR10_A_eq : matroidR10.A = matrixR10Z2 := rfl

@[simp]
lemma matroidR10.isRegular : matroidR10.toMatroid.IsRegular := by
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning]
  use matrixR10Rat
  simp_rw [Matrix.IsTuSigningOf]
  refine ⟨fun i j => ?_, ?_⟩
  · rw [matrixR10Rat, matroidR10_A_eq]
    simp_rw [Set.coe_setOf, Matrix.map_apply, abs_eq_self]
    apply Nat.cast_nonneg
  · rw [matrixR10Rat_eq_coe_matrixR10_Rat]
    apply matrixR10_Rat_isTotallyUnimodular.submatrix
