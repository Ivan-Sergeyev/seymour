import Seymour.Matroid.Notions.Graphicness
import Seymour.Matrix.TotalUnimodularityTest


def matroidR10_B_Z2 : Matrix (Fin 5) (Fin 5) Z2 :=
  !![1, 0, 0, 1, 1; 1, 1, 0, 0, 1; 0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 1, 1, 1, 1, 1]

def matroidR10_B_ℚ : Matrix (Fin 5) (Fin 5) ℚ :=
  matroidR10_B_Z2.map (·.val)

theorem matroidR10_B_ℚ_TU : matroidR10_B_ℚ.IsTotallyUnimodular :=
  matroidR10_B_ℚ.isTotallyUnimodular_of_testTotallyUnimodularFast (by decide +kernel)

def matroidR10_B_Z2_coe : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } Z2 :=
  matroidR10_B_Z2.submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩)

def matroidR10_B_ℚ_coe : Matrix { x : Fin 10 | x.val < 5 } { x : Fin 10 | 5 ≤ x.val } ℚ :=
  matroidR10_B_Z2_coe.map (·.val)

theorem matroidR10_B_ℚ_coe_eq_coe_matroidR10_B_ℚ : matroidR10_B_ℚ_coe = matroidR10_B_ℚ.submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩) := by
  simp_all only [Set.coe_setOf, Set.mem_setOf_eq]
  rfl

/-- Matroid R10. -/
def matroidR10 : StandardRepr (Fin 10) Z2 where
  X := { x | x.val < 5 }
  Y := { x | 5 ≤ x.val }
  hXY := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp
  -- K. Truemper, 9.2.13
  B := matroidR10_B_Z2_coe
  decmemX := (·.val.decLt 5)
  decmemY := Fin.decLe 5

@[simp] theorem matroidR10_X_eq : matroidR10.X = { x | x.val < 5 } := rfl
@[simp] theorem matroidR10_Y_eq : matroidR10.Y = { x | 5 ≤ x.val } := rfl
@[simp] theorem matroidR10_B_eq : matroidR10.B = matroidR10_B_Z2_coe := rfl

@[simp]
theorem matroidR10.isRegular : matroidR10.toMatroid.IsRegular := by
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning]
  use matroidR10_B_ℚ_coe
  simp_rw [Matrix.IsTuSigningOf]
  refine ⟨?_, fun i j => ?_⟩
  · rw [matroidR10_B_ℚ_coe_eq_coe_matroidR10_B_ℚ]
    exact Matrix.IsTotallyUnimodular.submatrix _ _ matroidR10_B_ℚ_TU
  · rw [matroidR10_B_ℚ_coe, matroidR10_B_eq]
    simp_rw [Set.coe_setOf, Matrix.map_apply, abs_eq_self]
    exact Nat.cast_nonneg _
