import Seymour.Matroid.Operations.Sum1
import Seymour.Matroid.Operations.Sum2
import Seymour.Matroid.Operations.Sum3
import Seymour.Matroid.Notions.Graphicness


/-- Matroid R10. -/
def matroidR10 : StandardRepr (Fin 10) Z2 where
  X := (·.val < 5)
  Y := (·.val ≥ 5)
  hXY := by
    rw [Set.disjoint_left]
    intro _ hX hY
    rw [Set.mem_def] at hX hY
    omega
  B := !![1, 0, 0, 1, 1; 1, 1, 0, 0, 1; 0, 1, 1, 0, 1; 0, 0, 1, 1, 1; 1, 1, 1, 1, 1].submatrix
    (fun i => ⟨i.val, i.property⟩)
    (fun j => ⟨j.val - 5, by omega⟩)
  decmemX := (·.val.decLt 5)
  decmemY := Fin.decLe 5

variable {α : Type} [DecidableEq α]

/-- Given matroid can be constructed from graphic matroids & cographics matroids & R10 using 1-sums & 2-sums & 3-sums. -/
inductive Matroid.IsGood : Matroid α → Prop
-- leaf constructors
| graphic {M : Matroid α} (hM : M.IsGraphic) : M.IsGood
| cographic {M : Matroid α} (hM : M.IsCographic) : M.IsGood
| isomorphicR10 {M : Matroid α} {e : α ≃ Fin 10} (hM : M.mapEquiv e = matroidR10.toMatroid) : M.IsGood
-- fork constructors
| is1sum {M M₁ M₂ : Matroid α} (hM : M.Is1sumOf M₁ M₂) : M.IsGood
| is2sum {M M₁ M₂ : Matroid α} (hM : M.Is2sumOf M₁ M₂) : M.IsGood
| is3sum {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : M.IsGood

/-- THE HOLY GRAIL. -/
theorem theSeymourDecomposition {M : Matroid α} (hM : M.IsRegular) : M.IsGood := by
  sorry
