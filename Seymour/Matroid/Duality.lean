import Seymour.Matroid.Regularity

/-!
# Matroid Duality

Here we study the duals of matroids given by their standard representation.
-/

open scoped Matrix

variable {α R : Type*} [DecidableEq α]

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual [DivisionRing R] (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.Bᵀ -- the sign is chosen following Oxley (it does not change the resulting matroid)
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of dual is the original standard representation. -/
lemma StandardRepr.dual_dual [DivisionRing R] (S : StandardRepr α R) : S✶✶ = S := by
  simp [StandardRepr.dual]

lemma StandardRepr.dual_indices_union_eq [DivisionRing R] (S : StandardRepr α R) : S✶.X ∪ S✶.Y = S.X ∪ S.Y :=
  Set.union_comm S.Y S.X

@[simp]
lemma StandardRepr.dual_ground [DivisionRing R] (S : StandardRepr α R) : S✶.toMatroid.E = S.toMatroid.E :=
  S.dual_indices_union_eq

lemma StandardRepr.toMatroid_dual_eq [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid✶ = S✶.toMatroid := by
  /-
  * follow proof of Theorem 2.2.8 in section "2.2 Duals of representable matroids" in James Oxley's Matroid Theory book
    - feel free to check the context
    - feel free to adapt the proof to make it more convenient to implement (ranks in Lean are notoriously inconvenient)
  * assume finiteness and propagate where necessary
    - reason: see section "2.6 Representability and thin independence" in "Axioms for infinite matroids" paper
  -/
  sorry

lemma Matroid.IsRegular.dual {M : Matroid α} (hM : M.IsRegular) :
    M✶.IsRegular := by
  /-
  proof outline:
  * take full representation of `M`
  * convert to standard representation using `Matrix.exists_standardRepr_isBase_isTotallyUnimodular`
  * apply `StandardRepr.toMatroid_dual_eq`
  -/
  sorry
