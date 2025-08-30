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

lemma StandardRepr.is_TU_iff [DecidableEq α] (S : StandardRepr α ℚ) :
    S.toFull.IsTotallyUnimodular ↔ S.B.IsTotallyUnimodular := by
  constructor
  · intro h_toFull_TU
    have h_block_TU : ((1 : Matrix S.X S.X ℚ) ◫ S.B).IsTotallyUnimodular := by
      let h_equiv_symm := S.hXY.equivSumUnion.symm
      exact (Matrix.reindex_isTotallyUnimodular (1 ◫ S.B) (Equiv.refl ↑S.X) h_equiv_symm.symm).→ h_toFull_TU
    exact (Matrix.one_fromCols_isTotallyUnimodular_iff S.B).→ h_block_TU
  · intro h_B_TU
    have h_block_TU : ((1 : Matrix S.X S.X ℚ) ◫ S.B).IsTotallyUnimodular := by
      rw [Matrix.one_fromCols_isTotallyUnimodular_iff]
      exact h_B_TU
    exact Matrix.IsTotallyUnimodular.submatrix _ _ h_block_TU

lemma Matroid.IsRegular.dual {M : Matroid α} [Matroid.RankFinite M] (hM : M.IsRegular)  :
    M✶.IsRegular := by
  obtain ⟨X, Y, A, A_TU, eq_1⟩ := hM
  have exists_TU : ∃ S : StandardRepr α ℚ, S.toMatroid = A.toMatroid ∧ S.B.IsTotallyUnimodular := by
    let ⟨G, G_base⟩ := M.exists_isBase
    have hAG_base : A.toMatroid.IsBase G := by simp only [eq_1, G_base]
    have finite : Fintype G := (IsBase.finite G_base).fintype
    have ⟨S, a, b, c⟩ := A.exists_standardRepr_isBase_isTotallyUnimodular hAG_base A_TU
    exact ⟨S, b, c⟩
  obtain ⟨S, eq_2, S_TU⟩ := exists_TU 
  have finite : S.toMatroid.RankFinite := by rwa [eq_2, eq_1]
  rw [← eq_1, ← eq_2, StandardRepr.toMatroid_dual_eq S]
  use S✶.X, S✶.X ∪ S✶.Y, S✶.toFull
  refine ⟨?_, by rfl⟩
  rw [StandardRepr.is_TU_iff]
  apply Matrix.IsTotallyUnimodular.neg
  exact Matrix.IsTotallyUnimodular.transpose S_TU
