import Seymour.Matroid.Notions.Regularity

open scoped Matrix

variable {α R : Type} [DecidableEq α] [DivisionRing R]

/-- The dual of standard representation (transpose the matrix and flip its signs). -/
def StandardRepr.dual (S : StandardRepr α R) : StandardRepr α R where
  X := S.Y
  Y := S.X
  hXY := S.hXY.symm
  B := - S.Bᵀ -- the sign is chosen following Oxley (which does not change the resulting matroid)
  decmemX := S.decmemY
  decmemY := S.decmemX

postfix:max "✶" => StandardRepr.dual

/-- The dual of dual is the original standard representation. -/
lemma StandardRepr.dual_dual (S : StandardRepr α R) : S✶✶ = S := by
  simp [StandardRepr.dual]

lemma StandardRepr.dual_indices_union_eq (S : StandardRepr α R) : S✶.X ∪ S✶.Y = S.X ∪ S.Y :=
  Set.union_comm .. ▸ rfl

lemma StandardRepr.dual_ground (S : StandardRepr α R) : S✶.toMatroid.E = S.toMatroid.E := by
  exact S.dual_indices_union_eq

lemma StandardRepr.dual_isBase_iff {S : StandardRepr α R} {G : Set α} (hG : G ⊆ S✶.toMatroid.E) :
    S✶.toMatroid.IsBase G ↔ S.toMatroid✶.IsBase G := by
  rw [StandardRepr.dual_ground] at hG
  rw [Matroid.dual_isBase_iff']
  simp only [hG, and_true]
  sorry -- Theorem 2.2.8 in Oxley

/-- The dual of standard representation gives a dual matroid. -/
lemma StandardRepr.dual_toMatroid (S : StandardRepr α R) :
    S✶.toMatroid = S.toMatroid✶ := by
  rw [← Matroid.dual_inj, Matroid.dual_dual, Matroid.ext_iff_isBase]
  constructor
  · rw [Matroid.dual_ground, StandardRepr.dual_ground]
  · intro G hG
    rw [Matroid.dual_ground] at hG
    simp_rw [Matroid.dual_isBase_iff hG, @S.dual_isBase_iff _ _ _ _ (S✶.toMatroid.E \ G) (by tauto_set)]
    rw [StandardRepr.dual_ground] at hG ⊢
    rw [Matroid.dual_isBase_iff (by tauto_set), Set.diff_diff_cancel_left hG]

/-- Every vector matroid's dual has a standard representation. -/
lemma VectorMatroid.dual_exists_standardRepr (M : VectorMatroid α R) :
    ∃ S' : StandardRepr α R, S'.toMatroid = M.toMatroid✶ :=
  have ⟨S, hS⟩ := M.exists_standardRepr
  ⟨S✶, hS ▸ S.dual_toMatroid⟩

lemma Matroid.IsRegular.dual {M : Matroid α} (hM : M.IsRegular) : M✶.IsRegular := by
  obtain ⟨S, rfl⟩ := hM.hasBinaryStandardRepr
  have : Finite S.X := sorry
  have : Finite S✶.X := sorry
  rw [←S.dual_toMatroid]
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM ⊢
  obtain ⟨A, hA, hAS⟩ := hM
  simp only [StandardRepr.dual]
  refine ⟨-Aᵀ, hA.transpose.neg, fun i : S.Y => fun j : S.X => ?_⟩
  convert hAS j i using 1 <;> simp

lemma Matroid.IsRegular.of_dual {M : Matroid α} (hM : M✶.IsRegular) : M.IsRegular :=
  M.dual_dual ▸ hM.dual
