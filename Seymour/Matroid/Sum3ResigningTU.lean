import Seymour.Basic.FunctionToHalfSum
import Seymour.Matrix.Conversions
import Seymour.Matrix.Determinants
import Seymour.Matrix.PartialUnimodularity
import Seymour.Matrix.Pivoting
import Seymour.Matroid.Regularity

/-!
    In this file, we prove a key lemma needed for a more elegant implementation of 3-sums:
    * If `A` and `B` are TU matrices that have the same absolute value,
      then there exists a resigning (via multiplying rows and columns by `±1` factors) that transforms `B` into `A`
    * We don't prove this lemma in full generality, but rather:
      - only for specific small dimensions (we only need 3x3, but we start with 2x2 to understand how the proof should work)
      - only for special matrix form ([1 1 0 / D | [1/1]] form)
-/

-- note: moreover, `u` and `v` have values in `±1`
-- todo: make statement constructive
lemma Matrix.IsTotallyUnimodular.eq_tu_exists_resigning_two {A B : Matrix (Fin 2) (Fin 2) ℚ}
    (hA : A.IsTotallyUnimodular) (hB : B.IsTotallyUnimodular) (hAB : ∀ i j, |A i j| = |B i j|) :
    ∃ u : Fin 2 → ℚ, ∃ v : Fin 2 → ℚ, ∀ i j, A i j = u i * v j * B i j := by
  set t0 := if hAB00 : A 0 0 / B 0 0 = 0 then 1 else A 0 0 / B 0 0
  use ![1, t0 * B 1 0 / A 1 0] -- todo: same as t0 for second multiplicand here
  use ![t0, A 0 1 / B 0 1] -- todo: same as t0 for second entry here
  intro i j
  have hBij := hB.apply i j
  have hABij := hAB i j
  fin_cases i <;> fin_cases j <;> simp
  · simp only [Fin.isValue, Set.mem_range] at hBij
    obtain ⟨s ,hs⟩ := hBij
    cases s with
    | zero =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [←hs, hABij]
        simp
    | neg =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        unfold t0
        cases hABij with
        | inl hABij =>
            rw [←hs, hABij]
            simp
        | inr hABij =>
            rw [←hs, hABij]
            simp
        rfl
    | pos =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        unfold t0
        cases hABij with
        | inl hABij =>
            rw [←hs, hABij]
            simp
        | inr hABij =>
            rw [←hs, hABij]
            simp
        rfl
  · simp only [Fin.isValue, Set.mem_range] at hBij
    obtain ⟨s ,hs⟩ := hBij
    cases s with
    | zero =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [←hs, hABij]
        simp
    | neg =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        cases hABij with
        | inl hABij => rw [←hs, hABij]; simp
        | inr hABij => rw [←hs, hABij]; simp
        rfl
    | pos =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        cases hABij with
        | inl hABij => rw [←hs, hABij]; simp
        | inr hABij => rw [←hs, hABij]; simp
        rfl
  · simp only [Fin.isValue, Set.mem_range] at hBij
    obtain ⟨s ,hs⟩ := hBij
    have hAB00 : 1 = t0 * t0
    · have hA00 := hA.apply 0 0
      have hB00 := hB.apply 0 0
      have hAB00 := hAB 0 0
      simp at hA00 hB00
      obtain ⟨a, ha⟩ := hA00
      obtain ⟨b, hb⟩ := hB00
      cases a <;> cases b
      all_goals
        simp at ha hb
        unfold t0
        rw [←ha, ←hb] at hAB00 ⊢
      all_goals simp at hAB00 -- eliminates 4 inconsistent cases
      all_goals simp -- closes remaining goals
    cases s with
    | zero =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [←hs, hABij]
        simp
    | neg =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        cases hABij with
        | inl hABij =>
            rw [←hs, hABij]
            simp
            rw [←hAB00]
        | inr hABij =>
            rw [←hs, hABij]
            simp
            rw [←hAB00]
        rfl
    | pos =>
        simp at hs hABij
        rw [←hs] at hABij
        simp at hABij
        rw [abs_eq] at hABij
        cases hABij with
        | inl hABij =>
            rw [←hs, hABij]
            simp
            rw [←hAB00]
        | inr hABij =>
            rw [←hs, hABij]
            simp
            rw [div_neg, div_one, neg_mul]
            rw [←hAB00]
        rfl
  · simp only [Fin.isValue, Set.mem_range] at hBij
    obtain ⟨s ,hs⟩ := hBij
    sorry -- todo: need to use TUness here

/-!
  idea for an easier proof:
  * use characterization to reduce to special cases that e.g. A can be
  * perform simplifications for each case separately
-/

-- todo: see notes for the `Fin 2` case
lemma Matrix.IsTotallyUnimodular.eq_tu_exists_resigning_three {A B : Matrix (Fin 3) (Fin 3) ℚ}
    (hA : A.IsTotallyUnimodular) (hB : B.IsTotallyUnimodular) (hAB : ∀ i j, |A i j| = |B i j|) :
    ∃ u : Fin 3 → ℚ, ∃ v : Fin 3 → ℚ, ∀ i j, A i j = u i * v j * B i j := by
  sorry
