import Seymour.Basic.Fin
import Seymour.Matrix.Basic


/-- Lemma 10 (motivates the difference between the definition of 3-sum in our implementation and in Truemper's book). -/
lemma Matrix.isUnit_2x2 (Q : Matrix (Fin 2) (Fin 2) Z2) (hQ : IsUnit Q) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, Q.submatrix f g = 1 ∨ Q.submatrix f g = !![1, 1; 0, 1] := by
  -- identity
  let eᵢ : Fin 2 ≃ Fin 2 := Equiv.refl (Fin 2)
  -- swap 0<->1
  let eₛ : Fin 2 ≃ Fin 2 := Equiv.ofBijective ![1, 0] (by decide)
  -- `hQ` via explicit determinant
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, isUnit_iff_eq_one] at hQ
  -- case exhaustion
  by_cases hQ₀₀ : Q 0 0 = 0 <;> by_cases hQ₀₁ : Q 0 1 = 0 <;> by_cases hQ₁₀ : Q 1 0 = 0 <;> by_cases hQ₁₁ : Q 1 1 = 0
  · -- `!![0, 0; 0, 0]`
    exfalso
    simp_all
  · -- `!![0, 0; 0, 1]`
    exfalso
    simp_all
  · -- `!![0, 0; 1, 0]`
    exfalso
    simp_all
  · -- `!![0, 0; 1, 1]`
    exfalso
    simp_all
  · -- `!![0, 1; 0, 0]`
    exfalso
    simp_all
  · -- `!![0, 1; 0, 1]`
    exfalso
    simp_all
  · -- `!![0, 1; 1, 0]`
    use eₛ, eᵢ
    left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![0, 1; 1, 1]`
    use eₛ, eᵢ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 0; 0, 0]`
    exfalso
    simp_all
  · -- `!![1, 0; 0, 1]`
    use eᵢ, eᵢ
    left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 0; 1, 0]`
    exfalso
    simp_all
  · -- `!![1, 0; 1, 1]`
    use eₛ, eₛ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 0, 0]`
    exfalso
    simp_all
  · -- `!![1, 1; 0, 1]`
    use eᵢ, eᵢ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 1, 0]`
    use eᵢ, eₛ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hQ₀₀, hQ₀₁, hQ₁₀, hQ₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 1, 1]`
    exfalso
    simp_all [fin2_eq_1_of_ne_0]


variable {X Y Z R : Type} [Fintype Z] [DecidableEq Z] [CommRing R]

lemma Matrix.submatrix_det_zero_of_not_injective_right (A : Matrix X Y R) (f : Z → X) {g : Z → Y} (hg : ¬g.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [Function.not_injective_iff] at hg
  obtain ⟨i, j, hgij, hij⟩ := hg
  apply Matrix.det_zero_of_column_eq hij
  simp [hgij]

lemma Matrix.submatrix_det_zero_of_not_injective_left (A : Matrix X Y R) {f : Z → X} (hf : ¬f.Injective) (g : Z → Y):
    (A.submatrix f g).det = 0 := by
  rw [←Matrix.det_transpose, Matrix.transpose_submatrix]
  exact A.transpose.submatrix_det_zero_of_not_injective_right g hf
