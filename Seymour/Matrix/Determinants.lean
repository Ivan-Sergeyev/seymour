import Seymour.Basic.Fin
import Seymour.Matrix.Basic


/-- Lemma 10 (motivates the difference between the definition of 3-sum in our implementation and in Truemper's book). -/
lemma Matrix.isUnit_2x2 (A : Matrix (Fin 2) (Fin 2) Z2) (hA : IsUnit A) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, A.submatrix f g = 1 ∨ A.submatrix f g = !![1, 1; 0, 1] := by
  -- identity
  let eᵢ : Fin 2 ≃ Fin 2 := Equiv.refl (Fin 2)
  -- swap 0<->1
  let eₛ : Fin 2 ≃ Fin 2 := Equiv.ofBijective ![1, 0] (by decide)
  -- `hA` via explicit determinant
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, isUnit_iff_eq_one] at hA
  -- case exhaustion
  by_cases hA₀₀ : A 0 0 = 0 <;> by_cases hA₀₁ : A 0 1 = 0 <;> by_cases hA₁₀ : A 1 0 = 0 <;> by_cases hA₁₁ : A 1 1 = 0
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
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![0, 1; 1, 1]`
    use eₛ, eᵢ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 0; 0, 0]`
    exfalso
    simp_all
  · -- `!![1, 0; 0, 1]`
    use eᵢ, eᵢ
    left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 0; 1, 0]`
    exfalso
    simp_all
  · -- `!![1, 0; 1, 1]`
    use eₛ, eₛ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 0, 0]`
    exfalso
    simp_all
  · -- `!![1, 1; 0, 1]`
    use eᵢ, eᵢ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 1, 0]`
    use eᵢ, eₛ
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₀₀, hA₀₁, hA₁₀, hA₁₁, eᵢ, eₛ, fin2_eq_1_of_ne_0]
  · -- `!![1, 1; 1, 1]`
    exfalso
    simp_all [fin2_eq_1_of_ne_0]


variable {Z R : Type} [Fintype Z] [DecidableEq Z] [CommRing R]

lemma Matrix.det_eq_zero_of_col_sub_col_eq_col [CommRing R] [IsDomain R] (A : Matrix Z Z R) (j₀ j₁ j₂ : Z)
    (hAjjj : (A · j₀) - (A · j₁) = (A · j₂)) :
    A.det = (0 : R) := by
  rw [←Matrix.exists_mulVec_eq_zero_iff]
  use (fun j => if j = j₀ then 1 else if j = j₁ then 1 else if j = j₂ then -1 else 0), (by simpa using congr_fun · j₀)
  ext i
  simp [Matrix.mulVec]
  sorry

variable {X Y : Type}

lemma Matrix.submatrix_det_zero_of_not_injective_cols (A : Matrix X Y R) (f : Z → X) {g : Z → Y} (hg : ¬g.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [Function.not_injective_iff] at hg
  obtain ⟨i, j, hgij, hij⟩ := hg
  apply Matrix.det_zero_of_column_eq hij
  simp [hgij]

lemma Matrix.submatrix_det_zero_of_not_injective_rows (A : Matrix X Y R) {f : Z → X} (g : Z → Y) (hf : ¬f.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [←Matrix.det_transpose, Matrix.transpose_submatrix]
  exact A.transpose.submatrix_det_zero_of_not_injective_cols g hf
