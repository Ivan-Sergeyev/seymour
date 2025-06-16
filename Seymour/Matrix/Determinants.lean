import Seymour.Basic.Fin
import Seymour.Matrix.Basic

/-!
# Determinants

This file provides lemmas about determinants that are not present in Mathlib.
-/

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

lemma Matrix.det_eq_zero_of_col_eq_mul_col (A : Matrix Z Z R) (j₀ j₁ : Z) (hjj : j₀ ≠ j₁) (k : R)
    (hAjj : ∀ i : Z, A i j₀ = k * A i j₁) :
    A.det = (0 : R) := by
  rw [←Matrix.det_updateCol_add_smul_self A hjj (k * -1)]
  simp_rw [smul_eq_mul]
  conv in _ * _ => rw [mul_comm, ←mul_assoc, mul_comm (A k j₁), ←hAjj k, mul_neg, mul_one]
  conv in _ + _ => rw [add_neg_cancel]
  refine Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => Matrix.updateCol_self

lemma Matrix.det_eq_zero_of_col_sub_col_eq_col [CommRing R] [IsDomain R] (A : Matrix Z Z R) (j₀ j₁ j₂ : Z)
    (hAjjj : (A · j₀) - (A · j₁) = (A · j₂)) :
    A.det = (0 : R) := by
  wlog hj₂ : j₀ ≠ j₁
  · push_neg at hj₂
    subst hj₂
    rw [sub_self, funext_iff] at hAjjj
    exact Matrix.det_eq_zero_of_column_eq_zero j₂ (Eq.symm <| hAjjj ·)
  wlog hj₁ : j₀ ≠ j₂
  · push_neg at hj₁
    subst hj₁
    rw [sub_eq_self, funext_iff] at hAjjj
    exact Matrix.det_eq_zero_of_column_eq_zero j₁ (hAjjj ·)
  wlog hj₀ : j₁ ≠ j₂
  · push_neg at hj₀
    subst hj₀
    rw [funext_iff] at hAjjj
    simp_rw [Pi.sub_apply, sub_eq_iff_eq_add] at hAjjj
    conv at hAjjj in _ = _ => rw [←mul_one (A x j₁), ←left_distrib, mul_comm]
    exact Matrix.det_eq_zero_of_col_eq_mul_col A j₀ j₁ hj₂ (1 + 1) hAjjj
  simp_rw [funext_iff, Pi.sub_apply] at hAjjj
  rw [←Matrix.exists_mulVec_eq_zero_iff]
  use (fun j : Z => if _ : j = j₀ then -1 else if _ : j = j₁ then 1 else if _ : j = j₂ then 1 else 0)
  use (by simpa using congr_fun · j₀)
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_dite, mul_one, mul_neg, mul_zero, Pi.zero_apply]
  specialize hAjjj i
  let f := fun (z : Z) => if z = j₀ then -A i j₀ else if z = j₁ then A i j₁ else if z = j₂ then A i j₀ - A i j₁ else 0
  conv_lhs => enter [2, x, 2, hxj₀]; rw [hxj₀, show -A i j₀ = f x by unfold f; split_ifs; rfl]
  conv_lhs => enter [2, x, 3, hj₂, 2, hxj₁]; rw [hxj₁, show A i j₁ = f x by unfold f; split_ifs; rfl]
  conv_lhs => enter [2, x, 3, hj₂, 3, hj₁, 2, hj₀]; rw [hj₀, ←hAjjj, show A i j₀ - A i j₁ = f x by unfold f; split_ifs; rfl]
  simp_rw [dite_eq_ite, ←Finset.mem_singleton, ←ite_or, ←Finset.mem_union, ←Finset.insert_eq]
  rw [Finset.univ.sum_ite_mem _ f, Finset.univ_inter, Finset.sum_insert (by simp [hj₂, hj₁]),
    Finset.sum_insert (hj₀.elim <| Finset.mem_singleton.→ ·), Finset.sum_singleton, Finset.mem_singleton]
  simp [f, hj₀.symm, hj₁.symm, hj₂.symm]

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
