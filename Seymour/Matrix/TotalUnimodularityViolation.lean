import Seymour.Matrix.Pivoting


variable {X Y : Type}

section
variable {R : Type} [CommRing R]

/-- A matrix is minimal TU violating if it is not TU, but its every proper submatrix is TU. -/
def Matrix.IsMinimalNonTU (A : Matrix X Y R) : Prop :=
  ¬A.IsTotallyUnimodular ∧
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, (¬f.Surjective ∨ ¬g.Surjective) → (A.submatrix f g).IsTotallyUnimodular

/-- The order of a minimal TU violating matrix is the number of its rows. -/
def Matrix.IsMinimalNonTU.order [Fintype X] [Fintype Y] {A : Matrix X Y R} (_hA : A.IsMinimalNonTU) :=
  #X -- Why is this definition useful?

def Matrix.ContainsMinimalNonTU (A : Matrix X Y R) (k : ℕ) : Prop :=
  ∃ f : Fin k → X, ∃ g : Fin k → Y, f.Bijective ∧ g.Bijective ∧ (A.submatrix f g).IsMinimalNonTU

/-- A minimal TU violating matrix is square. -/
lemma Matrix.IsMinimalNonTU_is_square [Fintype X] [Fintype Y] {A : Matrix X Y R} (hA : A.IsMinimalNonTU) :
    #X = #Y := by
  obtain ⟨hAnot, hAyes⟩ := hA
  rw [Matrix.IsTotallyUnimodular] at hAnot
  push_neg at hAnot
  obtain ⟨k, f, g, inj_f, inj_g, hAfg⟩ := hAnot
  specialize hAyes k f g
  by_contra hXY
  apply hAfg
  rw [Matrix.isTotallyUnimodular_iff] at hAyes
  apply hAyes
  rw [← Mathlib.Tactic.PushNeg.not_and_or_eq]
  intro ⟨surj_f, surj_g⟩
  apply hXY
  trans # Fin k
  · symm
    exact Fintype.card_of_bijective ⟨inj_f, surj_f⟩
  · exact Fintype.card_of_bijective ⟨inj_g, surj_g⟩

/-- A 2 × 2 minimal TU violating matrix has four ±1 entries. -/
lemma Matrix.IsMinimalNonTU.two_by_two_entries [Fintype X] [Fintype Y] {A : Matrix X Y R}
    (hA : A.IsMinimalNonTU) (h2 : hA.order = 2) :
    ∀ i : X, ∀ j : Y, A i j = -1 ∨ A i j = 1 := by
  have hX2 : #X = 2 := h2
  have trichotomy (i : X) (j : Y) : A i j = 0 ∨ A i j = -1 ∨ A i j = 1
  · obtain ⟨s, hs⟩ :=
      (hA.right 1 ![i] ![j] (by
        left
        intro contr
        have impos := hX2 ▸ Fintype.card_fin 1 ▸ Fintype.card_le_of_surjective _ contr
        norm_num at impos)
      ).apply 0 0
    cases s with
    | zero =>
      left
      exact hs.symm
    | neg =>
      right
      left
      exact hs.symm
    | pos =>
      right
      right
      exact hs.symm
  intro i j
  cases trichotomy i j with
  | inl h0 =>
    exfalso
    apply hA.left
    intro k f g hf hg
    if k_eq_0 : k = 0 then
      sorry -- empty matrix has determinant `1`
    else if k_eq_1 : k = 1 then
      sorry -- directly from `trichotomy`
    else if k_eq_2 : k = 2 then
      sorry -- laplace at `A i j` and plug `h0`
    else
      exfalso
      have : k ≤ #X := Fintype.card_fin k ▸ Fintype.card_le_of_injective f hf
      omega
  | inr h1 =>
    exact h1

/-- Every non-TU matrix contains a minimal TU violating matrix. -/
lemma Matrix.containsMinimalNonTU_of_not_isTotallyUnimodular {A : Matrix X Y R} (hA : ¬A.IsTotallyUnimodular) :
    ∃ k : ℕ, A.ContainsMinimalNonTU k := by
  rw [Matrix.isTotallyUnimodular_iff] at hA
  push_neg at hA
  obtain ⟨k, ⟨f, g, hfg⟩, hAk⟩ := exists_minimal_nat_of_exists hA
  use k, f, g, sorry, sorry
  constructor
  · rw [Matrix.isTotallyUnimodular_iff]
    push_neg
    exact ⟨k, id, id, hfg⟩
  intro n f' g'
  specialize @hAk n
  simp only [not_exists, forall_exists_index] at hAk
  specialize hAk (f ∘ f') (g ∘ g')
  intro huh
  by_contra contr
  rw [Matrix.submatrix_submatrix, Matrix.isTotallyUnimodular_iff] at contr
  sorry

/-- Pivoting in a minimal TU violating matrix and removing the pivot row and col yields a minimal TU violating matrix. -/
lemma Matrix.IsMinimalNonTU_after_pivot {A : Matrix X Y R} {x : X} {y : Y}
    (hA : A.IsMinimalNonTU) (hX : Fintype X) (hY : Fintype Y) (hXY : hX.card ≥ 2) (hxy : A x y ≠ 0) :
    False := -- fixme: pivot on A x y + delete pivot row & col => MVM
  sorry

end

section
variable {F : Type} [Field F]

/-- The form of a matrix after pivoting and removing the pivot row and column. -/
lemma Matrix.shortTableauPivot_no_pivot_row_col [DecidableEq X] [DecidableEq Y]
    (A : Matrix X Y F) (x : X) (y : Y) (i : X) (j : Y) (hix : i ≠ x) (hjx : j ≠ y) :
    A.shortTableauPivot x y i j = A i j - A i y * A x j / A x y := by
  simp [Matrix.shortTableauPivot, hix, hjx]
  -- sketch:
  -- * the resulting matrix has the same determinant as the original one (cofactor computation), hence not TU
  -- * every proper submatrix is TU, because TUness is preserved under pivoting

end
