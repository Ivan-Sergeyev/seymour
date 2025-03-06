import Seymour.Matrix.Basic


variable {X Y R : Type} [CommRing R]

/-- A matrix is minimal TU violating if it is not TU, but its every proper submatrix is TU. -/
def Matrix.IsMinimalNonTU (A : Matrix X Y R) : Prop :=
  ¬A.IsTotallyUnimodular ∧
  ∀ k : ℕ, ∀ f : Fin k → X, ∀ g : Fin k → Y, (¬f.Surjective ∨ ¬g.Surjective) → (A.submatrix f g).IsTotallyUnimodular

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
    (hA : A.IsMinimalNonTU) (h2 : #X = 2) :
    ∀ i : X, ∀ j : Y, A i j = -1 ∨ A i j = 1 := by
  have trichotomy (i : X) (j : Y) : A i j = 0 ∨ A i j = -1 ∨ A i j = 1
  · obtain ⟨s, hs⟩ :=
      (hA.right 1 ![i] ![j] (by
        left
        intro contr
        have impos := h2 ▸ Fintype.card_fin 1 ▸ Fintype.card_le_of_surjective _ contr
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
  intro
  by_contra contr
  rw [Matrix.submatrix_submatrix, Matrix.isTotallyUnimodular_iff] at contr
  sorry

lemma Matrix.containsMinimalNonTU_iff_not_isTotallyUnimodular (A : Matrix X Y R) :
    (∃ k : ℕ, A.ContainsMinimalNonTU k) ↔ ¬A.IsTotallyUnimodular := by
  constructor
  · sorry
  · exact A.containsMinimalNonTU_of_not_isTotallyUnimodular

lemma Matrix.isTotallyUnimodular_iff_not_containsMinimalNonTU (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ¬(∃ k : ℕ, A.ContainsMinimalNonTU k) :=
  iff_not_comm.→ A.containsMinimalNonTU_iff_not_isTotallyUnimodular

lemma Matrix.isTotallyUnimodular_iff_none_containsMinimalNonTU (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k : ℕ, ¬(A.ContainsMinimalNonTU k) :=
  A.isTotallyUnimodular_iff_not_containsMinimalNonTU.trans not_exists

/-- Pivoting in a minimal TU violating matrix and removing the pivot row and col yields a minimal TU violating matrix. -/
lemma Matrix.IsMinimalNonTU_after_pivot {A : Matrix X Y R} {x : X} {y : Y}
    (hA : A.IsMinimalNonTU) (hX : Fintype X) (hY : Fintype Y) (hXY : hX.card ≥ 2) (hxy : A x y ≠ 0) :
    False := -- fixme: pivot on A x y + delete pivot row & col => MVM
  sorry

-- Let's do the same but better...

/-- The smallest submatrix of `A` that is not totally unimodular has size `k` (propositionally equal to what is written). -/
def Matrix.MinimumViolationSizeIs (A : Matrix X Y R) (k : ℕ) : Prop :=
  (∀ n : ℕ, ∀ f : Fin n → X, ∀ g : Fin n → Y, n < k → f.Injective → g.Injective →
    (A.submatrix f g).det ∈ SignType.cast.range) ∧
  ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)

lemma Matrix.minimumViolationSizeIs_iff (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)) := by
  -- if not injective then `∈ SignType.cast.range` is tautological
  sorry

lemma Matrix.minimumViolationSizeIs_iff' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ∃ f : Fin k → X, ∃ g : Fin k → Y, f.Injective ∧ g.Injective ∧ (A.submatrix f g).det ∉ SignType.cast.range) := by
  simp [Matrix.minimumViolationSizeIs_iff]

lemma Matrix.minimumViolationSizeIs_iff'' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ∃ f : Fin k → X, ∃ g : Fin k → Y, (A.submatrix f g).det ∉ SignType.cast.range) := by
  -- `∉ SignType.cast.range` itself implies `f.Injective` and `g.Injective`
  sorry

lemma Matrix.isTotallyUnimodular_iff_none_minimumViolationSizeIs (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k : ℕ, ¬(A.MinimumViolationSizeIs k) := by
  sorry
