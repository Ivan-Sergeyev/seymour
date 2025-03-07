import Seymour.Matrix.Basic


variable {X Y R : Type} [CommRing R]

/-- The smallest submatrix of `A` that is not totally unimodular has size `k` (propositionally equal to what is written). -/
def Matrix.MinimumViolationSizeIs (A : Matrix X Y R) (k : ℕ) : Prop :=
  (∀ n : ℕ, ∀ f : Fin n → X, ∀ g : Fin n → Y, n < k → f.Injective → g.Injective →
    (A.submatrix f g).det ∈ SignType.cast.range) ∧
  ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)

lemma ll {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : P₁ ∧ Q ↔ P₂ ∧ Q :=
  and_congr_left (fun _ => hP)

lemma lll {P₁ P₂ : Prop} (hP : P₁ ↔ P₂) (Q : Prop) : Q ∧ P₁ ↔ Q ∧ P₂ :=
  and_congr_right (fun _ => hP)

lemma Matrix.minimumViolationSizeIs_iff (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)) := by
  apply ll
  constructor
  · intro hA n hn f g
    if hfg : f.Injective ∧ g.Injective then
      obtain ⟨hf, hg⟩ := hfg
      exact hA n f g hn hf hg
    else
      use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← Matrix.det_transpose, Matrix.transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro hA n f g hn hf hg
    exact hA n hn f g

lemma Matrix.minimumViolationSizeIs_iff' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
      ∃ f : Fin k → X, ∃ g : Fin k → Y, f.Injective ∧ g.Injective ∧ (A.submatrix f g).det ∉ SignType.cast.range) := by
  simp [Matrix.minimumViolationSizeIs_iff]

lemma Matrix.minimumViolationSizeIs_iff'' (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
      ∃ f : Fin k → X, ∃ g : Fin k → Y, (A.submatrix f g).det ∉ SignType.cast.range) :=
  (A.minimumViolationSizeIs_iff' k).trans <| by
  apply lll
  constructor
  · intro ⟨f, g, hf, hg, hA⟩
    exact ⟨f, g, hA⟩
  · intro ⟨f, g, hA⟩
    if hfg : f.Injective ∧ g.Injective then
      obtain ⟨hf, hg⟩ := hfg
      exact ⟨f, g, hf, hg, hA⟩
    else
      exfalso
      apply hA
      use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← Matrix.det_transpose, Matrix.transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]

private lemma Matrix.isTotallyUnimodular_of_none_minimumViolationSizeIs_aux (A : Matrix X Y R) (n : ℕ) :
    (∀ m ≤ n, ¬(A.MinimumViolationSizeIs m)) →
      (∀ m ≤ n, ∀ f : Fin m → X, ∀ g : Fin m → Y,
        f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range) := by
  induction n with
  | zero =>
    intro _ m hm
    rw [Nat.eq_zero_of_le_zero hm]
    intro _ _ _ _
    use SignType.pos
    simp
  | succ n ih =>
    intro hAn m hm
    if hmn : m ≤ n then
      exact ih (fun k hk => hAn k (k.le_succ_of_le hk)) m hmn
    else
      have m_eq : m = n.succ
      · omega
      clear hmn
      have hAn' := hAn n.succ (by rfl)
      erw [not_and] at hAn'
      specialize hAn' (fun k f g hk => ih (fun z hz => hAn z (z.le_succ_of_le hz)) k (k.le_of_lt_succ hk) f g)
      rw [not_not] at hAn'
      subst m_eq
      apply hAn'

lemma Matrix.isTotallyUnimodular_iff_none_minimumViolationSizeIs (A : Matrix X Y R) :
    A.IsTotallyUnimodular ↔ ∀ k : ℕ, ¬(A.MinimumViolationSizeIs k) := by
  constructor
  · intro hA k
    erw [not_and]
    intro _
    rw [not_not]
    apply hA
  · intro hA k f g hf hg
    apply A.isTotallyUnimodular_of_none_minimumViolationSizeIs_aux k
    · intro m hm
      apply hA
    · rfl
    · exact hf
    · exact hg
