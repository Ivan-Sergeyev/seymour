import Seymour.Matrix.Basic


variable {X Y R : Type} [CommRing R]

/-- The smallest submatrix of `A` that is not totally unimodular has size `k` (propositionally equal to what is written). -/
def Matrix.MinimumViolationSizeIs (A : Matrix X Y R) (k : ℕ) : Prop :=
  (∀ n : ℕ, ∀ f : Fin n → X, ∀ g : Fin n → Y, n < k → f.Injective → g.Injective →
    (A.submatrix f g).det ∈ SignType.cast.range) ∧
  ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)

lemma Matrix.submatrix_det_zero_of_not_injective_snd {Z : Type} [Fintype Z] [DecidableEq Z] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hg : ¬g.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [Function.not_injective_iff] at hg
  obtain ⟨i, j, hgij, hij⟩ := hg
  apply Matrix.det_zero_of_column_eq hij
  simp [hgij]

lemma Matrix.submatrix_det_zero_of_not_injective_fst {Z : Type} [Fintype Z] [DecidableEq Z] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hf : ¬f.Injective) :
    (A.submatrix f g).det = 0 := by
  rw [←Matrix.det_transpose, Matrix.transpose_submatrix]
  exact A.transpose.submatrix_det_zero_of_not_injective_snd hf

lemma Matrix.submatrix_det_zero_of_not_injective {Z : Type} [Fintype Z] [DecidableEq Z] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hfg : ¬(f.Injective ∧ g.Injective)) :
    (A.submatrix f g).det = 0 := by
  rw [not_and_or] at hfg
  cases hfg with
  | inl hf => exact A.submatrix_det_zero_of_not_injective_fst hf
  | inr hg => exact A.submatrix_det_zero_of_not_injective_snd hg

lemma Matrix.submatrix_det_in_singTypeCastRange_of_not_injective {Z : Type} [Fintype Z] [DecidableEq Z] {f : Z → X} {g : Z → Y}
    (A : Matrix X Y R) (hfg : ¬(f.Injective ∧ g.Injective)) :
    (A.submatrix f g).det ∈ SignType.cast.range :=
  ⟨SignType.zero, (A.submatrix_det_zero_of_not_injective hfg).symm⟩

lemma Matrix.minimumViolationSizeIs_iff (A : Matrix X Y R) (k : ℕ) :
    A.MinimumViolationSizeIs k ↔
    ((∀ n < k, ∀ f : Fin n → X, ∀ g : Fin n → Y, (A.submatrix f g).det ∈ SignType.cast.range) ∧
    ¬(∀ f : Fin k → X, ∀ g : Fin k → Y, f.Injective → g.Injective → (A.submatrix f g).det ∈ SignType.cast.range)) := by
  apply and_congr_l
  constructor
  · intro hA n hn f g
    if hfg : f.Injective ∧ g.Injective then
      obtain ⟨hf, hg⟩ := hfg
      exact hA n f g hn hf hg
    else
      exact A.submatrix_det_in_singTypeCastRange_of_not_injective hfg
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
      ∃ f : Fin k → X, ∃ g : Fin k → Y, (A.submatrix f g).det ∉ SignType.cast.range) := by
  rw [A.minimumViolationSizeIs_iff']
  apply and_congr_r
  constructor
  · intro ⟨f, g, hf, hg, hA⟩
    exact ⟨f, g, hA⟩
  · intro ⟨f, g, hA⟩
    if hfg : f.Injective ∧ g.Injective then
      obtain ⟨hf, hg⟩ := hfg
      exact ⟨f, g, hf, hg, hA⟩
    else
      exfalso
      exact hA (A.submatrix_det_in_singTypeCastRange_of_not_injective hfg)

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
