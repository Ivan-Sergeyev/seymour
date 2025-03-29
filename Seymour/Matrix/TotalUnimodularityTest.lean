import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.Data.Fintype.Card
import Seymour.Basic.Basic
import Seymour.Basic.SignTypeCast


/-- Formally verified algorithm for testing total unimodularity. -/
def Matrix.testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ k : ℕ, k ≤ min m n → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ SignType.cast.range


lemma Matrix.isTotallyUnimodular_of_aux_le {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ}
    (hA : ∀ k : ℕ, k ≤ m → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ SignType.cast.range) :
    A.IsTotallyUnimodular := by
  intro k f g hf _
  have hkm : k ≤ m
  · simpa using Fintype.card_le_of_injective f hf
  exact hA k hkm f g

lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular → A.IsTotallyUnimodular := by
  intro hA
  if hmn : m ≤ n then
    have hm : min m n = m := Nat.min_eq_left hmn
    apply A.isTotallyUnimodular_of_aux_le
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    convert hA
    exact hm.symm
  else
    push_neg at hmn
    have hn : min m n = n := Nat.min_eq_right hmn.le
    rw [←Matrix.transpose_isTotallyUnimodular_iff]
    apply A.transpose.isTotallyUnimodular_of_aux_le
    intro k hk f g
    simp only [Matrix.testTotallyUnimodular, decide_eq_true_eq, eq_iff_iff, iff_true] at hA
    rw [←Matrix.det_transpose]
    exact hA k (hk.trans_eq hn.symm) g f

theorem Matrix.testTotallyUnimodular_eq_isTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor
  · exact A.isTotallyUnimodular_of_testTotallyUnimodular
  intro hA
  rw [Matrix.isTotallyUnimodular_iff] at hA
  simp only [Matrix.testTotallyUnimodular, and_imp, decide_eq_true_eq, eq_iff_iff, iff_true]
  intro k _ f g
  exact hA k f g

instance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Decidable A.IsTotallyUnimodular :=
  decidable_of_iff _ A.testTotallyUnimodular_eq_isTotallyUnimodular

abbrev Matrix.square_set_submatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
      (r : Finset (Fin m)) (c : Finset (Fin n)) (h : #r = #c) :=
  @Matrix.submatrix (Fin (#r)) _ _ (Fin (#r)) ℚ A ((r.sort (· ≤ ·))[·]) (fun p ↦ (c.sort (· ≤ ·))[p]'(by
      rw [Finset.length_sort, show c.card = r.card by simp_all only [Fintype.card_coe]]
      calc
        p.val < #{ x // x ∈ r } := Fin.isLt p
        _ = r.card := by simp_all only [Fintype.card_coe]
      ))

/-- Faster algorithm for testing total unimodularity but without formal guarantees. -/
def Matrix.testTotallyUnimodularFaster {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  (∀ k : ℕ, k < min m n → ∀ x : Fin k → Fin m, ∀ y : Fin k → Fin n, (A.submatrix x y).det ∈ SignType.cast.range) ∧ (
    if hmn : m = n
      then (A.submatrix id (finCongr hmn)).det ∈ SignType.cast.range
    else if m < n
      then (∀ y : Fin m → Fin n, (A.submatrix id y).det ∈ SignType.cast.range)
      else (∀ x : Fin n → Fin m, (A.submatrix x id).det ∈ SignType.cast.range)
  )

/-- Faster algorithm for testing total unimodularity without permutation with pending formal guarantees. -/
def Matrix.testTotallyUnimodularFastest {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ (r : Finset (Fin m)) (c : Finset (Fin n)) (h : #r = #c),
    (A.square_set_submatrix r c h).det ∈ SignType.cast.range

-- Lemmas that should all be upstreamed to mathlib
lemma Matrix.det_reindex_self_self {m n : Type} [DecidableEq n] [Fintype n]
      [DecidableEq m] [Fintype m]
      {R : Type} [LinearOrderedCommRing R] (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    |((reindex e₁ e₂) A).det| = |A.det| :=
  Matrix.abs_det_submatrix_equiv_equiv e₁.symm e₂.symm A

lemma Set.range_eq_range_iff_exists_comp_equiv {α β γ : Type}
      {f : α → γ} {g : β → γ} (hf : f.Injective) (hg : g.Injective) :
    Set.range f = Set.range g ↔ ∃ (h : α ≃ β), f = g ∘ h := by
  constructor
  · classical
    intro hfg
    let j := fun (a : α) =>
      have : ∃ (b : β), g b = f a := by
        simp_rw [range, Set.ext_iff] at hfg
        have := (hfg (f a)).→ (by simp)
        exact this
      this.choose
    have hji : j.Injective := by sorry
    have hjs : j.Surjective := by sorry
    use Equiv.ofBijective j ⟨hji, hjs⟩
    simp only [Function.comp_def, funext_iff, Equiv.ofBijective_apply]
    unfold j
    intro x
    simp only
    sorry
  · intro ⟨e, he⟩
    simp_rw [range]
    ext x
    subst he
    simp_all only [Function.Injective.of_comp_iff, Function.comp_apply, mem_setOf_eq]
    constructor <;> intro ⟨w, h⟩ <;> subst h
    · simp_all only [exists_apply_eq_apply]
    · use e.symm w
      simp

lemma Matrix.submatrix_eq_submatrix_reindex {r c n o p q : Type}
      [DecidableEq r] [Fintype r] [DecidableEq c] [Fintype c] [DecidableEq n] [Fintype n]
      [DecidableEq o] [Fintype o] [DecidableEq p] [Fintype p] [DecidableEq q] [Fintype q]
      {R : Type} [CommRing R]
      {nr : n → r} {oc : o → c} {pr : p → r} {qc : q → c}
      (hnr : nr.Injective) (hoc : oc.Injective) (hpr : pr.Injective) (hqc : qc.Injective)
      (hnpr : nr.range = pr.range) (hoqc : oc.range = qc.range)
      (A : Matrix r c R) :
    ∃ e₁ e₂, (A.submatrix nr oc) = (A.submatrix pr qc).reindex e₁ e₂ := by
  have ⟨e₁, he₁⟩ : ∃ (e : n ≃ p), nr = pr ∘ e := (Set.range_eq_range_iff_exists_comp_equiv hnr hpr).→ (by tauto_set)
  have ⟨e₂, he₂⟩ : ∃ (e : o ≃ q), oc = qc ∘ e := (Set.range_eq_range_iff_exists_comp_equiv hoc hqc).→ (by tauto_set)
  refine ⟨e₁.symm, e₂.symm, ?_⟩
  subst he₁ he₂
  simp

lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodularFastest {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodularFastest → A.IsTotallyUnimodular := by
  rw [testTotallyUnimodularFastest]
  intro a k f g hf hg
  simp_all only [Fintype.card_coe, Function.range, Fin.getElem_fin,
    decide_eq_true_eq]
  simp_rw [(in_signTypeCastRange_iff_abs (A.submatrix f g).det)]
  have hfg : f.range.toFinset.card = g.range.toFinset.card := (by
    simp_rw [Function.range, Set.toFinset_card, Set.card_range_of_injective hf, Set.card_range_of_injective hg])
  obtain ⟨e₁, e₂, hee⟩ := @Matrix.submatrix_eq_submatrix_reindex
    (Fin m) (Fin n) (Fin (#{ x // x ∈ f.range.toFinset })) (Fin (#{ x // x ∈ f.range.toFinset })) (Fin k) (Fin k)
    _ _ _ _ _ _  _ _ _ _ _ _ ℚ _
    (fun x => (Finset.sort (fun x1 x2 => x1 ≤ x2) f.range.toFinset)[x]'(by
      rw [Finset.length_sort]
      calc
        x.val < #{ x // x ∈ f.range.toFinset } := Fin.isLt x
        _ = _ := by simp_all only [Fintype.card_coe]
      ))
    (fun p => (Finset.sort (fun x1 x2 => x1 ≤ x2) g.range.toFinset)[p]'(by
      rw [Finset.length_sort, show g.range.toFinset.card = f.range.toFinset.card by simp_all only [Fintype.card_coe]]
      calc
        p.val < #{ x // x ∈ f.range.toFinset } := Fin.isLt p
        _ = _ := by simp_all only [Fintype.card_coe])) f g
    (by
      sorry)
    (by
      sorry)
    hf hg
    (by
      simp only [Function.range, Set.toFinset_range, Fin.getElem_fin, ←Finset.univ_filter_mem_range]
      ext x
      sorry)
    (by
      simp only [Function.range, Set.toFinset_range, Fin.getElem_fin, ←Finset.univ_filter_mem_range]
      ext x
      sorry)
    A
  have := a f.range.toFinset g.range.toFinset hfg
  rw [square_set_submatrix, hee, in_signTypeCastRange_iff_abs (((reindex e₁ e₂) (A.submatrix f g))).det] at this
  rw [←Matrix.det_reindex_self_self e₁ e₂ (A.submatrix f g)]
  exact this
