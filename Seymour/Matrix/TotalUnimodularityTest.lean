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
    rw [Finset.length_sort, show c.card = r.card by simp_all only [Fintype.card_coe], ←Fintype.card_coe r]
    exact Fin.isLt p))

/-- Faster algorithm for testing total unimodularity without permutation with pending formal guarantees. -/
def Matrix.testTotallyUnimodularFast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ (r : Finset (Fin m)) (c : Finset (Fin n)) (h : #r = #c),
    (A.square_set_submatrix r c h).det ∈ SignType.cast.range

-- Lemmas that should all be upstreamed to mathlib
-- https://github.com/leanprover-community/mathlib4/pull/23421/files
lemma Matrix.abs_det_reindex_self_self {m n : Type} [DecidableEq n] [Fintype n]
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
        exact (hfg (f a)).→ (by simp)
      this
    let rj := fun (b : β) =>
      have : ∃ (a : α), f a = g b := by
        simp_rw [range, Set.ext_iff] at hfg
        exact (hfg (g b)).← (by simp)
      this
    use Equiv.ofBijective (fun a => (j a).choose) ⟨fun a₁ a₂ haa =>
      by
        simp only at haa
        have ha₁ := (j a₁).choose_spec
        rw [haa] at ha₁
        have ha₂ := (j a₂).choose_spec
        rw [ha₁] at ha₂
        exact hf ha₂,
      by
        rw [Function.surjective_iff_hasRightInverse]
        use (fun b => (rj b).choose)
        intro b
        have := (j ((fun b => (rj b).choose) b)).choose_spec
        simp only [(rj b).choose_spec] at this ⊢
        apply hg
        exact this⟩
    simp only [Function.comp_def, Equiv.ofBijective_apply]
    ext x
    exact (j x).choose_spec.symm
  · rintro ⟨e, rfl⟩
    simp_rw [range]
    ext x
    simp_all only [Function.comp_apply, mem_setOf_eq]
    constructor <;> rintro ⟨w, rfl⟩
    · exact exists_apply_eq_apply g (e w)
    · use e.symm w
      rw [Equiv.apply_symm_apply]

lemma Set.range_of_list_get {α : Type} [DecidableEq α] {n : ℕ} {s : List α} (hn : n = s.length) :
    (fun x : Fin n => s[x]).range = s.toFinset := by
  ext x
  simp_rw [Function.range, Fin.getElem_fin, List.coe_toFinset, mem_range, mem_setOf_eq]
  constructor <;> intro h
  · obtain ⟨w, rfl⟩ := h
    simp_rw [List.getElem_mem]
  · have ⟨i, hi, hii⟩ := List.getElem_of_mem h
    use (Fin.mk i (by rw [hn]; exact hi))

lemma Matrix.submatrix_eq_submatrix_reindex {r c n o p q : Type}
      [DecidableEq r] [Fintype r] [DecidableEq c] [Fintype c] [DecidableEq n] [Fintype n]
      [DecidableEq o] [Fintype o] [DecidableEq p] [Fintype p] [DecidableEq q] [Fintype q]
      {R : Type} [CommRing R]
      {nr : n → r} {oc : o → c} {pr : p → r} {qc : q → c}
      (hnr : nr.Injective) (hoc : oc.Injective) (hpr : pr.Injective) (hqc : qc.Injective)
      (hnpr : nr.range = pr.range) (hoqc : oc.range = qc.range)
      (A : Matrix r c R) :
    ∃ e₁ e₂, (A.submatrix nr oc) = (A.submatrix pr qc).reindex e₁ e₂ := by
  obtain ⟨e₁, rfl⟩ := (Set.range_eq_range_iff_exists_comp_equiv hnr hpr).→ hnpr
  obtain ⟨e₂, rfl⟩ := (Set.range_eq_range_iff_exists_comp_equiv hoc hqc).→ hoqc
  refine ⟨e₁.symm, e₂.symm, ?_⟩
  simp

/-- A fast version of `Matrix.testTotallyUnimodular` which doesn't test every permutation. -/
lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodularFast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodularFast → A.IsTotallyUnimodular := by
  rw [testTotallyUnimodularFast]
  intro a k f g hf hg
  simp_all only [Fintype.card_coe, Function.range, Fin.getElem_fin,
    decide_eq_true_eq]
  simp_rw [(in_signTypeCastRange_iff_abs (A.submatrix f g).det)]
  have hfg : f.range.toFinset.card = g.range.toFinset.card := (by
    simp_rw [Function.range, Set.toFinset_card, Set.card_range_of_injective hf, Set.card_range_of_injective hg])
  obtain ⟨e₁, e₂, hee⟩ := @Matrix.submatrix_eq_submatrix_reindex
    _ _ (Fin (#{ x // x ∈ f.range.toFinset })) (Fin (#{ x // x ∈ f.range.toFinset })) _ _
    _ _ _ _ _ _  _ _ _ _ _ _ _ _
    (fun x => (f.range.toFinset.sort (· ≤ ·))[x]'(by
      rw [Finset.length_sort, ←Fintype.card_coe f.range.toFinset]
      exact Fin.isLt x
    ))
    (fun p => (g.range.toFinset.sort (· ≤ ·))[p]'(by
      rw [Finset.length_sort, show g.range.toFinset.card = f.range.toFinset.card by simp_all only [Fintype.card_coe],
        ←Fintype.card_coe f.range.toFinset]
      exact Fin.isLt p
    ))
    f g
    (by
      intro a₁ a₂ haa
      have := (List.nodup_iff_injective_get.→ <| Finset.sort_nodup (· ≤ ·) f.range.toFinset) haa
      simp_rw [Fin.mk.injEq, Fin.val_inj] at this
      exact this)
    (by
      intro a₁ a₂ haa
      have := (List.nodup_iff_injective_get.→ <| Finset.sort_nodup (· ≤ ·) g.range.toFinset) haa
      simp_rw [Fin.mk.injEq, Fin.val_inj] at this
      exact this)
    hf hg
    (by
      rw [Set.range_of_list_get (by rw [Finset.length_sort, Fintype.card_coe])]
      simp
    )
    (by
      rw [Set.range_of_list_get (by rw [Finset.length_sort, Fintype.card_coe]; exact hfg)]
      simp
    )
    A
  have := a f.range.toFinset g.range.toFinset hfg
  rw [square_set_submatrix, hee, in_signTypeCastRange_iff_abs (((reindex e₁ e₂) (A.submatrix f g))).det] at this
  rw [←Matrix.abs_det_reindex_self_self e₁ e₂ (A.submatrix f g)]
  exact this
