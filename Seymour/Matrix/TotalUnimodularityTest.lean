import Mathlib.Data.Fintype.Card
import Seymour.Basic.Basic
import Seymour.Basic.SignTypeCast
import Seymour.Matrix.TotalUnimodularity

/-!
# Total Unimodularity Test

This file provides means to (computably) test total unimodularity of small matrices.
-/

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

lemma Matrix.testTotallyUnimodular_eq_isTotallyUnimodular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor
  · exact A.isTotallyUnimodular_of_testTotallyUnimodular
  intro hA
  simp only [Matrix.testTotallyUnimodular, and_imp, decide_eq_true_eq, eq_iff_iff, iff_true]
  intro _ _ f g
  exact hA.det f g

instance {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Decidable A.IsTotallyUnimodular :=
  decidable_of_iff _ A.testTotallyUnimodular_eq_isTotallyUnimodular

lemma filter_length_card {n : ℕ} {s : Finset (Fin n)} : ((List.finRange n).filter (· ∈ s)).length = s.card := by
  have := ((List.finRange n).filter (· ∈ s)).toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))
  simp_all

def Matrix.squareSetSubmatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    {X : Finset (Fin m)} {Y : Finset (Fin n)} (hXY : X.card = Y.card) :
    Matrix (Fin X.card) (Fin X.card) ℚ :=
  A.submatrix
    (fun p : Fin X.card => ((List.finRange m).filter (· ∈ X))[p]'(by convert p.isLt; exact filter_length_card))
    (fun p : Fin X.card => ((List.finRange n).filter (· ∈ Y))[p]'(by convert p.isLt; exact hXY ▸ filter_length_card))

/-- Faster algorithm for testing total unimodularity without permutation with pending formal guarantees. -/
def Matrix.testTotallyUnimodularFast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Bool :=
  ∀ (X : Finset (Fin m)) (Y : Finset (Fin n)) (hXY : X.card = Y.card),
    (A.squareSetSubmatrix hXY).det ∈ SignType.cast.range

lemma Matrix.abs_det_reindex_self_self {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
    {R : Type*} [LinearOrderedCommRing R] (A : Matrix m m R) (e₁ e₂ : m ≃ n) :
    |(A.reindex e₁ e₂).det| = |A.det| :=
  A.abs_det_submatrix_equiv_equiv e₁.symm e₂.symm

lemma range_eq_range_iff_exists_comp_equiv {α β γ : Type*} {f : α → γ} {g : β → γ} (hf : f.Injective) (hg : g.Injective) :
    f.range = g.range ↔ ∃ e : α ≃ β, f = g ∘ e := by
  constructor
  · classical
    intro hfg
    have hf' := fun (a : α) =>
      show ∃ (b : β), g b = f a by
      simp_rw [Set.range, Set.ext_iff] at hfg
      exact (hfg (f a)).→ (by simp)
    have hg' := fun (b : β) =>
      show ∃ (a : α), f a = g b by
      simp_rw [Set.range, Set.ext_iff] at hfg
      exact (hfg (g b)).← (by simp)
    use Equiv.ofBijective (fun a => (hf' a).choose) ⟨fun a₁ a₂ haa =>
      by
        simp only at haa
        have ha₁ := (hf' a₁).choose_spec
        rw [haa] at ha₁
        have ha₂ := (hf' a₂).choose_spec
        rw [ha₁] at ha₂
        exact hf ha₂,
      by
        rw [Function.surjective_iff_hasRightInverse]
        use (fun b => (hg' b).choose)
        intro b
        have hgf := (hf' ((fun b => (hg' b).choose) b)).choose_spec
        simp only [(hg' b).choose_spec] at hgf ⊢
        apply hg
        exact hgf⟩
    simp only [Function.comp_def, Equiv.ofBijective_apply]
    ext a
    exact (hf' a).choose_spec.symm
  · rintro ⟨e, rfl⟩
    simp_rw [Set.range]
    ext
    simp_all only [Function.comp_apply, Set.mem_setOf_eq]
    constructor
    <;> rintro ⟨w, rfl⟩
    · exact exists_apply_eq_apply g (e w)
    · use e.symm w
      rw [Equiv.apply_symm_apply]

lemma range_of_list_get {α : Type*} [DecidableEq α] {n : ℕ} {s : List α} (hn : n = s.length) :
    (fun x : Fin n => s[x]).range = s.toFinset := by
  ext a
  simp_rw [Function.range, Fin.getElem_fin, List.coe_toFinset, Set.mem_range, Set.mem_setOf_eq]
  constructor
  <;> intro ha
  · obtain ⟨_, rfl⟩ := ha
    simp_rw [List.getElem_mem]
  · have ⟨i, hi, _⟩ := List.getElem_of_mem ha
    use ⟨i, hn ▸ hi⟩

lemma Matrix.submatrix_eq_submatrix_reindex {r c n o p q α : Type*}
    [DecidableEq r] [Fintype r] [DecidableEq c] [Fintype c] [DecidableEq n] [Fintype n]
    [DecidableEq o] [Fintype o] [DecidableEq p] [Fintype p] [DecidableEq q] [Fintype q]
    {f₁ : n → r} {g₁ : o → c} {f₂ : p → r} {g₂ : q → c}
    (A : Matrix r c α) (hf₁ : f₁.Injective) (hg₁ : g₁.Injective) (hf₂ : f₂.Injective) (hg₂ : g₂.Injective)
    (hff : f₁.range = f₂.range) (hgg : g₁.range = g₂.range) :
    ∃ e₁ : p ≃ n, ∃ e₂ : q ≃ o, (A.submatrix f₁ g₁) = (A.submatrix f₂ g₂).reindex e₁ e₂ := by
  obtain ⟨e₁, rfl⟩ := (range_eq_range_iff_exists_comp_equiv hf₁ hf₂).→ hff
  obtain ⟨e₂, rfl⟩ := (range_eq_range_iff_exists_comp_equiv hg₁ hg₂).→ hgg
  exact ⟨e₁.symm, e₂.symm, by simp⟩

/-- A fast version of `Matrix.testTotallyUnimodular` which doesn't test every permutation. -/
lemma Matrix.isTotallyUnimodular_of_testTotallyUnimodularFast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.testTotallyUnimodularFast → A.IsTotallyUnimodular := by
  rw [Matrix.testTotallyUnimodularFast]
  intro hA k f g hf hg
  simp_all only [Fintype.card_coe, Fin.getElem_fin, decide_eq_true_eq]
  simp_rw [(in_signTypeCastRange_iff_abs (A.submatrix f g).det)]
  have hfg : f.range.toFinset.card = g.range.toFinset.card
  · simp_rw [Set.toFinset_card, Set.card_range_of_injective hf, Set.card_range_of_injective hg]
  obtain ⟨e₁, e₂, hee⟩ := @A.submatrix_eq_submatrix_reindex
    _ _ (Fin f.range.toFinset.card) (Fin f.range.toFinset.card) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun p => ((List.finRange m).filter (· ∈ f.range.toFinset))[p]'(by convert p.isLt; exact filter_length_card))
    (fun p => ((List.finRange n).filter (· ∈ g.range.toFinset))[p]'(by convert p.isLt; rw [hfg]; exact filter_length_card))
    f g
    (fun a₁ a₂ haa => by simpa [Fin.mk.injEq, Fin.val_inj] using
        (List.nodup_iff_injective_get.→ ((List.nodup_finRange m).filter _) haa))
    (fun a₁ a₂ haa => by simpa [Fin.mk.injEq, Fin.val_inj] using
        (List.nodup_iff_injective_get.→ ((List.nodup_finRange n).filter _) haa))
    hf hg
    (by
      rw [range_of_list_get filter_length_card.symm]
      simp
    )
    (by
      rw [range_of_list_get (by rw [hfg]; exact filter_length_card.symm)]
      simp
    )
  have hAfg := hA f.range.toFinset g.range.toFinset hfg
  rw [Matrix.squareSetSubmatrix, hee, in_signTypeCastRange_iff_abs ((A.submatrix f g).reindex e₁ e₂).det] at hAfg
  rw [←(A.submatrix f g).abs_det_reindex_self_self e₁ e₂]
  exact hAfg
