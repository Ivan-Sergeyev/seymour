import Mathlib.Data.Matroid.Sum
import Seymour.Matroid.Properties.Regularity


-- ## 1-sum of matrices

/-- 1-sum of matrices. -/
abbrev Matrix.oneSum {R Xₗ Yₗ Xᵣ Yᵣ : Type} [Zero R] (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

/-- If matrices have TU signings, then their 1-sum has a TU signing. -/
lemma Matrix.oneSum_hasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Aₗ : Matrix Xₗ Yₗ Z2} {Aᵣ : Matrix Xᵣ Yᵣ Z2} (hAₗ : Aₗ.HasTuSigning) (hAᵣ : Aᵣ.HasTuSigning) :
    (Aₗ.oneSum Aᵣ).HasTuSigning :=
  have ⟨_, hBAₗ, hBₗ⟩ := hAₗ
  have ⟨_, hBAᵣ, hBᵣ⟩ := hAᵣ
  ⟨
    _,
    fun i j => i.casesOn (fun iₗ => j.casesOn (hBAₗ iₗ) ↓abs_zero) (fun iᵣ => j.casesOn ↓abs_zero (hBAᵣ iᵣ)),
    Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ
  ⟩

private lemma Matrix.HasTuSigning.toMatrixUnionUnion {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α} {A : Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) Z2}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hA : A.HasTuSigning) :
    A.toMatrixUnionUnion.HasTuSigning :=
  have ⟨_, hBA, hB⟩ := hA
  ⟨
    _,
    (hBA ·.toSum ·.toSum),
    hB.toMatrixUnionUnion
  ⟩

private abbrev union_comm_equiv {α : Type} (A B : Set α) : (A ∪ B).Elem ≃ (B ∪ A).Elem where
  toFun := fun i => ⟨i.val, i.property.symm⟩
  invFun := fun i => ⟨i.val, i.property.symm⟩
  left_inv := (by intro x; simp only [Subtype.coe_eta])
  right_inv := (by intro x; simp only [Subtype.coe_eta])

/-- 1-sum is commutative (up to reindexing). -/
lemma Matrix.oneSum_comm {α R : Type} [DivisionRing R] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) :
    (Aᵣ.oneSum Aₗ).toMatrixUnionUnion =
    (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.reindex (union_comm_equiv Xₗ Xᵣ) (union_comm_equiv Yₗ Yᵣ) := by
  ext i j
  unfold Matrix.oneSum Matrix.toMatrixUnionUnion Matrix.reindex union_comm_equiv Subtype.toSum
  simp only [Function.comp_apply, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Matrix.submatrix_apply]
  if hiₗ : i.val ∈ Xₗ then
    have hiᵣ : i.val ∉ Xᵣ := Set.disjoint_left.→ hXX hiₗ
    if hjₗ : j.val ∈ Yₗ then
      have hjᵣ : j.val ∉ Yᵣ := Set.disjoint_left.→ hYY hjₗ
      simp [hiₗ, hjₗ, hiᵣ, hjᵣ]
    else if hjᵣ : j.val ∈ Yᵣ then
      simp [hiₗ, hjₗ, hiᵣ, hjᵣ]
    else
      exact (j.property.elim hjᵣ hjₗ).elim
  else if hiᵣ : i.val ∈ Xᵣ then
    if hjₗ : j.val ∈ Yₗ then
      have hjᵣ : j.val ∉ Yᵣ := Set.disjoint_left.→ hYY hjₗ
      simp [hiₗ, hjₗ, hiᵣ, hjᵣ]
    else if hjᵣ : j.val ∈ Yᵣ then
      simp [hiₗ, hjₗ, hiᵣ, hjᵣ]
    else
      exact (j.property.elim hjᵣ hjₗ).elim
  else
    exact (i.property.elim hiᵣ hiₗ).elim


-- ## 1-sum of standard representations

def standardReprOneSum {α : Type} {Sₗ Sᵣ : StandardRepr α Z2} (hXY : ) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      Sₗ.X ∪ Sᵣ.X,
      Sₗ.Y ∪ Sᵣ.Y,
      inferInstance,
      inferInstance,
      inferInstance,
      inferInstance,
      by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      (Sₗ.A.oneSum Sᵣ.A).toMatrixUnionUnion,
    ⟩,
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.X ⫗ Sᵣ.Y ∧ Sₗ.Y ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  ⟩

-- lemma standardReprOneSum_hasTuSigning {α : Type} {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :

-- lemma standardRepr1sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2}
--     (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
--     (standardRepr1sumComposition hXY hYX).fst.B.HasTuSigning :=
--   have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
--   have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
--   ⟨_, (Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ).toMatrixUnionUnion, (fun i j =>
--     show |((matrix1sumComposition Bₗ Bᵣ ∘ _) i ∘ _) j| = ZMod.val (((_ ∘ _) i ∘ _) j)
--     from Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸ Function.comp_apply ▸
--       i.toSum.casesOn (fun iₗ => j.toSum.casesOn (hBBₗ iₗ) ↓abs_zero) (fun iᵣ => j.toSum.casesOn ↓abs_zero (hBBᵣ iᵣ)))⟩

-- /-- A valid 1-sum of binary matroids is commutative. -/
-- lemma standardRepr1sumComposition_comm {R : Type} [DivisionRing R] {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
--     -- (dumb1 : DecidableEq (Xₗ ∪ Xᵣ).Elem := by exact?)
--     [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
--     (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
--     (hXₗXᵣ : Xₗ ⫗ Xᵣ) (hXₗYₗ : Xₗ ⫗ Yₗ) (hXₗYᵣ : Xₗ ⫗ Yᵣ) (hYₗXᵣ : Yₗ ⫗ Xᵣ) (hYₗYᵣ : Yₗ ⫗ Yᵣ) (hXᵣYᵣ : Xᵣ ⫗ Yᵣ) :
--     (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toStandardVectorMatroid =
--     (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toStandardVectorMatroid := by
--   have : DecidableEq (Xₗ ∪ Xᵣ).Elem := by exact Classical.typeDecidableEq (Xₗ ∪ Xᵣ).Elem
--   rw [standardRepr1sumComposition_eq_disjointSum Aₗ Aᵣ hXₗXᵣ hXₗYₗ hXₗYᵣ hYₗXᵣ hYₗYᵣ hXᵣYᵣ,
--       standardRepr1sumComposition_eq_disjointSum Aᵣ Aₗ hXₗXᵣ.symm hXᵣYᵣ hYₗXᵣ.symm hXₗYᵣ.symm hYₗYᵣ.symm hXₗYₗ,
--       Matroid.disjointSum_comm]

-- lemma standardRepr1sumComposition_hasTuSigning {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
--     [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
--     [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
--     {Aₗ : Matrix Xₗ Yₗ Z2} {Aᵣ : Matrix Xᵣ Yᵣ Z2} (hAₗ : Aₗ.HasTuSigning) (hAᵣ : Aᵣ.HasTuSigning) :
--     (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.HasTuSigning :=
--   (Matrix.oneSum_hasTuSigning hAₗ hAᵣ).toMatrixUnionUnion


-- ## 1-sum of matroids

/-- Matroid `M` is a 1-sum composition of `Mₗ` and `Mᵣ`. -/
structure Matroid.IsOneSumOf {α : Type} (M Mₗ Mᵣ : Matroid α) where
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.Y
  hSᵣ : Finite Sᵣ.Y
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hMₗ : Mₗ = Sₗ.toMatroid
  hMᵣ : Mᵣ = Sᵣ.toMatroid
  hM : M = (standardReprOneSum hXY hYX).fst.toMatroid
  IsValid : (standardReprOneSum hXY hYX).snd

-- instance Matroid.IsOneSumOf.finS {α : Type} {M Mₗ Mᵣ : Matroid α} (hM : M.IsOneSumOf Mₗ Mᵣ) :
--     Fintype (hM.Sₗ.Y ∪ hM.Sᵣ.Y).Elem := by
--   exact Fintype.ofFinite (hM.Sₗ.Y ∪ hM.Sᵣ.Y).Elem

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsOneSumOf.isRegular {α : Type} {M Mₗ Mᵣ : Matroid α}
    (hM : M.IsOneSumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  -- obtain ⟨Xₗ, Yₗ, Xᵣ, Yᵣ, deqXₗ, deqYₗ, deqXᵣ, deqYᵣ, deqXX, deqYY, dmemXₗ, dmemYₗ, dmemXᵣ, dmemYᵣ, Aₗ, Aᵣ, rfl, rfl, rfl, IsValid⟩ := hM
  -- have t : Aₗ.HasTuSigning := by exact?

  apply standardRepr1sumComposition_hasTuSigning
  sorry
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr1sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ


-- ## Equivalence with Matroid.disjointSum

-- set_option maxHeartbeats 0 in
/-- Matroid corresponding to matrix 1-sum is the same as the disjoint sum of matroids constructed from them. -/
lemma fullRepr1sumComposition_eq_disjointSum {R : Type} [DivisionRing R] {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
    (hXₗXᵣ : Xₗ ⫗ Xᵣ) (hXₗYₗ : Xₗ ⫗ Yₗ) (hXₗYᵣ : Xₗ ⫗ Yᵣ) (hYₗXᵣ : Yₗ ⫗ Xᵣ) (hYₗYᵣ : Yₗ ⫗ Yᵣ) (hXᵣYᵣ : Xᵣ ⫗ Yᵣ) :
    (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toVectorMatroid
    = Matroid.disjointSum Aₗ.toVectorMatroid Aᵣ.toVectorMatroid (by
        rw [Aₗ.toVectorMatroid_E, Aᵣ.toVectorMatroid_E]
        exact hXₗXᵣ) := by
  unfold Matrix.oneSum Matrix.toMatrixUnionUnion Matroid.disjointSum
  simp only [Function.comp_apply]
  ext I hI
  constructor
  · aesop
  · aesop
  · rw [Matrix.toVectorMatroid_E] at hI
    constructor
    · intro ⟨_, hI_indep⟩
      simp only [Matrix.toVectorMatroid_E, Matroid.mapEmbedding_indep_iff, Matroid.sum_indep_iff,
        Matroid.restrictSubtype_indep_iff, Function.Embedding.sumSet_preimage_inl,
        Matrix.toVectorMatroid_indep, Matrix.linearIndepRows_iff_elem, Function.range,
        Set.inter_subset_right, exists_true_left, Function.Embedding.sumSet_preimage_inr,
        Function.Embedding.sumSet_range]
      constructor
      · constructor
        · rw [linearIndepOn_iff] at hI_indep ⊢
          intro sₗ hsₗ hsₗ0
          let embₗ : Xₗ ↪ (Xₗ ∪ Xᵣ).Elem := Set.subset_union_left.elem_embedding
          refine Finsupp.embDomain_eq_zero.→ (hI_indep (Finsupp.embDomain embₗ sₗ) ?_ ?_)
          · rw [Finsupp.mem_supported] at hsₗ ⊢
            rw [Finsupp.support_embDomain embₗ sₗ]
            simp only [Finset.coe_map, Function.Embedding.coeFn_mk, HasSubset.Subset.elem,
              Set.image_subset_iff]
            let f : I ∩ Xₗ ⊆ Xₗ := Set.inter_subset_right
            have hssₗ : Set.range f.elem ⊆ ⇑embₗ ⁻¹' (Subtype.val ⁻¹' I) := fun _ => by aesop
            exact hsₗ.trans hssₗ
          · rw [Finsupp.linearCombination_embDomain]
            rw [funext_iff] at hsₗ0
            ext y
            simp only [Pi.zero_apply] at hsₗ0 ⊢
            if hyₗ : y.val ∈ Yₗ then
              specialize hsₗ0 ⟨y.val, hyₗ⟩
              simp only [←hsₗ0, embₗ, Finsupp.linearCombination_apply, Finsupp.sum.eq_1]
              simp [hyₗ]
            else if hyᵣ : y.val ∈ Yᵣ then
              simp [hyₗ, hyᵣ, embₗ, Finsupp.linearCombination, Finsupp.sum]
            else
              exact (y.property.elim hyₗ hyᵣ).elim
        · rw [linearIndepOn_iff] at hI_indep ⊢
          intro sᵣ hsᵣ hsᵣ0
          let embᵣ : Xᵣ ↪ (Xₗ ∪ Xᵣ).Elem := Set.subset_union_right.elem_embedding
          refine Finsupp.embDomain_eq_zero.→ (hI_indep (Finsupp.embDomain embᵣ sᵣ) ?_ ?_)
          · rw [Finsupp.mem_supported] at hsᵣ ⊢
            rw [Finsupp.support_embDomain embᵣ sᵣ]
            simp only [Finset.coe_map, Function.Embedding.coeFn_mk, HasSubset.Subset.elem,
              Set.image_subset_iff]
            let f : I ∩ Xᵣ ⊆ Xᵣ := Set.inter_subset_right
            have hssᵣ : Set.range f.elem ⊆ ⇑embᵣ ⁻¹' (Subtype.val ⁻¹' I) := fun _ => by aesop
            exact hsᵣ.trans hssᵣ
          · rw [Finsupp.linearCombination_embDomain]
            rw [funext_iff] at hsᵣ0
            ext y
            simp only [Pi.zero_apply] at hsᵣ0 ⊢
            if hyᵣ : y.val ∈ Yᵣ then
              specialize hsᵣ0 ⟨y.val, hyᵣ⟩
              simp only [←hsᵣ0, embᵣ, Finsupp.linearCombination_apply, Finsupp.sum.eq_1]
              simp [hyᵣ]
              unfold Subtype.toSum
              sorry
            else if hyₗ : y.val ∈ Yₗ then
              simp [hyₗ, hyᵣ, embᵣ, Finsupp.linearCombination, Finsupp.sum, toSum_left]
              sorry
            else
              exact (y.property.elim hyₗ hyᵣ).elim
      · exact hI
    · simp only [Matrix.toVectorMatroid_E, Matroid.mapEmbedding_indep_iff, Matroid.sum_indep_iff,
        Matroid.restrictSubtype_indep_iff, Function.Embedding.sumSet_preimage_inl,
        Matrix.toVectorMatroid_indep, Matrix.linearIndepRows_iff_elem, Function.range,
        Set.inter_subset_right, exists_true_left, Function.Embedding.sumSet_preimage_inr,
        Function.Embedding.sumSet_range, and_imp]
      intro hIₗ hIᵣ hIXX
      use hI
      sorry

/-- Matroid corresponding to matrix 1-sum is the same as the disjoint sum of matroids constructed from them. -/
lemma standardRepr1sumComposition_eq_disjointSum {R : Type} [DivisionRing R] {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
    (hXₗXᵣ : Xₗ ⫗ Xᵣ) (hXₗYₗ : Xₗ ⫗ Yₗ) (hXₗYᵣ : Xₗ ⫗ Yᵣ) (hYₗXᵣ : Yₗ ⫗ Xᵣ) (hYₗYᵣ : Yₗ ⫗ Yᵣ) (hXᵣYᵣ : Xᵣ ⫗ Yᵣ) :
    (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toStandardVectorMatroid
    = Matroid.disjointSum Aₗ.toStandardVectorMatroid Aᵣ.toStandardVectorMatroid (by
        rw [Aₗ.toStandardVectorMatroid_E, Aᵣ.toStandardVectorMatroid_E,
          Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨hXₗXᵣ, hYₗXᵣ⟩, ⟨hXₗYᵣ, hYₗYᵣ⟩⟩) := by
  unfold Matrix.oneSum Matrix.toMatrixUnionUnion
  simp only [Function.comp_apply, IndepMatroid.matroid_E]
  sorry
