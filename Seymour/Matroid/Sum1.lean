import Mathlib.Data.Matroid.Sum
import Seymour.Matroid.Regular


-- ## 1-sum of matrices

/-- 1-sum of matrices. -/
abbrev Matrix.oneSum {R : Type} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type} (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

/-- If matrices have TU signings, then their 1-sum has a TU signing. -/
lemma Matrix.oneSum_hasTuSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} [DecidableEq Xₗ] [DecidableEq Yₗ] [DecidableEq Xᵣ] [DecidableEq Yᵣ]
    {Aₗ : Matrix Xₗ Yₗ Z2} {Aᵣ : Matrix Xᵣ Yᵣ Z2} (hAₗ : Aₗ.HasTuSigning) (hAᵣ : Aᵣ.HasTuSigning) :
    (Aₗ.oneSum Aᵣ).HasTuSigning :=
  have ⟨_, hAAₗ, hBₗ⟩ := hAₗ
  have ⟨_, hAAᵣ, hBᵣ⟩ := hAᵣ
  ⟨
    _,
    fun i j => i.casesOn (fun iₗ => j.casesOn (hAAₗ iₗ) ↓abs_zero) (fun iᵣ => j.casesOn ↓abs_zero (hAAᵣ iᵣ)),
    Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ
  ⟩

private lemma Matrix.HasTuSigning.toMatrixUnionUnion {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α} {A : Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) Z2}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hA : A.HasTuSigning) :
    A.toMatrixUnionUnion.HasTuSigning :=
  have ⟨_, hAA, hB⟩ := hA
  ⟨
    _,
    (hAA ·.toSum ·.toSum),
    hB.toMatrixUnionUnion
  ⟩

/-- Equivalence mapping between union of two sets written in different order. -/
private abbrev union_comm_equiv {α : Type} (A B : Set α) : (A ∪ B).Elem ≃ (B ∪ A).Elem where
  toFun := fun i => ⟨i.val, i.property.symm⟩
  invFun := fun i => ⟨i.val, i.property.symm⟩
  left_inv := (by intro x; simp only [Subtype.coe_eta])
  right_inv := (by intro x; simp only [Subtype.coe_eta])

/-- 1-sum is commutative up to reindexing of resulting matrices. -/
lemma Matrix.oneSum_comm {R : Type} [DivisionRing R] {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
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

noncomputable def standardReprOneSumRepr {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 where
  X := Sₗ.X ∪ Sᵣ.X
  Y := Sₗ.Y ∪ Sᵣ.Y
  hXY := by simp only [Set.disjoint_union_left, Set.disjoint_union_right]; exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩
  A := (Sₗ.A.oneSum Sᵣ.A).toMatrixUnionUnion
  deqX := inferInstance
  deqY := inferInstance
  dmemX := inferInstance
  dmemY := inferInstance

def standardReprOneSumIsValid {α : Type} {Sₗ Sᵣ : StandardRepr α Z2} (_hXY : Sₗ.X ⫗ Sᵣ.Y) (_hYX : Sₗ.Y ⫗ Sᵣ.X) : Prop :=
  Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y

noncomputable def standardReprOneSum {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨standardReprOneSumRepr hXY hYX, standardReprOneSumIsValid hXY hYX⟩

@[simp]
private lemma standardReprOneSum_A_eq {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardReprOneSumRepr hXY hYX).A = (Sₗ.A.oneSum Sᵣ.A).toMatrixUnionUnion :=
  rfl

noncomputable instance standardReprOneSum.finY {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) [Fintype Sₗ.Y] [Fintype Sᵣ.Y] :
    Fintype (standardReprOneSumRepr hXY hYX).Y :=
  Fintype.ofFinite (Sₗ.Y ∪ Sᵣ.Y).Elem

lemma standardReprOneSum_hasTuSigning {α : Type} [DecidableEq α] {Sₗ Sᵣ : StandardRepr α Z2}
    (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) (hSₗ : Sₗ.A.HasTuSigning) (hSᵣ : Sᵣ.A.HasTuSigning) :
    (standardReprOneSumRepr hXY hYX).A.HasTuSigning :=
  (Matrix.oneSum_hasTuSigning hSₗ hSᵣ).toMatrixUnionUnion


-- ## 1-sum of matroids

/-- Matroid `M` is a 1-sum composition of `Mₗ` and `Mᵣ`. -/
structure Matroid.IsOneSumOf {α : Type} [DecidableEq α] (M Mₗ Mᵣ : Matroid α) where
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Fintype Sₗ.Y
  hSᵣ : Fintype Sᵣ.Y
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  hMₗ : Mₗ = Sₗ.toMatroid
  hMᵣ : Mᵣ = Sᵣ.toMatroid
  hM : M = (standardReprOneSumRepr hXY hYX).toMatroid
  IsValid : standardReprOneSumIsValid hXY hYX

noncomputable instance Matroid.IsOneSumOf.finY {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α} (hM : M.IsOneSumOf Mₗ Mᵣ) :
    Fintype (standardReprOneSumRepr hM.hXY hM.hYX).Y :=
  have := hM.hSₗ
  have := hM.hSᵣ
  Fintype.ofFinite (hM.Sₗ.Y ∪ hM.Sᵣ.Y).Elem

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsOneSumOf.isRegular {α : Type} [DecidableEq α] {M Mₗ Mᵣ : Matroid α}
    (hM : M.IsOneSumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨Sₗ, Sᵣ, hSₗ, hSᵣ, hXY, hYX, rfl, rfl, rfl, IsValid⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprOneSum_hasTuSigning hXY hYX hMₗ hMᵣ


-- ## Equivalence with Matroid.disjointSum

-- set_option maxHeartbeats 0 in
/-- Matroid corresponding to matrix 1-sum is the same as the disjoint sum of matroids constructed from them. -/
lemma fullReprOneSum_eq_disjointSum {R : Type} [DivisionRing R] {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
    (hXₗXᵣ : Xₗ ⫗ Xᵣ) (hXₗYₗ : Xₗ ⫗ Yₗ) (hXₗYᵣ : Xₗ ⫗ Yᵣ) (hYₗXᵣ : Yₗ ⫗ Xᵣ) (hYₗYᵣ : Yₗ ⫗ Yᵣ) (hXᵣYᵣ : Xᵣ ⫗ Yᵣ) :
    (Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toMatroid
    = Matroid.disjointSum Aₗ.toMatroid Aᵣ.toMatroid (by rw [Aₗ.toMatroid_E, Aᵣ.toMatroid_E]; exact hXₗXᵣ) := by
  unfold Matrix.oneSum Matrix.toMatrixUnionUnion Matroid.disjointSum
  simp only [Function.comp_apply]
  ext I hI
  constructor
  · aesop
  · aesop
  · rw [Matrix.toMatroid_E] at hI
    constructor
    · intro ⟨_, hI_indep⟩
      simp only [Matrix.toMatroid_E, Matroid.mapEmbedding_indep_iff, Matroid.sum_indep_iff,
        Matroid.restrictSubtype_indep_iff, Function.Embedding.sumSet_preimage_inl,
        Matrix.toMatroid_indep, Matrix.linearIndepRows_iff_elem, Function.range,
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
              sorry  -- todo: use disjointedness to complete proof
            else if hyₗ : y.val ∈ Yₗ then
              simp [hyₗ, hyᵣ, embᵣ, Finsupp.linearCombination, Finsupp.sum, toSum_left]
              sorry  -- todo: use disjointedness to complete proof
            else
              exact (y.property.elim hyₗ hyᵣ).elim
      · exact hI
    · simp only [Matrix.toMatroid_E, Matroid.mapEmbedding_indep_iff, Matroid.sum_indep_iff,
        Matroid.restrictSubtype_indep_iff, Function.Embedding.sumSet_preimage_inl,
        Matrix.toMatroid_indep, Matrix.linearIndepRows_iff_elem, Function.range,
        Set.inter_subset_right, exists_true_left, Function.Embedding.sumSet_preimage_inr,
        Function.Embedding.sumSet_range, and_imp]
      intro hIₗ hIᵣ hIXX
      use hI
      sorry  -- todo: complete proof

/-- Matroid corresponding to matrix 1-sum is the same as the disjoint sum of matroids constructed from them. -/
lemma standardReprOneSum_eq_disjointSum {R : Type} [DivisionRing R] {α : Type} [DecidableEq α] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
    (hXₗXᵣ : Xₗ ⫗ Xᵣ) (hXₗYₗ : Xₗ ⫗ Yₗ) (hXₗYᵣ : Xₗ ⫗ Yᵣ) (hYₗXᵣ : Yₗ ⫗ Xᵣ) (hYₗYᵣ : Yₗ ⫗ Yᵣ) (hXᵣYᵣ : Xᵣ ⫗ Yᵣ) :
    ((Aₗ.oneSum Aᵣ).toMatrixUnionUnion.toStandardRepr (by sorry)).toMatroid
    = Matroid.disjointSum (Aₗ.toStandardRepr (by sorry)).toMatroid (Aᵣ.toStandardRepr (by sorry)).toMatroid (by sorry)
        -- rw [Aₗ.toStandardRepr.toMatroid_E, Aᵣ.toStandardRepr.toMatroid_E,
        --   Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        -- exact ⟨⟨hXₗXᵣ, hYₗXᵣ⟩, ⟨hXₗYᵣ, hYₗYᵣ⟩⟩)
        := by
  sorry  -- todo: reduce to `fullRepr1sumComposition_eq_disjointSum`
