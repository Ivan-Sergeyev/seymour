import Seymour.Matrix.Conversions
import Seymour.Matroid.Regularity

/-!
# Matroid 1-sum

Here we study the 1-sum of matroids (starting with the 1-sum of matrices).
-/

/-! ## Definition -/

/-- `Matrix`-level 1-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
def matrixSum1 {R : Type*} [Zero R] {Xₗ Yₗ Xᵣ Yᵣ : Type*}
    (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) R :=
  ⊞ Aₗ 0 0 Aᵣ

variable {α : Type*} [DecidableEq α]

/-- `StandardRepr`-level 1-sum of two matroids. Returns the result only if valid. -/
noncomputable def standardReprSum1 {Sₗ Sᵣ : StandardRepr α Z2} (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    Option (StandardRepr α Z2) :=
  open scoped Classical in if
    Sₗ.X ⫗ Sᵣ.X ∧ Sₗ.Y ⫗ Sᵣ.Y
  then
    some ⟨
      -- row indices
      Sₗ.X ∪ Sᵣ.X,
      -- col indices
      Sₗ.Y ∪ Sᵣ.Y,
      -- row and col indices are disjoint
      by rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
         exact ⟨⟨Sₗ.hXY, hYX.symm⟩, ⟨hXY, Sᵣ.hXY⟩⟩,
      -- standard representation matrix
      (matrixSum1 Sₗ.B Sᵣ.B).toMatrixUnionUnion,
      -- decidability of row indices
      inferInstance,
      -- decidability of col indices
      inferInstance⟩
  else
    none

/-- Binary matroid `M` is a result of 1-summing `Mₗ` and `Mᵣ` in some way. -/
def Matroid.IsSum1of (M : Matroid α) (Mₗ Mᵣ : Matroid α) : Prop :=
  ∃ S Sₗ Sᵣ : StandardRepr α Z2,
  ∃ hXY : Sₗ.X ⫗ Sᵣ.Y,
  ∃ hYX : Sₗ.Y ⫗ Sᵣ.X,
  standardReprSum1 hXY hYX = some S
  ∧ Finite Sₗ.X
  ∧ Finite Sᵣ.X
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ


/-! ## Results -/

lemma standardReprSum1_disjoint_X {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    Sₗ.X ⫗ Sᵣ.X := by
  simp [standardReprSum1] at hS
  tauto

lemma standardReprSum1_disjoint_Y {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    Sₗ.Y ⫗ Sᵣ.Y := by
  simp [standardReprSum1] at hS
  tauto

lemma standardReprSum1_X_eq {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.X = Sₗ.X ∪ Sᵣ.X := by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.X hSSS.symm

lemma standardReprSum1_Y_eq {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.Y = Sₗ.Y ∪ Sᵣ.Y := by
  simp_rw [standardReprSum1, Option.ite_none_right_eq_some, Option.some.injEq] at hS
  obtain ⟨_, hSSS⟩ := hS
  exact congr_arg StandardRepr.Y hSSS.symm

lemma Matroid.IsSum1of.E_eq (M : Matroid α) (Mₗ Mᵣ : Matroid α) (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M.E = Mₗ.E ∪ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, hS, _, _, rfl, rfl, rfl⟩ := hMMM
  have hX := standardReprSum1_X_eq hS
  have hY := standardReprSum1_Y_eq hS
  simp only [StandardRepr.toMatroid_E]
  tauto_set

private lemma standardReprSum1_eq_disjointSum_partitioned {Xₗ Yₗ Xᵣ Yᵣ Iₗ Iᵣ Jₗ Jᵣ : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : (Iₗ ∪ Iᵣ) ∪ (Jₗ ∪ Jᵣ) ⊆ (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ)) (hIₗ : Iₗ ∪ Jₗ ⊆ Yₗ ∪ Xₗ) (hIᵣ : Iᵣ ∪ Jᵣ ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range := by
  sorry

private lemma standardReprSum1_eq_disjointSum_untransposed {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ) (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range := by
  have hI' := hI
  have hIₗ' := hIₗ
  have hIᵣ' := hIᵣ
  rw [←Set.left_eq_inter] at hI'
  simp only [Set.inter_union_distrib_left] at hIₗ' hIᵣ' hI'
  have hhIₗ' : hIₗ.elem.range = hIₗ'.elem.range := sorry
  have hhIᵣ' : hIᵣ.elem.range = hIᵣ'.elem.range := sorry
  convert standardReprSum1_eq_disjointSum_partitioned hXY hYX Bₗ Bᵣ (by rw [hI'] at hI; congr) hIₗ' hIᵣ'

private lemma standardReprSum1_eq_disjointSum_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Xₗ ∪ Xᵣ) ∪ (Yₗ ∪ Yᵣ)) (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ) (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion.transpose) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range :=
  (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion_transpose ▸
  Matrix.fromBlocks_transpose .. ▸
  standardReprSum1_eq_disjointSum_untransposed hYX hXY Bₗ.transpose Bᵣ.transpose hI hIₗ hIᵣ

private lemma standardReprSum1_eq_disjointSum_aux {Xₗ Yₗ Xᵣ Yᵣ X Y I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXXX : X = Xₗ ∪ Xᵣ) (hYYY : Y = Yₗ ∪ Yᵣ) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ X ∪ Y) (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ) (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    have : ∀ a : α, Decidable (a ∈ X) := hXXX ▸ (Set.decidableUnion Xₗ Xᵣ ·)
    have : ∀ a : α, Decidable (a ∈ Y) := hYYY ▸ (Set.decidableUnion Yₗ Yᵣ ·)
    LinearIndepOn Z2 ((1 ⊟ ((⊞ Bₗ 0 0 Bᵣ).toMatrixElemElem hXXX hYYY).transpose) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range := by
  subst hXXX hYYY
  convert standardReprSum1_eq_disjointSum_aux_aux hXY hYX Bₗ Bᵣ hI hIₗ hIᵣ

lemma standardReprSum1_eq_disjointSum {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.toMatroid = Matroid.disjointSum Sₗ.toMatroid Sᵣ.toMatroid (by
      simp [StandardRepr.toMatroid, StandardRepr.toFull, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨standardReprSum1_disjoint_X hS, hYX⟩, ⟨hXY, standardReprSum1_disjoint_Y hS⟩⟩) := by
  have hXXX := standardReprSum1_X_eq hS
  have hYYY := standardReprSum1_Y_eq hS
  ext I hIS
  · aesop
  · rw [Matroid.disjointSum_indep_iff]
    have hIEE : I ⊆ Sₗ.toMatroid.E ∪ Sᵣ.toMatroid.E
    · simpa [hXXX, hYYY, Set.union_comm, Set.union_left_comm] using hIS
    have hB : S.B = (⊞ Sₗ.B 0 0 Sᵣ.B).toMatrixElemElem hXXX hYYY
    · simp only [standardReprSum1, Option.ite_none_right_eq_some] at hS
      aesop
    simp_rw [hIEE]
    simp [show I ⊆ S.X ∪ S.Y from hIS]
    convert standardReprSum1_eq_disjointSum_aux hXXX hYYY hXY hYX Sₗ.B Sᵣ.B hIS Set.inter_subset_right Set.inter_subset_right

lemma standardReprSum1_hasTuSigning {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning)
    (hS : standardReprSum1 hXY hYX = some S) :
    S.B.HasTuSigning := by
  have ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  have ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  have hSX : S.X = Sₗ.X ∪ Sᵣ.X := standardReprSum1_X_eq hS
  have hSY : S.Y = Sₗ.Y ∪ Sᵣ.Y := standardReprSum1_Y_eq hS
  have hSB : S.B = (matrixSum1 Sₗ.B Sᵣ.B).toMatrixElemElem hSX hSY
  · simp_rw [standardReprSum1, Option.ite_none_right_eq_some] at hS
    aesop
  use (matrixSum1 Bₗ Bᵣ).toMatrixElemElem hSX hSY, (Matrix.fromBlocks_isTotallyUnimodular hBₗ hBᵣ).toMatrixElemElem hSX hSY
  rw [hSB]
  intro i j
  simp only [Matrix.toMatrixElemElem_apply]
  exact (hSX ▸ i).toSum.casesOn
    (fun iₗ => (hSY ▸ j).toSum.casesOn (hBBₗ iₗ) ↓abs_zero)
    (fun iᵣ => (hSY ▸ j).toSum.casesOn ↓abs_zero (hBBᵣ iᵣ))

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsSum1of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum1of Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, _, _, _, _, hS, _, _, rfl, rfl, rfl⟩ := hMMM
  have : Finite S.X := standardReprSum1_X_eq hS ▸ Finite.Set.finite_union ..
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum1_hasTuSigning hMₗ hMᵣ hS
