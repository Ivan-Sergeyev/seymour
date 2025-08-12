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
  ∧ S.toMatroid = M
  ∧ Sₗ.toMatroid = Mₗ
  ∧ Sᵣ.toMatroid = Mᵣ


/-! ## API -/

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

lemma Matroid.IsSum1of.E_eq {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M.E = Mₗ.E ∪ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  have hX := standardReprSum1_X_eq hS
  have hY := standardReprSum1_Y_eq hS
  simp only [StandardRepr.toMatroid_E]
  tauto_set

lemma standardReprSum1_disjoint_E {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    Sₗ.toMatroid.E ⫗ Sᵣ.toMatroid.E := by
  simp
  exact ⟨⟨standardReprSum1_disjoint_X hS, hYX⟩, ⟨hXY, standardReprSum1_disjoint_Y hS⟩⟩

lemma Matroid.IsSum1of.disjoint_E {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    Mₗ.E ⫗ Mᵣ.E := by
  obtain ⟨S, _, _, _, _, hS, _, rfl, rfl⟩ := hMMM
  exact standardReprSum1_disjoint_E hS


/-! ## Results -/

set_option maxHeartbeats 333333 in
open scoped Set.Notation in
lemma Disjoint.linearIndepOn_fromRows_elem_range_iff {Xₗ Xᵣ Y I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Y)]
    (hXX : Xₗ ⫗ Xᵣ) (Aₗ : Matrix Xₗ Y Z2) (Aᵣ : Matrix Xᵣ Y Z2)
    (hI : I ⊆ Xₗ ∪ Xᵣ) (hIXₗ : I ∩ Xₗ ⊆ Xₗ) (hIXᵣ : I ∩ Xᵣ ⊆ Xᵣ) :
    LinearIndepOn Z2 (((Aₗ ⊟ Aᵣ) ∘ Subtype.toSum)) hI.elem.range ↔
      LinearIndepOn Z2 Aₗ hIXₗ.elem.range ∧
      LinearIndepOn Z2 Aᵣ hIXᵣ.elem.range := by
  have hXₗ : Xₗ ⊆ (Xₗ ∪ Xᵣ) := Set.subset_union_left
  have hXᵣ : Xᵣ ⊆ (Xₗ ∪ Xᵣ) := Set.subset_union_right
  rw [linearIndepOn_iff, linearIndepOn_iff, linearIndepOn_iff]
  constructor
  · intro hAA
    constructor
    <;> intro c hc hc0
    · specialize hAA
        ⟨c.support.map hXₗ.embed, fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xₗ then c ⟨x.val, hx⟩ else 0, by aesop⟩
        (by sorry)
        (by sorry)
      ext i
      simpa using congr_fun (congr_arg Finsupp.toFun hAA) (hXₗ.elem i)
    · specialize hAA
        ⟨c.support.map hXᵣ.embed, fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xᵣ then c ⟨x.val, hx⟩ else 0, by aesop⟩
        (by sorry)
        (by sorry)
      ext i
      simpa using congr_fun (congr_arg Finsupp.toFun hAA) (hXᵣ.elem i)
  · intro ⟨hAₗ, hAᵣ⟩ c hc hc0
    have : Fintype (Xₗ ↓∩ c.support.toSet) :=
      ((c.support.finite_toSet.image Subtype.val).preimage'
        ↓↓(Set.subsingleton_singleton.preimage Subtype.val_injective).finite
      ).fintype
    have : Fintype (Xᵣ ↓∩ c.support.toSet) :=
      ((c.support.finite_toSet.image Subtype.val).preimage'
        ↓↓(Set.subsingleton_singleton.preimage Subtype.val_injective).finite
      ).fintype
    specialize hAₗ ⟨(Xₗ ↓∩ c.support.toSet).toFinset, fun x : Xₗ => c (hXₗ.elem x), by aesop⟩ (by sorry) (by sorry)
    specialize hAᵣ ⟨(Xᵣ ↓∩ c.support.toSet).toFinset, fun x : Xᵣ => c (hXᵣ.elem x), by aesop⟩ (by sorry) (by sorry)
    ext i
    if hiXₗ : i.val ∈ Xₗ then
      exact congr_fun (congr_arg Finsupp.toFun hAₗ) ⟨i.val, hiXₗ⟩
    else
      have hiXᵣ : i.val ∈ Xᵣ
      · sorry
      exact congr_fun (congr_arg Finsupp.toFun hAᵣ) ⟨i.val, hiXᵣ⟩

private lemma standardReprSum1_eq_disjointSum_untransposed_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (Aₗ : Matrix Xₗ Yₗ Z2) (Aᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ Xₗ ∪ Xᵣ) (hIXₗ : I ∩ Xₗ ⊆ Xₗ) (hIXᵣ : I ∩ Xᵣ ⊆ Xᵣ) :
    LinearIndepOn Z2 (((⊞ Aₗ 0 0 Aᵣ).toMatrixUnionUnion)) hI.elem.range ↔
      LinearIndepOn Z2 Aₗ hIXₗ.elem.range ∧
      LinearIndepOn Z2 Aᵣ hIXᵣ.elem.range := by
  have hIAₗ : LinearIndepOn Z2 Aₗ hIXₗ.elem.range ↔ LinearIndepOn Z2 (Aₗ ◫ (0 : Matrix Xₗ Yᵣ Z2)) hIXₗ.elem.range
  · sorry
  have hIAᵣ : LinearIndepOn Z2 Aᵣ hIXᵣ.elem.range ↔ LinearIndepOn Z2 ((0 : Matrix Xᵣ Yₗ Z2) ◫ Aᵣ) hIXᵣ.elem.range
  · sorry
  rw [hIAₗ, hIAᵣ]
  have : ∀ a : α, Decidable (a ∈ Yₗ ∪ Yᵣ) := (Set.decidableUnion Yₗ Yᵣ ·)
  convert
    hXX.linearIndepOn_fromRows_elem_range_iff
      (((Aₗ ◫ 0) : Matrix Xₗ (Yₗ ⊕ Yᵣ) Z2).submatrix id Subtype.toSum)
      (((0 ◫ Aᵣ) : Matrix Xᵣ (Yₗ ⊕ Yᵣ) Z2).submatrix id Subtype.toSum)
      hI hIXₗ hIXᵣ
  · ext i j
    cases hi : i.toSum with
    | inl iₗ =>
      cases hj : j.toSum with
      | inl jₗ => sorry
      | inr jᵣ => sorry
    | inr iᵣ =>
      cases hj : j.toSum with
      | inl jₗ => sorry
      | inr jᵣ => sorry
  · sorry
  · sorry

private lemma standardReprSum1_eq_disjointSum_untransposed_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ) (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 (((⊞ ((1 ⊟ Bₗ) ∘ Subtype.toSum) 0 0 ((1 ⊟ Bᵣ) ∘ Subtype.toSum)).toMatrixUnionUnion)) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range := by
  apply standardReprSum1_eq_disjointSum_untransposed_aux_aux sorry sorry

private lemma standardReprSum1_eq_disjointSum_untransposed {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ) (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range := by
  have hI' : I ⊆ (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ)
  · tauto_set
  rw [←standardReprSum1_eq_disjointSum_untransposed_aux hXY hYX Bₗ Bᵣ hI' hIₗ hIᵣ]
  sorry

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
    S.toMatroid = Matroid.disjointSum Sₗ.toMatroid Sᵣ.toMatroid (standardReprSum1_disjoint_E hS) := by
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
    -- TODO also disjointness from the `StandardRepr` structures will have to be propagated
    convert standardReprSum1_eq_disjointSum_aux hXXX hYYY hXY hYX Sₗ.B Sᵣ.B hIS Set.inter_subset_right Set.inter_subset_right

theorem Matroid.IsSum1of.eq_disjointSum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M = Matroid.disjointSum Mₗ Mᵣ hMMM.disjoint_E := by
  obtain ⟨S, _, _, _, _, hS, rfl, rfl, rfl⟩ := hMMM
  exact standardReprSum1_eq_disjointSum hS

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
    (fun iₗ : Sₗ.X => (hSY ▸ j).toSum.casesOn (hBBₗ iₗ) ↓abs_zero)
    (fun iᵣ : Sᵣ.X => (hSY ▸ j).toSum.casesOn ↓abs_zero (hBBᵣ iᵣ))

/-- Any 1-sum of regular matroids is a regular matroid.
    This is part one (of three) of the easy direction of the Seymour's theorem. -/
theorem Matroid.IsSum1of.isRegular {M Mₗ Mᵣ : Matroid α}
    (hMMM : M.IsSum1of Mₗ Mᵣ) (hM : M.RankFinite) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  obtain ⟨S, Sₗ, Sᵣ, _, _, hSSS, rfl, rfl, rfl⟩ := hMMM
  have hX : Finite S.X := S.finite_X_of_toMatroid_rankFinite hM
  obtain ⟨hXₗ, hXᵣ⟩ : Finite Sₗ.X ∧ Finite Sᵣ.X
  · simpa [standardReprSum1_X_eq hSSS, Set.finite_coe_iff] using hX
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  exact standardReprSum1_hasTuSigning hMₗ hMᵣ hSSS
