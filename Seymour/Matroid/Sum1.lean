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
      union_disjoint_union Sₗ.hXY Sᵣ.hXY hXY hYX,
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

set_option maxHeartbeats 666666 in
private lemma standardReprSum1_eq_disjointSum_untransposed_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (Aₗ : Matrix Xₗ Yₗ Z2) (Aᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ Xₗ ∪ Xᵣ) (hIXₗ : I ∩ Xₗ ⊆ Xₗ) (hIXᵣ : I ∩ Xᵣ ⊆ Xᵣ) :
    LinearIndepOn Z2 (((⊞ Aₗ 0 0 Aᵣ).toMatrixUnionUnion)) hI.elem.range ↔
      LinearIndepOn Z2 Aₗ hIXₗ.elem.range ∧
      LinearIndepOn Z2 Aᵣ hIXᵣ.elem.range := by
  have hIAₗ : LinearIndepOn Z2 Aₗ hIXₗ.elem.range ↔ LinearIndepOn Z2 (Aₗ ◫ (0 : Matrix Xₗ Yᵣ Z2)) hIXₗ.elem.range := by
    simp only [linearIndepOn_iff']
    constructor
    <;> intros h t g ht hg_zero i hi
    · apply h
      apply ht
      ext y
      have h := congrArg (fun v => v (Sum.inl y)) hg_zero
      simpa [Finset.sum_apply, Pi.smul_apply] using h
      exact hi
    · apply h
      apply ht
      ext j
      cases j with
      | inl y =>
        have h := congrArg (fun v => v y) hg_zero
        simpa [Finset.sum_apply, Pi.smul_apply] using h
      | inr y =>
        have : (∑ i in t, g i • (Aₗ ◫ (0 : Matrix (↑Xₗ) (↑Yᵣ) Z2)) i (Sum.inr y)) = ∑ i in t, 0 := by
            aesop
        aesop
      simp_all only [Set.inter_subset_right, Subtype.forall]
  have hIAᵣ : LinearIndepOn Z2 Aᵣ hIXᵣ.elem.range ↔ LinearIndepOn Z2 ((0 : Matrix Xᵣ Yₗ Z2) ◫ Aᵣ) hIXᵣ.elem.range := by
    simp only [linearIndepOn_iff']
    constructor
    <;> intros h t g ht hg_zero i hi
    · apply h
      apply ht
      ext y
      have h := congrArg (fun v => v (Sum.inr y)) hg_zero
      simpa [Finset.sum_apply, Pi.smul_apply] using h
      exact hi
    · apply h
      apply ht
      ext j
      cases j with
      | inl y =>
        have : (∑ i ∈ t, g i • ((0 : Matrix (↑Xᵣ) (↑Yₗ) Z2) ◫ Aᵣ) i (Sum.inl y)) = ∑ i in t, 0 := by
            aesop
        aesop
      | inr y =>
        have h := congrArg (fun v => v y) hg_zero
        simpa [Finset.sum_apply, Pi.smul_apply] using h
      simp_all only [Subtype.forall]
  --rw [hIAₗ, hIAᵣ]
  simp only [linearIndepOn_iff']
  have hXₗ : Xₗ ⊆ Xₗ ∪ Xᵣ := Set.subset_union_left
  have hXᵣ : Xᵣ ⊆ Xₗ ∪ Xᵣ := Set.subset_union_right
  have hYₗ : Yₗ ⊆ Yₗ ∪ Yᵣ := Set.subset_union_left
  have hYᵣ : Yᵣ ⊆ Yₗ ∪ Yᵣ := Set.subset_union_right
  constructor
  · intro h0
    constructor
    <;> intro s c hs hsc0 i hi
    · specialize h0 (s.map hXₗ.embed) (fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xₗ then c ⟨x.val, hx⟩ else 0)
      specialize h0 sorry sorry (hXₗ.elem i) (by simpa using hi)
      simpa using h0
    · specialize h0 (s.map hXᵣ.embed) (fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xᵣ then c ⟨x.val, hx⟩ else 0)
      specialize h0 sorry sorry (hXᵣ.elem i) (by simpa using hi)
      simpa using h0
  · intro ⟨h0Xₗ, h0Xᵣ⟩ s c hs hsc0 i hi
    specialize h0Xₗ (s.filterMap (fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xₗ then some ⟨x.val, hx⟩ else none) (by aesop))
    specialize h0Xᵣ (s.filterMap (fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xᵣ then some ⟨x.val, hx⟩ else none) (by aesop))
    if hiXₗ : i.val ∈ Xₗ then
      refine h0Xₗ (c ∘ hXₗ.elem) ?_ ?_ ⟨i, hiXₗ⟩ (by simp [hi, hiXₗ])
      · intro ⟨x, hxXₗ⟩ hxs
        simp at hxs
        use ⟨x, by simpa using hs hxs, hxXₗ⟩
        rfl
      · ext j
        have hsc0jₗ := congr_fun hsc0 (hYₗ.elem j)
        rw [Pi.zero_apply, Finset.sum_apply] at hsc0jₗ ⊢
        have hXXjₗ : ∀ x : (Xₗ ∪ Xᵣ).Elem, (⊞ Aₗ 0 0 Aᵣ) x.toSum ◩j = if hx : x.val ∈ Xₗ then Aₗ ⟨x.val, hx⟩ j else 0
        · intro x
          if hx : x.val ∈ Xₗ then
            simp [hx]
          else
            simp [hx, in_right_of_in_union_of_ni_left x.property]
        simp [Matrix.toMatrixUnionUnion, hXXjₗ, Finset.sum_dite] at hsc0jₗ
        convert hsc0jₗ
        exact Finset.sum_bij (↓⟨hXₗ.elem ·, by simp_all⟩) (by simp) (by simp) (by aesop) (by simp)
    else
      have hiXᵣ : i.val ∈ Xᵣ := in_right_of_in_union_of_ni_left i.property hiXₗ
      refine h0Xᵣ (c ∘ hXᵣ.elem) ?_ ?_ ⟨i, hiXᵣ⟩ (by simp [hi, hiXᵣ])
      · sorry
      · sorry

private lemma standardReprSum1_eq_disjointSum_untransposed_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ) (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 (((⊞ ((1 ⊟ Bₗ) ∘ Subtype.toSum) 0 0 ((1 ⊟ Bᵣ) ∘ Subtype.toSum)).toMatrixUnionUnion)) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range :=
  standardReprSum1_eq_disjointSum_untransposed_aux_aux (union_disjoint_union_aux hYY hXX hXY hYX) hYY _ _ hI hIₗ hIᵣ

lemma Disjoint.matrix_one_eq_fromBlocks_toMatrixUnionUnion {R : Type*} [Zero R] [One R]
    {Zₗ Zᵣ : Set α} [∀ a, Decidable (a ∈ Zₗ)] [∀ a, Decidable (a ∈ Zᵣ)]
    (hZZ : Zₗ ⫗ Zᵣ) :
    (1 : Matrix (Zₗ ∪ Zᵣ).Elem (Zₗ ∪ Zᵣ).Elem R) = (⊞ 1 0 0 1).toMatrixUnionUnion := by
  rw [Matrix.fromBlocks_one]
  ext i j
  cases hi : i.toSum with
  | inl iₗ =>
    cases hj : j.toSum with
    | inl jₗ =>
      if hij : i = j then
        simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
        have hii : iₗ.val = i.val := val_eq_val_of_toSum_eq_left hi
        have hjj : jₗ.val = j.val := val_eq_val_of_toSum_eq_left hj
        rw [hi, hj, hij, show iₗ = jₗ from Subtype.ext (hii ▸ hjj ▸ congr_arg Subtype.val hij)]
        simp only [Matrix.one_apply_eq]
      else
        simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
        rw [hi, hj, Matrix.one_apply_ne hij,
          Matrix.one_apply_ne (hij <| by simpa using congr_arg Sum.toUnion <| hi.trans · |>.trans hj.symm)]
    | inr jᵣ =>
      simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
      rw [hi, hj]
      have hij : i.val ≠ j.val
      · rw [←val_eq_val_of_toSum_eq_left hi, ←val_eq_val_of_toSum_eq_right hj]
        exact (hZZ.ni_left_of_in_right jᵣ.property <| · ▸ iₗ.property)
      simp [show i ≠ j from (hij <| congr_arg Subtype.val ·)]
  | inr iᵣ =>
    cases hj : j.toSum with
    | inl jₗ =>
      simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
      rw [hi, hj]
      have hij : i.val ≠ j.val
      · rw [←val_eq_val_of_toSum_eq_right hi, ←val_eq_val_of_toSum_eq_left hj]
        exact (hZZ.ni_left_of_in_right iᵣ.property <| · ▸ jₗ.property)
      simp [show i ≠ j from (hij <| congr_arg Subtype.val ·)]
    | inr jᵣ =>
      if hij : i = j then
        simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
        have hii : iᵣ.val = i.val := val_eq_val_of_toSum_eq_right hi
        have hjj : jᵣ.val = j.val := val_eq_val_of_toSum_eq_right hj
        rw [hi, hj, hij, show iᵣ = jᵣ from Subtype.ext (hii ▸ hjj ▸ congr_arg Subtype.val hij)]
        simp only [Matrix.one_apply_eq]
      else
        simp only [Matrix.toMatrixUnionUnion, Function.comp_apply]
        rw [hi, hj, Matrix.one_apply_ne hij,
          Matrix.one_apply_ne (hij <| by simpa using congr_arg Sum.toUnion <| hi.trans · |>.trans hj.symm)]

private lemma standardReprSum1_eq_disjointSum_untransposed {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hSₗ : Xₗ ⫗ Yₗ) (hSᵣ : Xᵣ ⫗ Yᵣ) (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ)
    (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ)) (hIₗ : I ∩ (Yₗ ∪ Xₗ) ⊆ Yₗ ∪ Xₗ) (hIᵣ : I ∩ (Yᵣ ∪ Xᵣ) ⊆ Yᵣ ∪ Xᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ) ∘ Subtype.toSum) hIᵣ.elem.range := by
  have hYXYX : Yₗ ∪ Xₗ ⫗ Yᵣ ∪ Xᵣ :=
    union_disjoint_union_aux hYY hXX hXY hYX
  have hYYXXYXYX : (Yₗ ∪ Yᵣ) ∪ (Xₗ ∪ Xᵣ) = (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ) :=
    Set.union_union_union_comm Yₗ Yᵣ Xₗ Xᵣ
  have hI' : I ⊆ (Yₗ ∪ Xₗ) ∪ (Yᵣ ∪ Xᵣ) := hYYXXYXYX ▸ hI
  rw [←standardReprSum1_eq_disjointSum_untransposed_aux hXX hYY hXY hYX Bₗ Bᵣ hI' hIₗ hIᵣ]
  apply linearIndepOn_matrix_elem_range_iff_subst hYYXXYXYX
  show _ = (⊞ ((1 ⊟ Bₗ) ∘ Subtype.toSum) 0 0 ((1 ⊟ Bᵣ) ∘ Subtype.toSum)).toMatrixElemElem hYYXXYXYX rfl
  ext i j
  have hBBij :
    ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion) ∘ Subtype.toSum) i j =
      (⊞ ((1 ⊟ Bₗ) ∘ Subtype.toSum) 0 0 ((1 ⊟ Bᵣ) ∘ Subtype.toSum)).toMatrixUnionUnion (hYYXXYXYX ▸ i) j
  · cases hi : i.toSum with
    | inl i₁ =>
      rw [hYY.matrix_one_eq_fromBlocks_toMatrixUnionUnion]
      cases hi₁ : i₁.toSum with
      | inl iₗ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = ◩⟨iₗ, Set.mem_union_left Xₗ iₗ.property⟩
        · have hiₗ : iₗ.val = i.val := (val_eq_val_of_toSum_eq_left hi₁).trans (val_eq_val_of_toSum_eq_left hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yₗ ∪ Xₗ := hiₗ ▸ Set.mem_union_left Xₗ iₗ.property
          simp [*]
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion, -Matrix.fromBlocks_one]
      | inr iᵣ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = ◪⟨iᵣ, Set.mem_union_left Xᵣ iᵣ.property⟩
        · have hiᵣ : iᵣ.val = i.val := (val_eq_val_of_toSum_eq_right hi₁).trans (val_eq_val_of_toSum_eq_left hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yᵣ ∪ Xᵣ := hiᵣ ▸ Set.mem_union_left Xᵣ iᵣ.property
          have hi_' : i.val ∉ Yₗ ∪ Xₗ := hYXYX.ni_left_of_in_right hi''
          simp [*]
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion, -Matrix.fromBlocks_one]
    | inr i₂ =>
      cases hi₂ : i₂.toSum with
      | inl iₗ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = ◩⟨iₗ, Set.mem_union_right Yₗ iₗ.property⟩
        · have hiₗ : iₗ.val = i.val := (val_eq_val_of_toSum_eq_left hi₂).trans (val_eq_val_of_toSum_eq_right hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yₗ ∪ Xₗ := hiₗ ▸ Set.mem_union_right Yₗ iₗ.property
          simp [*]
        have hiₗ : iₗ.val ∉ Yₗ := hSₗ.ni_right_of_in_left iₗ.property
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion]
      | inr iᵣ =>
        have hi' : (hYYXXYXYX ▸ i).toSum = ◪⟨iᵣ, Set.mem_union_right Yᵣ iᵣ.property⟩
        · have hiᵣ : iᵣ.val = i.val := (val_eq_val_of_toSum_eq_right hi₂).trans (val_eq_val_of_toSum_eq_right hi)
          have hi' : (hYYXXYXYX ▸ i).val = i.val := i.subst_elem hYYXXYXYX
          have hi'' : i.val ∈ Yᵣ ∪ Xᵣ := hiᵣ ▸ Set.mem_union_right Yᵣ iᵣ.property
          have hi_' : i.val ∉ Yₗ ∪ Xₗ := hYXYX.ni_left_of_in_right hi''
          simp [*]
        have hiᵣ : iᵣ.val ∉ Yᵣ := hSᵣ.ni_right_of_in_left iᵣ.property
        cases hj : j.toSum <;> simp [*, Matrix.toMatrixUnionUnion]
  rewrite [hBBij, Matrix.toMatrixElemElem_apply]
  rfl

private lemma standardReprSum1_eq_disjointSum_aux_aux {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hSₗ : Xₗ ⫗ Yₗ) (hSᵣ : Xᵣ ⫗ Yᵣ) (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ)
    (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ (Xₗ ∪ Xᵣ) ∪ (Yₗ ∪ Yᵣ)) (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ) (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    LinearIndepOn Z2 ((1 ⊟ (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion.transpose) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range :=
  (⊞ Bₗ 0 0 Bᵣ).toMatrixUnionUnion_transpose ▸
  Matrix.fromBlocks_transpose .. ▸
  standardReprSum1_eq_disjointSum_untransposed hSₗ.symm hSᵣ.symm hYY hXX hYX hXY Bₗ.transpose Bᵣ.transpose hI hIₗ hIᵣ

private lemma standardReprSum1_eq_disjointSum_aux {Xₗ Yₗ Xᵣ Yᵣ X Y I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hSₗ : Xₗ ⫗ Yₗ) (hSᵣ : Xᵣ ⫗ Yᵣ) (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (hXY : Xₗ ⫗ Yᵣ) (hYX : Yₗ ⫗ Xᵣ)
    (hXXX : X = Xₗ ∪ Xᵣ) (hYYY : Y = Yₗ ∪ Yᵣ) (Bₗ : Matrix Xₗ Yₗ Z2) (Bᵣ : Matrix Xᵣ Yᵣ Z2)
    (hI : I ⊆ X ∪ Y) (hIₗ : I ∩ (Xₗ ∪ Yₗ) ⊆ Xₗ ∪ Yₗ) (hIᵣ : I ∩ (Xᵣ ∪ Yᵣ) ⊆ Xᵣ ∪ Yᵣ) :
    have : ∀ a : α, Decidable (a ∈ X) := hXXX ▸ (Set.decidableUnion Xₗ Xᵣ ·)
    have : ∀ a : α, Decidable (a ∈ Y) := hYYY ▸ (Set.decidableUnion Yₗ Yᵣ ·)
    LinearIndepOn Z2 ((1 ⊟ ((⊞ Bₗ 0 0 Bᵣ).toMatrixElemElem hXXX hYYY).transpose) ∘ Subtype.toSum) hI.elem.range ↔
      LinearIndepOn Z2 ((1 ⊟ Bₗ.transpose) ∘ Subtype.toSum) hIₗ.elem.range ∧
      LinearIndepOn Z2 ((1 ⊟ Bᵣ.transpose) ∘ Subtype.toSum) hIᵣ.elem.range := by
  subst hXXX hYYY
  convert standardReprSum1_eq_disjointSum_aux_aux hSₗ hSᵣ hXX hYY hXY hYX Bₗ Bᵣ hI hIₗ hIᵣ

lemma standardReprSum1_eq_disjointSum {Sₗ Sᵣ S : StandardRepr α Z2} {hXY : Sₗ.X ⫗ Sᵣ.Y} {hYX : Sₗ.Y ⫗ Sᵣ.X}
    (hS : standardReprSum1 hXY hYX = some S) :
    S.toMatroid = (standardReprSum1_disjoint_E hS).matroidSum := by
  have hXXX := standardReprSum1_X_eq hS
  have hYYY := standardReprSum1_Y_eq hS
  simp only [standardReprSum1, Option.ite_none_right_eq_some] at hS
  ext I hIS
  · aesop
  · rw [Matroid.disjointSum_indep_iff]
    have hIEE : I ⊆ Sₗ.toMatroid.E ∪ Sᵣ.toMatroid.E
    · simpa [hXXX, hYYY, Set.union_comm, Set.union_left_comm] using hIS
    have hB : S.B = (⊞ Sₗ.B 0 0 Sᵣ.B).toMatrixElemElem hXXX hYYY
    · aesop
    simp_rw [hIEE]
    simp [show I ⊆ S.X ∪ S.Y from hIS]
    convert standardReprSum1_eq_disjointSum_aux Sₗ.hXY Sᵣ.hXY hS.left.left hS.left.right hXY hYX hXXX hYYY Sₗ.B Sᵣ.B hIS _ _

/-- The 1-sum of matroids is a disjoint sum of those matroids. -/
theorem Matroid.IsSum1of.eq_disjointSum {M Mₗ Mᵣ : Matroid α} (hMMM : M.IsSum1of Mₗ Mᵣ) :
    M = hMMM.disjoint_E.matroidSum := by
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
