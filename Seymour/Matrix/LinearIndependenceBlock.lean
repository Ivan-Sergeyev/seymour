import Seymour.Basic.Sets
import Seymour.Matrix.Conversions

/-!
# Linear Independence and Block Matrices

This file provides lemmas about linear independence in the context of block-like matrices.
-/

variable {α R : Type*}

lemma Disjoint.matrix_one_eq_fromBlocks_toMatrixUnionUnion [DecidableEq α] [Zero R] [One R]
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

lemma Matrix.linearIndepOn_iff_fromCols_zero [Ring R] {X Y I : Set α} (A : Matrix X Y R) (hIX : I ∩ X ⊆ X) (Y₀ : Set α)  :
    LinearIndepOn R A hIX.elem.range ↔ LinearIndepOn R (A ◫ (0 : Matrix X Y₀ R)) hIX.elem.range := by
  simp only [linearIndepOn_iff']
  constructor
  <;> intros h0 s c hs hsc0 x hx
  · apply h0
    · apply hs
    · ext y
      simpa using congr_fun hsc0 ◩y
    · exact hx
  · apply h0
    · apply hs
    · ext j
      cases j with
      | inr => simp
      | inl jₗ =>
        simpa [Finset.sum_apply, Pi.smul_apply] using congr_fun hsc0 jₗ
    · simpa using hx

lemma Matrix.linearIndepOn_iff_zero_fromCols [Ring R] {X Y I : Set α} (A : Matrix X Y R) (hIX : I ∩ X ⊆ X) (Y₀ : Set α)  :
    LinearIndepOn R A hIX.elem.range ↔ LinearIndepOn R ((0 : Matrix X Y₀ R) ◫ A) hIX.elem.range := by
  rw [A.linearIndepOn_iff_fromCols_zero hIX Y₀]
  constructor
  <;> [let l : (Y₀ ⊕ Y → R) →ₗ[R] (Y ⊕ Y₀ → R) := ⟨⟨(· <| Sum.swap ·), ↓↓rfl⟩, ↓↓rfl⟩;
       let l : (Y ⊕ Y₀ → R) →ₗ[R] (Y₀ ⊕ Y → R) := ⟨⟨(· <| Sum.swap ·), ↓↓rfl⟩, ↓↓rfl⟩]
  <;> convert LinearIndepOn.of_comp l
  <;> aesop

set_option maxHeartbeats 666666 in
lemma linearIndepOn_toMatrixUnionUnion_elem_range_iff [Ring R] {Xₗ Yₗ Xᵣ Yᵣ I : Set α}
    [∀ a, Decidable (a ∈ Xₗ)] [∀ a, Decidable (a ∈ Yₗ)] [∀ a, Decidable (a ∈ Xᵣ)] [∀ a, Decidable (a ∈ Yᵣ)]
    (hXX : Xₗ ⫗ Xᵣ) (hYY : Yₗ ⫗ Yᵣ) (Aₗ : Matrix Xₗ Yₗ R) (Aᵣ : Matrix Xᵣ Yᵣ R)
    (hI : I ⊆ Xₗ ∪ Xᵣ) (hIXₗ : I ∩ Xₗ ⊆ Xₗ) (hIXᵣ : I ∩ Xᵣ ⊆ Xᵣ) :
    LinearIndepOn R (((⊞ Aₗ 0 0 Aᵣ).toMatrixUnionUnion)) hI.elem.range ↔
      LinearIndepOn R Aₗ hIXₗ.elem.range ∧
      LinearIndepOn R Aᵣ hIXᵣ.elem.range := by
  rw [Aₗ.linearIndepOn_iff_fromCols_zero hIXₗ Yᵣ, Aᵣ.linearIndepOn_iff_zero_fromCols hIXᵣ Yₗ]
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
      specialize h0 (by
        simp_rw [Finset.coe_map, Set.image_subset_iff]
        apply hs.trans
        simp [HasSubset.Subset.elem_range])
      specialize h0 (by
        ext j
        simp [Matrix.toMatrixUnionUnion]
        convert congr_fun hsc0 j.toSum
        cases hj : j.toSum <;> simp [hj])
      simpa using h0 (hXₗ.elem i) (by simpa using hi)
    · specialize h0 (s.map hXᵣ.embed) (fun x : (Xₗ ∪ Xᵣ).Elem => if hx : x.val ∈ Xᵣ then c ⟨x.val, hx⟩ else 0)
      specialize h0 (by
        simp_rw [Finset.coe_map, Set.image_subset_iff]
        apply hs.trans
        simp [HasSubset.Subset.elem_range])
      specialize h0 (by
        ext j
        simp [Matrix.toMatrixUnionUnion]
        convert congr_fun hsc0 j.toSum
        cases hj : j.toSum <;> simp [hj, hXX.ni_left_of_in_right])
      simpa using h0 (hXᵣ.elem i) (by simpa using hi)
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
        cases j with
        | inr => simp
        | inl jₗ =>
          have hsc0jₗ := congr_fun hsc0 (hYₗ.elem jₗ)
          rw [Pi.zero_apply, Finset.sum_apply] at hsc0jₗ ⊢
          have hXXjₗ : ∀ x : (Xₗ ∪ Xᵣ).Elem, (⊞ Aₗ 0 0 Aᵣ) x.toSum ◩jₗ = if hx : x.val ∈ Xₗ then Aₗ ⟨x.val, hx⟩ jₗ else 0
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
      · intro ⟨x, hxXₗ⟩ hxs
        simp at hxs
        use ⟨x, by simpa using hs hxs, hxXₗ⟩
        rfl
      · ext j
        cases j with
        | inl => simp
        | inr jᵣ =>
          have hsc0jᵣ := congr_fun hsc0 (hYᵣ.elem jᵣ)
          rw [Pi.zero_apply, Finset.sum_apply] at hsc0jᵣ ⊢
          have hXXjᵣ : ∀ x : (Xₗ ∪ Xᵣ).Elem, (⊞ Aₗ 0 0 Aᵣ) x.toSum ◪jᵣ = if hx : x.val ∈ Xᵣ then Aᵣ ⟨x.val, hx⟩ jᵣ else 0
          · intro x
            if hx : x.val ∈ Xᵣ then
              simp [hx, hXX.ni_left_of_in_right]
            else
              simp [hx, in_left_of_in_union_of_ni_right x.property]
          simp [Matrix.toMatrixUnionUnion, hXXjᵣ, Finset.sum_dite, hYY.ni_left_of_in_right] at hsc0jᵣ
          convert hsc0jᵣ
          exact Finset.sum_bij (↓⟨hXᵣ.elem ·, by simp_all⟩) (by simp) (by simp) (by aesop) (by simp)
