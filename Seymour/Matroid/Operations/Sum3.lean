import Seymour.Matroid.Notions.Regularity
import Seymour.Matroid.Operations.Sum2


variable {α : Type} [DecidableEq α]

section StandardMatrixDefinition

/-- The 3-sum composition of two matrices. -/
noncomputable def matrix3sumComposition_standard {β : Type} [Field β] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ : Matrix Xₗ Yₗ β) (Bᵣ : Matrix Xᵣ Yᵣ β) (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x'}).Elem) ((Yₗ \ {y'}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) β × Prop :=
  -- row membership
  have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
  have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
  have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
  have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
  have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
  have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
  -- column membership
  have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
  have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
  have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
  have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
  have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
  have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
  -- top left submatrix
  let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem β := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem β := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- pieces of bottom left submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) β :=
    !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) β :=
    !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
  let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem β :=
    ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
  let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) β :=
    Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
  let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem β := Dᵣ * D₀ₗ⁻¹ * Dₗ
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) β := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
  -- reindexing for bottom left submatrix
  have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := j
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  -- final bottom left submatrix
  let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem β := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
  -- actual definition
  ⟨
    -- 3-sum defined as a block matrix
    Matrix.fromBlocks Aₗ 0 D Aᵣ,
    -- the special elements are all distinct
    (x₀ ≠ x₁ ∧ x₀ ≠ x' ∧ x₁ ≠ x' ∧ y₀ ≠ y₁ ∧ y₀ ≠ y' ∧ y₁ ≠ y')
    -- index sets of rows and columns do not overlap
    ∧ (Xₗ ⫗ Yₗ ∧ Xₗ ⫗ Yᵣ ∧ Xᵣ ⫗ Yₗ ∧ Xᵣ ⫗ Yᵣ)
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ D₀ₗ = D₀ᵣ
    -- `D₀` has the correct form
    ∧ (D₀ₗ = 1 ∨ D₀ₗ = !![1, 1; 0, 1])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y', y'inYₗ⟩ = 1
    ∧ Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y', y'inYₗ⟩ = 1
    ∧ Bₗ ⟨x', x'inXₗ⟩ ⟨y₀, y₀inYₗ⟩ = 1
    ∧ Bₗ ⟨x', x'inXₗ⟩ ⟨y₁, y₁inYₗ⟩ = 1
    ∧ (∀ x, ∀ hx : x ∈ Xₗ, x ≠ x₀ ∧ x ≠ x₁ → Bₗ ⟨x, hx⟩ ⟨y', y'inYₗ⟩ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y', y'inYᵣ⟩ = 1
    ∧ Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y', y'inYᵣ⟩ = 1
    ∧ Bᵣ ⟨x', x'inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩ = 1
    ∧ Bᵣ ⟨x', x'inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩ = 1
    ∧ (∀ y, ∀ hy : y ∈ Yᵣ, y ≠ y₀ ∧ y ≠ y₁ → Bᵣ ⟨x', x'inXᵣ⟩ ⟨y, hy⟩ = 0)
  ⟩

-- todo: lemmas about parts of the correctness Prop

end StandardMatrixDefinition


section CanonicalSigning

-- motivates the difference between the definition of 3-sum in our implementation and in Truemper's book
private lemma Matrix.Z2_2x2_nonsingular_form (Q : Matrix (Fin 2) (Fin 2) Z2) (hQ : IsUnit Q) :
    ∃ f : Fin 2 ≃ Fin 2, ∃ g : Fin 2 ≃ Fin 2, Q.submatrix f g = 1 ∨ Q.submatrix f g = !![1, 1; 0, 1] := by
  sorry

-- converts a TU signing of a summand of 3-sum to a canonical TU signing
private def Matrix.toCanonicalSigning {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y) :
    Matrix X Y ℚ :=
  let u : X → ℚ := (fun i =>
    if i = x₀ then Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ * Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ else
    if i = x₁ then Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ * Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩ * Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩ * Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ else
    if i = x' then 1 else
    1)
  let v : Y → ℚ := (fun j =>
    if j = y₀ then Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ else
    if j = y₁ then Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ else
    if j = y' then Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ * Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩ * Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ else
    1)
  Matrix.of (fun i j => Q i j * u i * v j)

lemma Matrix.toCanonicalSigning_TU {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    (Q.toCanonicalSigning hx₀ hx₁ hx' hy₀ hy₁ hy').IsTotallyUnimodular :=
  -- multiplying rows and columns by ±1 factors preserves TUness
  sorry

lemma Matrix.toCanonicalSigning_Form_Case1 {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular)
    (hQsub : Matrix.abs !![
      Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
      Q ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
      Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q ⟨x', hx'⟩ ⟨y', hy'⟩
    ] = !![1, 0, 1; 0, 1, 1; 1, 1, 0]) :
    let Q' := Q.toCanonicalSigning hx₀ hx₁ hx' hy₀ hy₁ hy'
    !![
      Q' ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q' ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q' ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
      Q' ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q' ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q' ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
      Q' ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q' ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q' ⟨x', hx'⟩ ⟨y', hy'⟩
    ] = !![1, 0, 1; 0, -1, 1; 1, 1, 0] :=
  -- see proof of Lemma 12 in the write-up on 3-sum, the case where D₀ is 1
  sorry

lemma Matrix.toCanonicalSigning_Form_Case2 {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular)
    (hQsub : Matrix.abs !![
      Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
      Q ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
      Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q ⟨x', hx'⟩ ⟨y', hy'⟩
    ] = !![1, 1, 1; 0, 1, 1; 1, 1, 0]) :
    let Q' := Q.toCanonicalSigning hx₀ hx₁ hx' hy₀ hy₁ hy'
    !![
      Q' ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q' ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q' ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
      Q' ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q' ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q' ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
      Q' ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q' ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q' ⟨x', hx'⟩ ⟨y', hy'⟩
    ] = !![1, 1, 1; 0, 1, 1; 1, 1, 0] :=
  -- see proof of Lemma 12 in the write-up on 3-sum, the case where D₀ is !![1, 1; 0, 1] (up to indices)
  sorry

-- lemma 15.a
-- todo: replace `Matrix.fromCols` with `◫`;
-- curretly `◫` does not work because category theory is imorted somewhere in the project
lemma Matrix.toCanonicalSigning_ExpandColsTU_a {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Matrix.fromCols (Matrix.fromCols Q' (▮c₀)) ((▮c₀) - (▮c₁))).IsTotallyUnimodular :=
  sorry

-- lemma 15.b
lemma Matrix.toCanonicalSigning_ExpandColsTU_b {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Matrix.fromCols (Matrix.fromCols Q' (▮c₁)) ((▮c₀) - (▮c₁))).IsTotallyUnimodular :=
  sorry

-- lemma 16.1
lemma Matrix.toCanonicalSigning_SpecialColsForm {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    ∀ i, ![c₀ i, c₁ i] ≠ ![1, -1] ∧ ![c₀ i, c₁ i] ≠ ![-1, 1] :=
  sorry

-- lemma 16.2
lemma Matrix.toCanonicalSigning_ExpandColsTU {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols
      (Matrix.fromCols (Matrix.fromCols
        ((Matrix.fromCols (Matrix.fromCols Q' (▮c₀)) (▮(-c₀))))
      (▮c₁)) (▮(-c₁)))
    (▮(c₀ - c₁))) (▮(c₁ - c₀))) (▮0)).IsTotallyUnimodular :=
  sorry

-- todo: same lemmas for rows instead of columns, final lemma (18.2) is given below
lemma Matrix.toCanonicalSigning_ExpandRowsTU {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y)
    (hQ : Q.IsTotallyUnimodular) :
    let d₀ : (Y \ {y'}).Elem → ℚ := fun i => Q ⟨x₀, hx₀⟩ (Set.diff_subset.elem i)
    let d₁ : (Y \ {y'}).Elem → ℚ := fun i => Q ⟨x₁, hx₁⟩ (Set.diff_subset.elem i)
    let Q' : Matrix (X \ {x₀, x₁}).Elem (Y \ {y'}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Matrix.fromRows (Matrix.fromRows (Matrix.fromRows
      (Matrix.fromRows (Matrix.fromRows
        ((Matrix.fromRows (Matrix.fromRows Q' (▬d₀)) (▬(-d₀))))
      (▬d₁)) (▬(-d₁)))
    (▬(d₀ - d₁))) (▬(d₁ - d₀))) (▬0)).IsTotallyUnimodular :=
  sorry

-- canonical signing of 3-sum constructed from TU signings of summands
noncomputable def matrix3sumComposition_CanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ' : Matrix Xₗ Yₗ ℚ) (Bᵣ' : Matrix Xᵣ Yᵣ ℚ)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x'}).Elem) ((Yₗ \ {y'}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) ℚ :=
  -- row membership
  have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
  have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
  have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
  have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
  have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
  have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
  have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
  -- column membership
  have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
  have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
  have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
  have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
  have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
  have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
  have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
  -- convert summands to canonical form
  let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
  let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
  -- top left submatrix
  let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- pieces of bottom left submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
    !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
    !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
  let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
    ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
  let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
    Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
  let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
  -- reindexing for bottom left submatrix
  have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := j
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  -- final bottom left submatrix
  let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
  -- actual definition
  Matrix.fromBlocks Aₗ 0 D Aᵣ


-- experimental lemmas and definitions that help state lemma 19
omit [DecidableEq α] in
lemma inter_three_mem₀ₗ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₀ ∈ Xₗ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_left (Set.mem_insert x₀ {x₁, x₂})

omit [DecidableEq α] in
lemma inter_three_mem₁ₗ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₁ ∈ Xₗ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_left (Set.insert_comm x₀ x₁ {x₂} ▸ Set.mem_insert x₁ {x₀, x₂})

omit [DecidableEq α] in
lemma inter_three_mem₂ₗ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₂ ∈ Xₗ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_left (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])

omit [DecidableEq α] in
lemma inter_three_mem₀ᵣ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₀ ∈ Xᵣ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_right (Set.mem_insert x₀ {x₁, x₂})

omit [DecidableEq α] in
lemma inter_three_mem₁ᵣ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₁ ∈ Xᵣ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_right (Set.insert_comm x₀ x₁ {x₂} ▸ Set.mem_insert x₁ {x₀, x₂})

omit [DecidableEq α] in
lemma inter_three_mem₂ᵣ {Xₗ Xᵣ : Set α} {x₀ x₁ x₂ : α} (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x₂}) : x₂ ∈ Xᵣ :=
  hXₗXᵣ.symm.subset.trans Set.inter_subset_right (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])

private def Matrix.special3x3Submatrix {X Y : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    (Q : Matrix X Y ℚ) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
    Q ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
    Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q ⟨x', hx'⟩ ⟨y', hy'⟩
  ]

private def Special3x3Submatrix_Case1_Unsigned : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
private def Special3x3Submatrix_Case1_Signed : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, -1, 1; 1, 1, 0]
private def Special3x3Submatrix_Case2_Unsigned : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
private def Special3x3Submatrix_Case2_Signed : Matrix (Fin 3) (Fin 3) ℚ := Special3x3Submatrix_Case2_Unsigned


-- lemma 19.1
lemma matrix3sumComposition_CanonicalSigning_D_Eq_SumOuterProducts {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ'sub : Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned)
    (hBᵣ'sub : Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned) :
    -- row membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
    have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
    -- column membership
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
    have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := i
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := j
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₁, y₁inYᵣ⟩
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₀, x₀inXₗ⟩ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₁, x₁inXₗ⟩ (Set.diff_subset.elem i)
    let D₀_unsigned :=
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
        (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ))
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then -d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ - d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    -- actual statement
    D = (c₀ · * r₀ ·) + (c₁ · * r₁ ·) :=
  sorry

-- lemma 19.2
lemma matrix3sumComposition_CanonicalSigning_D_Rows {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ'sub : Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned)
    (hBᵣ'sub : Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned) :
    -- row membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
    have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
    -- column membership
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
    have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := i
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := j
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₁, y₁inYᵣ⟩
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₀, x₀inXₗ⟩ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₁, x₁inXₗ⟩ (Set.diff_subset.elem i)
    let D₀_unsigned :=
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
        (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ))
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then -d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ - d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    -- actual statement
    ∀ i, D i = r₀ ∨ D i = -r₀ ∨ D i = r₁ ∨ D i = -r₁ ∨ D i = r₂ ∨ D i = -r₂ ∨ D i = 0 :=
  sorry

-- lemma 19.3
lemma matrix3sumComposition_CanonicalSigning_D_Cols {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ'sub : Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned)
    (hBᵣ'sub : Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned) :
    -- row membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
    have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
    -- column membership
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
    have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := i
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := j
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₁, y₁inYᵣ⟩
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₀, x₀inXₗ⟩ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₁, x₁inXₗ⟩ (Set.diff_subset.elem i)
    let D₀_unsigned :=
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
        (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ))
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then -d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ - d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    -- actual statement
    ∀ j, (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀ ∨ (D · j) = 0 :=
  sorry

-- lemma 19.5
lemma matrix3sumComposition_CanonicalSigning_Aᵣ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ'sub : Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned)
    (hBᵣ'sub : Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned) :
    -- row membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
    have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
    -- column membership
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
    have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := i
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := j
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₁, y₁inYᵣ⟩
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₀, x₀inXₗ⟩ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₁, x₁inXₗ⟩ (Set.diff_subset.elem i)
    let D₀_unsigned :=
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
        (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ))
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then -d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ - d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    -- actual statement
    (Matrix.fromCols Aᵣ D).IsTotallyUnimodular :=
  sorry

-- lemma 19.7
lemma matrix3sumComposition_CanonicalSigning_Aₗ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ'sub : Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
      (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned)
    (hBᵣ'sub : Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case1_Unsigned ∨
      Matrix.abs (Bᵣ'.special3x3Submatrix (inter_three_mem₀ᵣ hXₗXᵣ) (inter_three_mem₁ᵣ hXₗXᵣ) (inter_three_mem₂ᵣ hXₗXᵣ)
      (inter_three_mem₀ᵣ hYₗYᵣ) (inter_three_mem₁ᵣ hYₗYᵣ) (inter_three_mem₂ᵣ hYₗYᵣ)) = Special3x3Submatrix_Case2_Unsigned) :
    -- row membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have hrXᵣ : {x₀, x₁, x'} ⊆ Xᵣ := hXₗXᵣ.symm.subset.trans Set.inter_subset_right
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₀inXᵣ : x₀ ∈ Xᵣ := hrXᵣ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x₁inXᵣ : x₁ ∈ Xᵣ := hrXᵣ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have x'inXₗ : x' ∈ Xₗ := hrXₗ (by simp)
    have x'inXᵣ : x' ∈ Xᵣ := hrXᵣ (by simp)
    -- column membership
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y'inYₗ : y' ∈ Yₗ := hcYₗ (by simp)
    have y'inYᵣ : y' ∈ Yᵣ := hcYᵣ (by simp)
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀inXₗ x₁inXₗ x'inXₗ y₀inYₗ y₁inYₗ y'inYₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀inXᵣ x₁inXᵣ x'inXᵣ y₀inYᵣ y₁inYᵣ y'inYᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ :=
      !![Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₀, x₀inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩; Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₀, y₀inYᵣ⟩, Bᵣ ⟨x₁, x₁inXᵣ⟩ ⟨y₁, y₁inYᵣ⟩]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem, Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩, Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := Matrix.fromBlocks Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    have fXᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := i
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    have fYₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      False.elim (by
        simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
        obtain ⟨_, _⟩ := j
        simp_all only
        simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := Matrix.of (fun i j => D' (fXᵣ i) (fYₗ j))
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) ⟨y₁, y₁inYᵣ⟩
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₀, x₀inXₗ⟩ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ ⟨x₁, x₁inXₗ⟩ (Set.diff_subset.elem i)
    let D₀_unsigned :=
      Matrix.abs (Bₗ'.special3x3Submatrix (inter_three_mem₀ₗ hXₗXᵣ) (inter_three_mem₁ₗ hXₗXᵣ) (inter_three_mem₂ₗ hXₗXᵣ)
        (inter_three_mem₀ₗ hYₗYᵣ) (inter_three_mem₁ₗ hYₗYᵣ) (inter_three_mem₂ₗ hYₗYᵣ))
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then -d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₁ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀_case1: D₀_unsigned = Special3x3Submatrix_Case1_Unsigned then d₀ - d₁ else
      if hD₀_case2: D₀_unsigned = Special3x3Submatrix_Case2_Unsigned then d₀ else
      (False.elim (by
        simp_all only [D₀_unsigned]
        cases hBₗ'sub with
        | inl h => simp_all only [not_true_eq_false, D₀_unsigned]
        | inr h_1 => simp_all only [not_true_eq_false, D₀_unsigned]))
    -- actual statement
    (Matrix.fromRows Aₗ D).IsTotallyUnimodular :=
  sorry

end CanonicalSigning

section Regularity

end Regularity



section AlternativeMatrixDefinition

omit [DecidableEq α] in
/-- Alternative definition of 3-sum composition using sum of two outer products of vectors to define bottom left submatrix. -/
def matrix3sumCompositionAlt {β : Type} [CommRing β] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ β) (Aᵣ : Matrix Xᵣ Yᵣ β) (r₀ : Yₗ → β) (r₁ : Yₗ → β) (c₀ : Xᵣ → β) (c₁ : Xᵣ → β) :
    Matrix (Xₗ ⊕ Xᵣ) (Yₗ ⊕ Yᵣ) β :=
  Matrix.fromBlocks Aₗ 0 ((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) Aᵣ

omit [DecidableEq α] in
private lemma matrix3sumCompositionAlt_eq_fromRows {β : Type} [CommRing β] {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ β) (Aᵣ : Matrix Xᵣ Yᵣ β) (r₀ : Yₗ → β) (r₁ : Yₗ → β) (c₀ : Xᵣ → β) (c₁ : Xᵣ → β) :
    matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁ = (Aₗ ◫ 0) ⊟ (((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) ◫ Aᵣ) := by
  rfl

private lemma matrix3sumCompositionAlt_isPreTU_1 {α : Type} {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {r₀ : Yₗ → ℚ} {r₁ : Yₗ → ℚ} {c₀ : Xᵣ → ℚ} {c₁ : Xᵣ → ℚ}
    (hAₗ : (▬r₀ ⊟ ▬r₁ ⊟ Aₗ).IsTotallyUnimodular) (hAᵣ : (▮c₀ ◫ ▮c₁ ◫ Aᵣ).IsTotallyUnimodular)
    (hcc : ∀ i : Xᵣ, (c₀ - c₁) i ∈ SignType.cast.range) (hrr : ∀ j : Yₗ, (r₀ + r₁) j ∈ SignType.cast.range) :
    (matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁).IsPreTU 1 := by
  intro f g
  rw [Matrix.det_unique, Fin.default_eq_zero, Matrix.submatrix_apply]
  have hAₗ : Aₗ.IsTotallyUnimodular := hAₗ.comp_rows Sum.inr
  have hAᵣ : Aᵣ.IsTotallyUnimodular := hAᵣ.comp_cols Sum.inr
  cases f 0 with
  | inl i₁ => cases g 0 with
    | inl j₁ => exact hAₗ.apply i₁ j₁
    | inr j₂ => exact zero_in_signTypeCastRange
  | inr i₂ => cases g 0 with
    | inl j₁ =>
      unfold matrix3sumCompositionAlt
      rw [Matrix.fromBlocks_apply₂₁, Pi.add_apply, Pi.add_apply]
      -- todo: follows from `c₀`, `c₁`, `c₀ - c₁`, `r₀`, `r₁`, `r₀ + r₁` all being {0, ±1} vectors
      sorry
    | inr j₂ => exact hAᵣ.apply i₂ j₂

/-
Does not hold!
Counterexample:
`Aᵣ := !![0]`
`c₀ := ![1]`
`c₁ := ![1]`
-/
private lemma matrix3sumCompositionAlt_bottom_isTotallyUnimodular_aux {Xᵣ Yᵣ : Set α}
    {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {c₀ : Xᵣ → ℚ} {c₁ : Xᵣ → ℚ}
    (hAᵣ : (▮c₀ ◫ ▮c₁ ◫ Aᵣ).IsTotallyUnimodular) (hcc : ∀ i : Xᵣ, (c₀ - c₁) i ∈ SignType.cast.range) :
    (▮0 ◫ ▮(-c₀-c₁) ◫ ▮(c₀-c₁) ◫ ▮(c₁-c₀) ◫ ▮(c₀+c₁) ◫ ▮(-c₀) ◫ ▮(-c₁) ◫ ▮c₀ ◫ ▮c₁ ◫ Aᵣ).IsTotallyUnimodular := by
  sorry

attribute [local simp] neg_add_eq_sub in
attribute [local simp ←] sub_eq_add_neg in
set_option maxHeartbeats 500000 in
/-- In our settings `D ◫ Aᵣ` is totally unimodular.-/
private lemma matrix3sumCompositionAlt_bottom_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {r₀ : Yₗ → ℚ} {r₁ : Yₗ → ℚ} {c₀ : Xᵣ → ℚ} {c₁ : Xᵣ → ℚ}
    (hAₗ : (▬r₀ ⊟ ▬r₁ ⊟ Aₗ).IsTotallyUnimodular) (hAᵣ : (▮c₀ ◫ ▮c₁ ◫ Aᵣ).IsTotallyUnimodular)
    (hcc : ∀ i : Xᵣ, (c₀ - c₁) i ∈ SignType.cast.range) :
    (((c₀ · * r₀ ·) + (c₁ · * r₁ ·)) ◫ Aᵣ).IsTotallyUnimodular := by
  convert
    (matrix3sumCompositionAlt_bottom_isTotallyUnimodular_aux hAᵣ hcc).submatrix id
      (fun y : Yₗ.Elem ⊕ Yᵣ.Elem => y.casesOn
        (fun y' =>
          match hs₀ : (hAₗ.apply ◩◩() y').choose with
          | .zero =>
            match hs₁ : (hAₗ.apply ◩◪() y').choose with
            | .zero => ◩◩◩◩◩◩◩◩◩()
            | .pos => ◩◪()
            | .neg => ◩◩◩◪()
          | .pos =>
            match hs₁ : (hAₗ.apply ◩◪() y').choose with
            | .zero => ◩◩◪()
            | .pos => ◩◩◩◩◩◪()
            | .neg => ◩◩◩◩◩◩◩◪()
          | .neg =>
            match hs₁ : (hAₗ.apply ◩◪() y').choose with
            | .zero => ◩◩◩◩◪()
            | .pos => ◩◩◩◩◩◩◪()
            | .neg => ◩◩◩◩◩◩◩◩◪()
        )
        Sum.inr
      )
  ext i j
  cases j with
  | inl j' =>
    cases hs₀ : (hAₗ.apply ◩◩() j').choose with
    | zero =>
      cases hs₁ : (hAₗ.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = 0
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
    | pos =>
      cases hs₁ : (hAₗ.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = 1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
    | neg =>
      cases hs₁ : (hAₗ.apply ◩◪() j').choose with
      | zero =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 0
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | pos =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = 1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
      | neg =>
        have hr₀ : r₀ j' = -1
        · simpa [hs₀] using (hAₗ.apply ◩◩() j').choose_spec.symm
        have hr₁ : r₁ j' = -1
        · simpa [hs₁] using (hAₗ.apply ◩◪() j').choose_spec.symm
        aesop
  | inr => simp

/-- Expresses how row vector of first outer product changes after pivot in `Aₗ`. -/
private def matrix3sumCompositionAlt_pivotAₗ_Dr₀ {Xₗ Yₗ Xᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r₀ : Yₗ → ℚ) (r₁ : Yₗ → ℚ) (c₀ : Xᵣ → ℚ) (c₁ : Xᵣ → ℚ)
    {i : Xₗ} {j : Yₗ} (hij : Aₗ i j = 1 ∨ Aₗ i j = -1) : Yₗ → ℚ :=
  -- todo: find explicit formula
  sorry

/-- Expresses how row vector of second outer product changes after pivot in `Aₗ`. -/
private def matrix3sumCompositionAlt_pivotAₗ_Dr₁ {Xₗ Yₗ Xᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r₀ : Yₗ → ℚ) (r₁ : Yₗ → ℚ) (c₀ : Xᵣ → ℚ) (c₁ : Xᵣ → ℚ)
    {i : Xₗ} {j : Yₗ} (hij : Aₗ i j = 1 ∨ Aₗ i j = -1) : Yₗ → ℚ :=
  -- todo: find explicit formula
  sorry

private lemma matrix3sumCompositionAlt_pivotAₗ_Dr₀r₁_properties_preserved {Xₗ Yₗ Xᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (r₀ : Yₗ → ℚ) (r₁ : Yₗ → ℚ) (c₀ : Xᵣ → ℚ) (c₁ : Xᵣ → ℚ)
    {i : Xₗ} {j : Yₗ} (hij : Aₗ i j = 1 ∨ Aₗ i j = -1)
    (hAₗ : (▬r₀ ⊟ ▬r₁ ⊟ Aₗ).IsTotallyUnimodular) (hAᵣ : (▮c₀ ◫ ▮c₁).IsTotallyUnimodular)
    (hc₀c₁ : ∀ i, (c₀ - c₁) i ∈ SignType.cast.range) (hr₀r₁ : ∀ j, (r₀ + r₁) j ∈ SignType.cast.range) :
    let r₀' : Yₗ → ℚ := matrix3sumCompositionAlt_pivotAₗ_Dr₀ Aₗ r₀ r₁ c₀ c₁ hij
    let r₁' : Yₗ → ℚ := matrix3sumCompositionAlt_pivotAₗ_Dr₁ Aₗ r₀ r₁ c₀ c₁ hij
    (▬r₀' ⊟ ▬r₁' ⊟ Aₗ).IsTotallyUnimodular ∧ ∀ j, (r₀' + r₁') j ∈ SignType.cast.range := by
  sorry

private lemma matrix3sumCompositionAlt_shortTableauPivot {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    (Aₗ : Matrix Xₗ Yₗ ℚ) (Aᵣ : Matrix Xᵣ Yᵣ ℚ) (r₀ : Yₗ → ℚ) (r₁ : Yₗ → ℚ) (c₀ : Xᵣ → ℚ) (c₁ : Xᵣ → ℚ)
    {i : Xₗ} {j : Yₗ} (hij : Aₗ i j = 1 ∨ Aₗ i j = -1) :
    let B := (matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁)
    let r₀' : Yₗ → ℚ := matrix3sumCompositionAlt_pivotAₗ_Dr₀ Aₗ r₀ r₁ c₀ c₁ hij
    let r₁' : Yₗ → ℚ := matrix3sumCompositionAlt_pivotAₗ_Dr₁ Aₗ r₀ r₁ c₀ c₁ hij
    B.shortTableauPivot ◩i ◩j = matrix3sumCompositionAlt (Aₗ.shortTableauPivot i j) Aᵣ r₀' r₁' c₀ c₁ := by
  intro B r₀' r₁'
  have hBAₗ : (B.shortTableauPivot ◩i ◩j).toBlocks₁₁ = Aₗ.shortTableauPivot i j
  · exact (B.submatrix_shortTableauPivot Sum.inl_injective Sum.inl_injective i j).symm
  have hB0 : (B.shortTableauPivot ◩i ◩j).toBlocks₁₂ = 0
  · ext i' j'
    exact B.shortTableauPivot_zero i ◩j Sum.inl Sum.inr (by simp) (by simp [matrix3sumCompositionAlt, B]) i' j'
  have hBD : (B.shortTableauPivot ◩i ◩j).toBlocks₂₁ = ((c₀ · * r₀' ·) + (c₁ · * r₁' ·))
  · sorry
  have hBAᵣ : (B.shortTableauPivot ◩i ◩j).toBlocks₂₂ = Aᵣ
  · exact B.shortTableauPivot_submatrix_zero_external_row ◩i ◩j Sum.inr Sum.inr (by simp) (by simp) (fun _ => rfl)
  rw [←(B.shortTableauPivot ◩i ◩j).fromBlocks_toBlocks, hBAₗ, hB0, hBD, hBAᵣ]
  rfl

private lemma matrix3sumCompositionAlt_isTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Set α}
    {Aₗ : Matrix Xₗ Yₗ ℚ} {Aᵣ : Matrix Xᵣ Yᵣ ℚ} {r₀ : Yₗ → ℚ} {r₁ : Yₗ → ℚ} {c₀ : Xᵣ → ℚ} {c₁ : Xᵣ → ℚ}
    (hrrAₗ : (▬r₀ ⊟ ▬r₁ ⊟ Aₗ).IsTotallyUnimodular) (hccAᵣ : (▮c₀ ◫ ▮c₁ ◫ Aᵣ).IsTotallyUnimodular)
    (hcc : ∀ i : Xᵣ, (c₀ - c₁) i ∈ SignType.cast.range) (hrr : ∀ j : Yₗ, (r₀ + r₁) j ∈ SignType.cast.range) :
    (matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff_forall_IsPreTU]
  intro k
  cases k with
  | zero => simp [Matrix.IsPreTU]
  | succ m => induction m generalizing Aₗ Aᵣ r₀ r₁ c₀ c₁ with
    | zero => exact matrix3sumCompositionAlt_isPreTU_1 hrrAₗ hccAᵣ hcc hrr
    | succ n ih =>
      have hAₗ : Aₗ.IsTotallyUnimodular := hrrAₗ.comp_rows Sum.inr
      have hAᵣ : Aᵣ.IsTotallyUnimodular := hccAᵣ.comp_cols Sum.inr
      by_contra contr
      obtain ⟨f, g, hAfg⟩ := exists_submatrix_of_not_isPreTU contr
      wlog hf : f.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁).submatrix_det_zero_of_not_injective_left hf
      wlog hg : g.Injective
      · apply hAfg
        convert zero_in_signTypeCastRange
        exact (matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁).submatrix_det_zero_of_not_injective_right hg
      obtain ⟨i₁, x₁, hix₁⟩ : ∃ i₁ : Fin (n + 2), ∃ x₁ : Xₗ, f i₁ = ◩x₁
      · have isTU := matrix3sumCompositionAlt_bottom_isTotallyUnimodular hrrAₗ hccAᵣ hcc
        rw [Matrix.isTotallyUnimodular_iff] at isTU
        rw [matrix3sumCompositionAlt_eq_fromRows] at hAfg
        by_contra! hfXₗ
        apply hAfg
        convert isTU (n + 2) (fn_of_sum_ne_inl hfXₗ) g using 2
        ext i j
        rewrite [Matrix.submatrix_apply, eq_of_fn_sum_ne_inl hfXₗ i]
        rfl
      obtain ⟨j₀, y₀, hjy₀, hAxy0⟩ : ∃ j₀ : Fin (n + 2), ∃ y₀ : Yₗ, g j₀ = ◩y₀ ∧ Aₗ x₁ y₀ ≠ 0
      · by_contra! hgYₗ -- because the `i₁`th row cannot be all `0`s
        apply hAfg
        convert zero_in_signTypeCastRange
        apply Matrix.det_eq_zero_of_row_eq_zero i₁
        intro z
        rw [matrix3sumCompositionAlt_eq_fromRows, Matrix.submatrix_apply, hix₁, Matrix.fromRows_apply_inl]
        cases hgz : g z with
        | inl => exact hgYₗ z _ hgz
        | inr => simp
      have hAxy1 : Aₗ x₁ y₀ = 1 ∨ Aₗ x₁ y₀ = -1
      · obtain ⟨s, hs⟩ := hAₗ.apply x₁ y₀
        cases s with
        | zero =>
          exfalso
          apply hAxy0
          exact hs.symm
        | pos =>
          left
          exact hs.symm
        | neg =>
          right
          exact hs.symm
      obtain ⟨f', g', -, -, impossible⟩ := corollary1 hAfg i₁ j₀ (by convert hAxy1 <;> simp [matrix3sumCompositionAlt, *])
      apply impossible
      rw [(matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁).submatrix_shortTableauPivot hf hg, Matrix.submatrix_submatrix,
        hix₁, hjy₀, matrix3sumCompositionAlt_shortTableauPivot Aₗ Aᵣ r₀ r₁ c₀ c₁ hAxy1]
      apply ih _ hccAᵣ hcc _
      · sorry
      · sorry

end AlternativeMatrixDefinition


section ConversionStandardAlternative

lemma matrix3sumComposition_standard_toAlt_eq {β : Type} [Field β] {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ : Matrix Xₗ Yₗ β) (Bᵣ : Matrix Xᵣ Yᵣ β) (hXₗXᵣ : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYₗYᵣ : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    {B} (hB : B = matrix3sumComposition_standard Bₗ Bᵣ hXₗXᵣ hYₗYᵣ) :
    -- question: what is the correct way to introduce `B`, so that we have access to both `B.fst` and `B.snd`?
    -- note: this definition doesn't make sense unless `B.snd` is satisfied
    -- for example, `Bₗ` and `Bᵣ` have to match on their intersection

    -- row and column membership
    have hrXₗ : {x₀, x₁, x'} ⊆ Xₗ := hXₗXᵣ.symm.subset.trans Set.inter_subset_left
    have x₀inXₗ : x₀ ∈ Xₗ := hrXₗ (Set.mem_insert x₀ {x₁, x'})
    have x₁inXₗ : x₁ ∈ Xₗ := hrXₗ (Set.insert_comm x₀ x₁ {x'} ▸ Set.mem_insert x₁ {x₀, x'})
    have hcYₗ : {y₀, y₁, y'} ⊆ Yₗ := hYₗYᵣ.symm.subset.trans Set.inter_subset_left
    have hcYᵣ : {y₀, y₁, y'} ⊆ Yᵣ := hYₗYᵣ.symm.subset.trans Set.inter_subset_right
    have y₀inYₗ : y₀ ∈ Yₗ := hcYₗ (Set.mem_insert y₀ {y₁, y'})
    have y₀inYᵣ : y₀ ∈ Yᵣ := hcYᵣ (Set.mem_insert y₀ {y₁, y'})
    have y₁inYₗ : y₁ ∈ Yₗ := hcYₗ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    have y₁inYᵣ : y₁ ∈ Yᵣ := hcYᵣ (Set.insert_comm y₀ y₁ {y'} ▸ Set.mem_insert y₁ {y₀, y'})
    -- take submatrices of Bₗ and Bᵣ
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem β := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem β := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- take columns from Bᵣ
    let c₀ : (Xᵣ \ {x'}).Elem → β := fun i => Bᵣ (Set.diff_subset.elem i) ⟨y₀, y₀inYᵣ⟩
    let c₁ : (Xᵣ \ {x'}).Elem → β := fun i => Bᵣ (Set.diff_subset.elem i) ⟨y₁, y₁inYᵣ⟩
    -- take rows of Bₗ, but multiplied by `D₀⁻¹` on the left
    let v₀ : (Yₗ \ {y'}).Elem → β := Bₗ ⟨x₀, x₀inXₗ⟩ ∘ Set.diff_subset.elem
    let v₁ : (Yₗ \ {y'}).Elem → β := Bₗ ⟨x₁, x₁inXₗ⟩ ∘ Set.diff_subset.elem
    let D₀ₗ : Matrix (Fin 2) (Fin 2) β :=
      !![Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₀, x₀inXₗ⟩ ⟨y₁, y₁inYₗ⟩; Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₀, y₀inYₗ⟩, Bₗ ⟨x₁, x₁inXₗ⟩ ⟨y₁, y₁inYₗ⟩]
    let r₀ : (Yₗ \ {y'}).Elem → β := fun i => (D₀ₗ⁻¹ 0 0) * (v₀ i) + (D₀ₗ⁻¹ 0 1) * (v₁ i)
    let r₁ : (Yₗ \ {y'}).Elem → β := fun i => (D₀ₗ⁻¹ 1 0) * (v₀ i) + (D₀ₗ⁻¹ 1 1) * (v₁ i)
    -- statement
    B.fst = matrix3sumCompositionAlt Aₗ Aᵣ r₀ r₁ c₀ c₁ := by
  intro _ _ _ _ _ _ _ _ _ Aₗ Aᵣ c₀ c₁ v₀ v₁ D₀ₗ r₀ r₁

  have hBₗ₁ : B.fst.toBlocks₁₁ = Aₗ := hB ▸ rfl
  have hBₗ₂ : B.fst.toBlocks₁₂ = 0 := hB ▸ rfl
  have hBᵣ₂ : B.fst.toBlocks₂₂ = Aᵣ := hB ▸ rfl

  have hBᵣ₁ : B.fst.toBlocks₂₁ = (c₀ · * r₀ ·) + (c₁ · * r₁ ·) := by
    rw [hB]
    unfold matrix3sumComposition_standard
    simp_all only [HasSubset.Subset.elem, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
      false_or, Matrix.toBlocks_fromBlocks₂₁]
    ext i j
    simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or,
      Matrix.of_apply, Pi.add_apply]
    -- todo: need to use properties from `B.snd`
    if hi : i = x₀ then
      if hj : j = y₀ then
        -- aesop
        sorry
      else
        sorry
    else
      sorry

  rw [←B.fst.fromBlocks_toBlocks, hBₗ₁, hBₗ₂, hBᵣ₁, hBᵣ₂]
  rfl

end ConversionStandardAlternative



section MatroidThreeSum

/-- The 3-sum composition of two binary matroids given by their stanard representations. -/
noncomputable def standardRepr3sumComposition_standard {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      (S₁.X \ {x₀, x₁}) ∪ (S₂.X \ {x'}),
      (S₁.Y \ {y'}) ∪ (S₂.Y \ {y₀, y₁}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨S₁.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, S₂.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (matrix3sumComposition_standard S₁.B S₂.B hXX hYY).fst.toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (matrix3sumComposition_standard S₁.B S₂.B hXX hYY).snd
  ⟩

lemma standardRepr3sumComposition_standard_X {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.X = (S₁.X \ {x₀, x₁}) ∪ (S₂.X \ {x'}) :=
  rfl

lemma standardRepr3sumComposition_standard_Y {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.Y = (S₁.Y \ {y'}) ∪ (S₂.Y \ {y₀, y₁}) :=
  rfl

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `M₁` and `M₂`. -/
structure Matroid.Is3sumOf (M : Matroid α) (M₁ M₂ : Matroid α) where
  S : StandardRepr α Z2
  S₁ : StandardRepr α Z2
  S₂ : StandardRepr α Z2
  hS₁ : Finite S₁.X
  hS₂ : Finite S₂.X
  hM : S.toMatroid = M
  hM₁ : S₁.toMatroid = M₁
  hM₂ : S₂.toMatroid = M₂
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : S₁.X ∩ S₂.X = {x₁, x₂, x₃}
  hYY : S₁.Y ∩ S₂.Y = {y₁, y₂, y₃}
  hXY : S₁.X ⫗ S₂.Y
  hYX : S₁.Y ⫗ S₂.X
  IsSum : (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition_standard hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M M₁ M₂ : Matroid α} (hM : M.Is3sumOf M₁ M₂) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_standard_X]
  apply Finite.Set.finite_union

lemma standardRepr3sumComposition_hasTuSigning {α : Type} [DecidableEq α] {S₁ S₂ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : S₁.X ∩ S₂.X = {x₀, x₁, x'}) (hYY : S₁.Y ∩ S₂.Y = {y₀, y₁, y'}) (hXY : S₁.X ⫗ S₂.Y) (hYX : S₁.Y ⫗ S₂.X)
    (hS₁ : S₁.HasTuSigning) (hS₂ : S₂.HasTuSigning) :
    ((standardRepr3sumComposition_standard hXX hYY hXY hYX).fst).HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hS₁
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hS₂
  -- use matrix3sumComposition_toCanonicalSigning
  sorry

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final of the three parts of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M M₁ M₂ : Matroid α}
    (hM : M.Is3sumOf M₁ M₂) (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hM₁ hM₂ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hM₁
  · exact hM₂

end MatroidThreeSum
