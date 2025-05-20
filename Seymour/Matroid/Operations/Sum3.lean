import Seymour.Matrix.Pivoting
import Seymour.Matroid.Properties.Regularity


variable {α : Type}

section members_of_intersection

variable {Zₗ Zᵣ : Set α} {a₀ a₁ a₂ : α}

private lemma Eq.mem3₀ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ₗ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zₗ :=
  hZZ.symm.subset.trans Set.inter_subset_left (by simp)

private lemma Eq.mem3₀ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₀ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.mem_insert a₀ {a₁, a₂})

private lemma Eq.mem3₁ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₁ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (Set.insert_comm a₀ a₁ {a₂} ▸ Set.mem_insert a₁ {a₀, a₂})

private lemma Eq.mem3₂ᵣ (hZZ : Zₗ ∩ Zᵣ = {a₀, a₁, a₂}) : a₂ ∈ Zᵣ :=
  hZZ.symm.subset.trans Set.inter_subset_right (by simp)

end members_of_intersection


-- ## The 3-sum of matrices

/-- The 3-sum composition of two matrices. -/
noncomputable def matrix3sumComposition_standard [DecidableEq α] {F : Type} [Field F]
    {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ : Matrix Xₗ Yₗ F) (Bᵣ : Matrix Xᵣ Yᵣ F) (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x'}).Elem) ((Yₗ \ {y'}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) F × Prop :=
  -- row membership
  let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
  let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
  let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
  let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
  let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
  let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
  -- column membership
  let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
  let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
  let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
  let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
  let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
  let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
  -- top left submatrix
  let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem F := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem F := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- pieces of bottom left submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) F := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) F := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
  let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem F :=
    ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
  let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) F :=
    Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
  let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem F := Dᵣ * D₀ₗ⁻¹ * Dₗ
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) F := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
  -- reindexing for bottom left submatrix
  let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
  let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
  -- final bottom left submatrix
  let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem F := D'.submatrix fᵣ fₗ
  -- actual definition
  ⟨
    -- 3-sum defined as a block matrix
    ⊞ Aₗ 0 D Aᵣ,
    -- the special elements are all distinct
    ((x₀ ≠ x₁ ∧ x₀ ≠ x' ∧ x₁ ≠ x') ∧ (y₀ ≠ y₁ ∧ y₀ ≠ y' ∧ y₁ ≠ y'))
    -- index sets of rows and columns do not overlap
    ∧ (Xₗ ⫗ Yₗ ∧ Xₗ ⫗ Yᵣ ∧ Xᵣ ⫗ Yₗ ∧ Xᵣ ⫗ Yᵣ)
    -- `D₀` is the same in `Bₗ` and `Bᵣ`
    ∧ D₀ₗ = D₀ᵣ
    -- `D₀` has the correct form
    ∧ (D₀ₗ = 1 ∨ D₀ₗ = !![1, 1; 0, 1])
    -- `Bₗ` has the correct structure outside of `Aₗ`, `Dₗ`, and `D₀`
    ∧ Bₗ x₀ₗ y'ₗ = 1
    ∧ Bₗ x₁ₗ y'ₗ = 1
    ∧ Bₗ x'ₗ y₀ₗ = 1
    ∧ Bₗ x'ₗ y₁ₗ = 1
    ∧ (∀ x, ∀ hx : x ∈ Xₗ, x ≠ x₀ ∧ x ≠ x₁ → Bₗ ⟨x, hx⟩ y'ₗ = 0)
    -- `Bᵣ` has the correct structure outside of `Aᵣ`, `Dᵣ`, and `D₀`
    ∧ Bᵣ x₀ᵣ y'ᵣ = 1
    ∧ Bᵣ x₁ᵣ y'ᵣ = 1
    ∧ Bᵣ x'ᵣ y₀ᵣ = 1
    ∧ Bᵣ x'ᵣ y₁ᵣ = 1
    ∧ (∀ y, ∀ hy : y ∈ Yᵣ, y ≠ y₀ ∧ y ≠ y₁ → Bᵣ x'ᵣ ⟨y, hy⟩ = 0)
  ⟩

-- todo: lemmas about parts of the correctness Prop


-- ## Lemmas

-- ## Submatrix 3×3

@[simp] private abbrev matrix3x3unsigned₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, 1, 1; 1, 1, 0]
@[simp] private abbrev matrix3x3unsigned₁ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[simp] private abbrev matrix3x3signed₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 0, -1, 1; 1, 1, 0]
@[simp] private abbrev matrix3x3signed₁ : Matrix (Fin 3) (Fin 3) ℚ := matrix3x3unsigned₁

@[simp]
private abbrev Matrix.submatrix3x3 {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q x₀ y₀, Q x₀ y₁, Q x₀ y';
    Q x₁ y₀, Q x₁ y₁, Q x₁ y';
    Q x' y₀, Q x' y₁, Q x' y']

private lemma submatrix3x3signed₀_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x' : X} {y₀ y₁ y' : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₀) :
    |Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y'| = matrix3x3unsigned₀ :=
  hQ ▸ |matrix3x3signed₀|.eta_fin_three

private lemma submatrix3x3signed₁_abs {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x' : X} {y₀ y₁ y' : Y}
    (hQ : Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₁) :
    |Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y'| = matrix3x3unsigned₁ :=
  hQ ▸ |matrix3x3signed₁|.eta_fin_three

private lemma Matrix.submatrix3x3_eq {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) :
    Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y' =
    Q.submatrix
      (match · with
        | 0 => x₀
        | 1 => x₁
        | 2 => x')
      (match · with
        | 0 => y₀
        | 1 => y₁
        | 2 => y') := by
  ext
  rw [Matrix.submatrix_apply]
  split <;> split <;> rfl

private lemma Matrix.IsTotallyUnimodular.submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) :
    (Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y').IsTotallyUnimodular := by
  rw [Matrix.submatrix3x3_eq]
  apply hQ.submatrix

-- we might need this, but later
private def Matrix.submatrix3x3mems {X Y : Set α} (Q : Matrix X Y ℚ)
    {x₀ x₁ x' y₀ y₁ y' : α} (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y) :
    Matrix (Fin 3) (Fin 3) ℚ :=
  !![
    Q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩, Q ⟨x₀, hx₀⟩ ⟨y₁, hy₁⟩, Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩;
    Q ⟨x₁, hx₁⟩ ⟨y₀, hy₀⟩, Q ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩, Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩;
    Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩, Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩, Q ⟨x', hx'⟩ ⟨y', hy'⟩]

private lemma Matrix.submatrix3x3mems_eq {X Y : Set α} (Q : Matrix X Y ℚ)
    {x₀ x₁ x' y₀ y₁ y' : α} (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy' : y' ∈ Y) :
    Q.submatrix3x3mems hx₀ hx₁ hx' hy₀ hy₁ hy' =
    Q.submatrix3x3 ⟨x₀, hx₀⟩ ⟨x₁, hx₁⟩ ⟨x', hx'⟩ ⟨y₀, hy₀⟩ ⟨y₁, hy₁⟩ ⟨y', hy'⟩ :=
  rfl


variable [DecidableEq α]

-- ## Canonical signing

/-- Proposition that `Q` is a TU canonical signing with `0` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x' ≠ x₀ ∧ x' ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y' ≠ y₀ ∧ y' ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₀

/-- Proposition that `Q` is a TU canonical signing with `1` on the [0,1] position. -/
def Matrix.IsTuCanonicalSigning₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x' ≠ x₀ ∧ x' ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y' ≠ y₀ ∧ y' ≠ y₁)
  ∧ Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₁

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
private def Matrix.IsTuCanonicallySignable₀ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x' ≠ x₀ ∧ x' ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y' ≠ y₀ ∧ y' ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y'| = matrix3x3unsigned₀

/-- Sufficient condition for `Q.toCanonicalSigning` being a TU canonical signing of `Q.support`. -/
private def Matrix.IsTuCanonicallySignable₁ {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) : Prop :=
  Q.IsTotallyUnimodular
  ∧ (x₁ ≠ x₀ ∧ x' ≠ x₀ ∧ x' ≠ x₁)
  ∧ (y₁ ≠ y₀ ∧ y' ≠ y₀ ∧ y' ≠ y₁)
  ∧ |Q.submatrix3x3 x₀ x₁ x' y₀ y₁ y'| = matrix3x3unsigned₁

/-- Converts a matrix to the form of canonical TU signing, does not check assumptions. -/
private def Matrix.toCanonicalSigning {X Y : Set α} (Q : Matrix X Y ℚ) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) :
    Matrix X Y ℚ :=
  let u : X → ℚ := (fun i : X =>
    if i = x₀ then Q x₀ y₀ * Q x' y₀ else
    if i = x₁ then Q x₀ y₀ * Q x₀ y' * Q x₁ y' * Q x' y₀ else
    if i = x' then 1 else
    1)
  let v : Y → ℚ := (fun j : Y =>
    if j = y₀ then Q x' y₀ else
    if j = y₁ then Q x' y₁ else
    if j = y' then Q x₀ y₀ * Q x₀ y' * Q x' y₀ else
    1)
  Q ⊡ u ⊗ v

/-- Canonical signing of a TU matrix is TU. -/
private lemma Matrix.IsTotallyUnimodular.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ}
    (hQ : Q.IsTotallyUnimodular) (x₀ x₁ x' : X) (y₀ y₁ y' : Y) :
    (Q.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').IsTotallyUnimodular := by
  have hu : ∀ i : X,
    (fun i : X =>
      if i = x₀ then Q x₀ y₀ * Q x' y₀ else
      if i = x₁ then Q x₀ y₀ * Q x₀ y' * Q x₁ y' * Q x' y₀ else
      if i = x' then 1 else
      1) i ∈ SignType.cast.range
  · intro i
    if hix₀ : i = x₀ then
      simp_rw [hix₀, ite_true]
      apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix₁ : i = x₁ then
      simp_rw [hix₀, ite_false, hix₁, ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else if hix' : i = x' then
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix', ite_true]
      exact one_in_signTypeCastRange
    else
      simp_rw [hix₀, ite_false, hix₁, ite_false, hix', ite_false]
      exact one_in_signTypeCastRange
  have hv : ∀ j : Y,
    (fun j : Y =>
      if j = y₀ then Q x' y₀ else
      if j = y₁ then Q x' y₁ else
      if j = y' then Q x₀ y₀ * Q x₀ y' * Q x' y₀ else
      1) j ∈ SignType.cast.range
  · intro j
    if hjy₀ : j = y₀ then
      simp_rw [hjy₀, ite_true]
      apply hQ.apply
    else if hjy₁ : j = y₁ then
      simp_rw [hjy₀, ite_false, hjy₁, ite_true]
      apply hQ.apply
    else if hjy' : j = y' then
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy', ite_true]
      repeat apply in_signTypeCastRange_mul_in_signTypeCastRange
      all_goals apply hQ.apply
    else
      simp_rw [hjy₀, ite_false, hjy₁, ite_false, hjy', ite_false]
      exact one_in_signTypeCastRange
  unfold Matrix.toCanonicalSigning
  exact entryProd_outerProd_eq_mul_col_mul_row Q _ _ ▸ (hQ.mul_rows hu).mul_cols hv

private lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x' : X} {y₀ y₁ y' : Y} (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x' y₀ y₁ y') :
    (Q.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₀ := by
  obtain ⟨hQtu, ⟨hx₀, hx₁, hx'⟩, ⟨hy₀, hy₁, hy'⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₀] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').submatrix3x3 x₀ x₁ x' y₀ y₁ y'
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₀,
        hx₀, hx₁, hx', hy₀, hy₁, hy', hQ₀₁, hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d, hd⟩ := hQ3x3tu 3 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_three] at hd
  clear hQtu hQ3x3tu hQxy hQ₀₁ hQ₁₀ hQ₂₂ hx₀ hx₁ hx' hy₀ hy₁ hy'
  cases hQ₀₀ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd

private lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning_submatrix3x3 {X Y : Set α} {Q : Matrix X Y ℚ}
    {x₀ x₁ x' : X} {y₀ y₁ y' : Y} (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x' y₀ y₁ y') :
    (Q.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').submatrix3x3 x₀ x₁ x' y₀ y₁ y' = matrix3x3signed₁ := by
  obtain ⟨hQtu, ⟨hx₀, hx₁, hx'⟩, ⟨hy₀, hy₁, hy'⟩, hQxy⟩ := hQ
  simp only [Matrix.submatrix3x3, matrix3x3unsigned₁] at hQxy
  have hQ₀₀ := congr_fun (congr_fun hQxy 0) 0
  have hQ₀₁ := congr_fun (congr_fun hQxy 0) 1
  have hQ₀₂ := congr_fun (congr_fun hQxy 0) 2
  have hQ₁₀ := congr_fun (congr_fun hQxy 1) 0
  have hQ₁₁ := congr_fun (congr_fun hQxy 1) 1
  have hQ₁₂ := congr_fun (congr_fun hQxy 1) 2
  have hQ₂₀ := congr_fun (congr_fun hQxy 2) 0
  have hQ₂₁ := congr_fun (congr_fun hQxy 2) 1
  have hQ₂₂ := congr_fun (congr_fun hQxy 2) 2
  simp [Matrix.abs, abs_eq] at hQ₀₀ hQ₀₁ hQ₀₂ hQ₁₀ hQ₁₁ hQ₁₂ hQ₂₀ hQ₂₁ hQ₂₂
  have hQ3x3tu := (hQtu.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').submatrix3x3 x₀ x₁ x' y₀ y₁ y'
  simp [Matrix.submatrix3x3, Matrix.toCanonicalSigning, matrix3x3signed₁, matrix3x3unsigned₁,
        hx₀, hx₁, hx', hy₀, hy₁, hy', hQ₁₀, hQ₂₂] at hQ3x3tu ⊢
  obtain ⟨d₁, hd₁⟩ := (hQ3x3tu.submatrix ![0, 2] ![0, 1]) 2 id id Function.injective_id Function.injective_id
  obtain ⟨d₂, hd₂⟩ := (hQ3x3tu.submatrix ![0, 1] ![1, 2]) 2 id id Function.injective_id Function.injective_id
  simp [Matrix.det_fin_two] at hd₁ hd₂
  clear hQtu hQ3x3tu hQxy hQ₁₀ hQ₂₂ hx₀ hx₁ hx' hy₀ hy₁ hy'
  cases hQ₀₀ <;> cases hQ₀₁ <;> cases hQ₀₂ <;> cases hQ₁₁ <;> cases hQ₁₂ <;> cases hQ₂₀ <;> cases hQ₂₁
  <;> simp only [mul_one, mul_neg, neg_zero, neg_neg, *]
  <;> simp [*] at hd₁ hd₂

private lemma Matrix.IsTuCanonicallySignable₀.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x' : X} {y₀ y₁ y' : Y}
    (hQ : Q.IsTuCanonicallySignable₀ x₀ x₁ x' y₀ y₁ y') :
    (Q.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').IsTuCanonicalSigning₀ x₀ x₁ x' y₀ y₁ y' :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x' y₀ y₁ y', hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

private lemma Matrix.IsTuCanonicallySignable₁.toCanonicalSigning {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ x' : X} {y₀ y₁ y' : Y}
    (hQ : Q.IsTuCanonicallySignable₁ x₀ x₁ x' y₀ y₁ y') :
    (Q.toCanonicalSigning x₀ x₁ x' y₀ y₁ y').IsTuCanonicalSigning₁ x₀ x₁ x' y₀ y₁ y' :=
  have ⟨hQtu, hxxx, hyyy, _⟩ := hQ
  ⟨hQtu.toCanonicalSigning x₀ x₁ x' y₀ y₁ y', hxxx, hyyy, hQ.toCanonicalSigning_submatrix3x3⟩

-- lemma 15.a
private lemma Matrix.IsTotallyUnimodular.signing_expansion₀ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x' y₀ y₁ : α} (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hyy : y₀ ≠ y₁)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1)
    (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q ⟨x', hx'⟩ y = 0) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ◫ ▮c₀ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B : Matrix X Y ℚ := Q.shortTableauPivot ⟨x', hx'⟩ ⟨y₀, hy₀⟩
  let B' : Matrix (X \ {x'}).Elem Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓⟨y₀, hy₀⟩) ↓⟨y₁, hy₁⟩),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◩◪() else if hy₁ : y = y₁ then ◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).submatrix id e.symm
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    have := hi.right
    if j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀]
    else if j = y₁ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₀]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) (-1))
  have hq : ∀ i : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 15.b
private lemma Matrix.IsTotallyUnimodular.signing_expansion₁ {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x' y₀ y₁ : α} (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hyy : y₀ ≠ y₁)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1)
    (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q ⟨x', hx'⟩ y = 0) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intro c₀ c₁ Q'
  let B := Q.shortTableauPivot ⟨x', hx'⟩ ⟨y₁, hy₁⟩
  let B' : Matrix (X \ {x'}).Elem Y ℚ := B.submatrix Set.diff_subset.elem id
  let e : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit ≃ Y := ⟨
    (·.casesOn (·.casesOn Set.diff_subset.elem ↓⟨y₁, hy₁⟩) ↓⟨y₀, hy₀⟩),
    fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◪() else if hy₁ : y = y₁ then ◩◪() else ◩◩⟨y, by simp [*]⟩,
    ↓(by aesop),
    ↓(by aesop)⟩
  have B'_eq : B' = (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).submatrix id e.symm
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    if j = y₀ then
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₁]
      aesop
    else if j = y₁ then
      have := hi.right
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
    else
      simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
  have hB : B.IsTotallyUnimodular
  · apply hQ.shortTableauPivot
    rw [hQy₁]
    exact Rat.zero_ne_one.symm
  have hB' : B'.IsTotallyUnimodular
  · apply hB.submatrix
  rw [B'_eq] at hB'
  have hQcc : (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular
  · simpa using hB'.submatrix id e
  let q : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
  have hq : ∀ i : ((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
  · rintro ((_|_)|_) <;> simp [q]
  convert hQcc.mul_cols hq
  ext _ ((_|_)|_) <;> simp [q]

-- lemma 16.1
omit [DecidableEq α] in
private lemma Matrix.IsTotallyUnimodular.special_form_cols {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
    {x' y₀ y₁ : α} (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1) (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    ∀ i : (X \ {x'}).Elem, ![c₀ i, c₁ i] ≠ ![1, -1] ∧ ![c₀ i, c₁ i] ≠ ![-1, 1] := by
  intro c₀ c₁ i
  constructor <;>
  · intro contr
    simp only [c₀, c₁] at contr
    have := congr_fun contr 0
    have := congr_fun contr 1
    have := hQ.det ![⟨x', hx'⟩, Set.diff_subset.elem i] ![⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩]
    simp_all [Matrix.det_fin_two]

-- lemma 16.2
private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_weak {X Y : Set α} {Q : Matrix X Y ℚ} {x' y₀ y₁ : α}
    (hQ : Q.IsTotallyUnimodular) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hyy : y₀ ≠ y₁)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1)
    (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q ⟨x', hx'⟩ y = 0) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ◫ ▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  sorry

private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_aux {X Y : Set α} {Q : Matrix X Y ℚ} {x' y₀ y₁ : α}
    (hQ : Q.IsTotallyUnimodular) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hyy : y₀ ≠ y₁)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1)
    (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q ⟨x', hx'⟩ y = 0) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ◫ ▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
  intros
  convert (hQ.signing_expansion_cols_weak hx' hy₀ hy₁ hyy hQy₀ hQy₁ hQy).comp_cols
    (fun j : (((((((Y \ {y₀, y₁}).Elem ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) =>
      (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (◩◩◩·) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) ↓◪()) ↓◪()))
  aesop

private lemma Matrix.IsTotallyUnimodular.signing_expansion_cols {X Y : Set α} {Q : Matrix X Y ℚ} {x' y₀ y₁ : α}
    (hQ : Q.IsTotallyUnimodular) (hx' : x' ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hyy : y₀ ≠ y₁)
    (hQy₀ : Q ⟨x', hx'⟩ ⟨y₀, hy₀⟩ = 1)
    (hQy₁ : Q ⟨x', hx'⟩ ⟨y₁, hy₁⟩ = 1)
    (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q ⟨x', hx'⟩ y = 0) :
    let c₀ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₀, hy₀⟩
    let c₁ : (X \ {x'}).Elem → ℚ := fun j => Q (Set.diff_subset.elem j) ⟨y₁, hy₁⟩
    let Q' : Matrix (X \ {x'}).Elem (Y \ {y₀, y₁}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ◫ ▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ ▮0).IsTotallyUnimodular := by
  intros
  convert ((hQ.signing_expansion_cols_aux hx' hy₀ hy₁ hyy hQy₀ hQy₁ hQy).mul_cols
    (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 1) (-1)) 1) (-1)) 1) (-1)) j ∈
        SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).fromCols_zero Unit
  aesop

-- Lemma 18.2's corollary
private lemma Matrix.IsTotallyUnimodular.signing_expansion_rows {X Y : Set α} {Q : Matrix X Y ℚ} {x₀ x₁ y' : α}
    (hQ : Q.IsTotallyUnimodular) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hy' : y' ∈ Y) (hxx : x₀ ≠ x₁)
    (hQx₀ : Q ⟨x₀, hx₀⟩ ⟨y', hy'⟩ = 1)
    (hQx₁ : Q ⟨x₁, hx₁⟩ ⟨y', hy'⟩ = 1)
    (hQx : ∀ x : X, x.val ≠ x₀ ∧ x.val ≠ x₁ → Q x ⟨y', hy'⟩ = 0) :
    let d₀ : (Y \ {y'}).Elem → ℚ := (Q ⟨x₀, hx₀⟩ <| Set.diff_subset.elem ·)
    let d₁ : (Y \ {y'}).Elem → ℚ := (Q ⟨x₁, hx₁⟩ <| Set.diff_subset.elem ·)
    let Q' : Matrix (X \ {x₀, x₁}).Elem (Y \ {y'}).Elem ℚ := Q.submatrix Set.diff_subset.elem Set.diff_subset.elem
    (Q' ⊟ ▬d₀ ⊟ ▬(-d₀) ⊟ ▬d₁ ⊟ ▬(-d₁) ⊟ ▬(d₀ - d₁) ⊟ ▬(d₁ - d₀) ⊟ ▬0).IsTotallyUnimodular := by
  intros
  convert (hQ.transpose.signing_expansion_cols hy' hx₀ hx₁ hxx hQx₀ hQx₁ hQx).transpose
  aesop

-- canonical signing of 3-sum constructed from TU signings of summands
private noncomputable def matrix3sumCompositionCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    (Bₗ' : Matrix Xₗ Yₗ ℚ) (Bᵣ' : Matrix Xᵣ Yᵣ ℚ)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'}) :
    Matrix ((Xₗ \ {x₀, x₁}).Elem ⊕ (Xᵣ \ {x'}).Elem) ((Yₗ \ {y'}).Elem ⊕ (Yᵣ \ {y₀, y₁}).Elem) ℚ :=
  -- row membership
  let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
  let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
  let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
  let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
  let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
  let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
  -- column membership
  let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
  let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
  let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
  let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
  let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
  let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
  -- convert summands to canonical form
  let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
  let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
  -- top left submatrix
  let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- bottom right submatrix
  let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
  -- pieces of bottom left submatrix
  let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
  let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
  let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
    ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
  let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
    Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
  let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
  -- initial bottom left submatrix
  let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
  -- reindexing for bottom left submatrix
  let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
    if hi₀ : i.val = x₀ then ◩0 else
    if hi₁ : i.val = x₁ then ◩1 else
    if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := i
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
    if hj₀ : j.val = y₀ then ◪0 else
    if hj₁ : j.val = y₁ then ◪1 else
    if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
    False.elim (by
      simp_all only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, false_or, not_and, Decidable.not_not]
      obtain ⟨_, _⟩ := j
      simp_all only
      simp_all only [Set.mem_diff, Set.mem_singleton_iff, imp_false, not_true_eq_false]))
  -- final bottom left submatrix
  let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
  -- actual definition
  ⊞ Aₗ 0 D Aᵣ

-- lemma 19.1
private lemma matrix3sumCompositionCanonicalSigning_D_Eq_SumOuterProducts {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
    let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
    -- column membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
    let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
    let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₀ᵣ
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₁ᵣ
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₀ₗ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₁ₗ (Set.diff_subset.elem i)
    let D₀': Matrix (Fin 3) (Fin 3) ℚ :=
      |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ|
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then -d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ - d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    -- actual statement
    D = c₀ ⊗ r₀ + c₁ ⊗ r₁ :=
  sorry

-- lemma 19.2
private lemma matrix3sumCompositionCanonicalSigning_D_Rows {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
    let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
    -- column membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
    let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
    let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₀ᵣ
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₁ᵣ
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₀ₗ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₁ₗ (Set.diff_subset.elem i)
    let D₀' : Matrix (Fin 3) (Fin 3) ℚ :=
      |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ|
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then -d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ - d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    -- actual statement
    ∀ i, D i = r₀ ∨ D i = -r₀ ∨ D i = r₁ ∨ D i = -r₁ ∨ D i = r₂ ∨ D i = -r₂ ∨ D i = 0 :=
  sorry

-- lemma 19.3
private lemma matrix3sumCompositionCanonicalSigning_D_Cols {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
    let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
    -- column membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
    let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
    let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₀ᵣ
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₁ᵣ
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₀ₗ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₁ₗ (Set.diff_subset.elem i)
    let D₀' : Matrix (Fin 3) (Fin 3) ℚ :=
      |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ|
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then -d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ - d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    -- actual statement
    ∀ j, (D · j) = c₀ ∨ (D · j) = -c₀ ∨ (D · j) = c₁ ∨ (D · j) = -c₁ ∨ (D · j) = c₀ - c₁ ∨ (D · j) = c₁ - c₀ ∨ (D · j) = 0 :=
  sorry

-- lemma 19.5
private lemma matrix3sumCompositionCanonicalSigning_Aᵣ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
    let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
    -- column membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
    let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
    let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₀ᵣ
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₁ᵣ
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₀ₗ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₁ₗ (Set.diff_subset.elem i)
    let D₀' : Matrix (Fin 3) (Fin 3) ℚ :=
      |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ|
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then -d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ - d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    -- actual statement
    (Aᵣ ◫ D).IsTotallyUnimodular :=
  sorry

-- lemma 19.7
private lemma matrix3sumCompositionCanonicalSigning_Aₗ_D_TU {Xₗ Yₗ Xᵣ Yᵣ : Set α} {x₀ x₁ x' y₀ y₁ y' : α}
    [∀ x, Decidable (x ∈ Xₗ \ {x₀, x₁, x'})] [∀ x, Decidable (x ∈ Xᵣ \ {x₀, x₁, x'})] -- for reindexing of `D`
    [∀ y, Decidable (y ∈ Yₗ \ {y₀, y₁, y'})] [∀ y, Decidable (y ∈ Yᵣ \ {y₀, y₁, y'})] -- for reindexing of `D`
    {Bₗ' : Matrix Xₗ Yₗ ℚ} {Bᵣ' : Matrix Xᵣ Yᵣ ℚ} (hBₗ' : Bₗ'.IsTotallyUnimodular) (hBᵣ' : Bᵣ'.IsTotallyUnimodular)
    (hXX : Xₗ ∩ Xᵣ = {x₀, x₁, x'}) (hYY : Yₗ ∩ Yᵣ = {y₀, y₁, y'})
    (hBₗ' : |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₀ ∨
            |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ| = matrix3x3unsigned₁ )
    (hBᵣ' : |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₀ ∨
            |Bᵣ'.submatrix3x3mems hXX.mem3₀ᵣ hXX.mem3₁ᵣ hXX.mem3₂ᵣ hYY.mem3₀ᵣ hYY.mem3₁ᵣ hYY.mem3₂ᵣ| = matrix3x3unsigned₁ ) :
    -- row membership
    let x₀ₗ : Xₗ := ⟨x₀, hXX.mem3₀ₗ⟩
    let x₀ᵣ : Xᵣ := ⟨x₀, hXX.mem3₀ᵣ⟩
    let x₁ₗ : Xₗ := ⟨x₁, hXX.mem3₁ₗ⟩
    let x₁ᵣ : Xᵣ := ⟨x₁, hXX.mem3₁ᵣ⟩
    let x'ₗ : Xₗ := ⟨x', hXX.mem3₂ₗ⟩
    let x'ᵣ : Xᵣ := ⟨x', hXX.mem3₂ᵣ⟩
    -- column membership
    let y₀ₗ : Yₗ := ⟨y₀, hYY.mem3₀ₗ⟩
    let y₀ᵣ : Yᵣ := ⟨y₀, hYY.mem3₀ᵣ⟩
    let y₁ₗ : Yₗ := ⟨y₁, hYY.mem3₁ₗ⟩
    let y₁ᵣ : Yᵣ := ⟨y₁, hYY.mem3₁ᵣ⟩
    let y'ₗ : Yₗ := ⟨y', hYY.mem3₂ₗ⟩
    let y'ᵣ : Yᵣ := ⟨y', hYY.mem3₂ᵣ⟩
    -- convert summands to canonical form
    let Bₗ := Bₗ'.toCanonicalSigning x₀ₗ x₁ₗ x'ₗ y₀ₗ y₁ₗ y'ₗ
    let Bᵣ := Bᵣ'.toCanonicalSigning x₀ᵣ x₁ᵣ x'ᵣ y₀ᵣ y₁ᵣ y'ᵣ
    -- top left submatrix
    let Aₗ : Matrix (Xₗ \ {x₀, x₁}).Elem (Yₗ \ {y'}).Elem ℚ := Bₗ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- bottom right submatrix
    let Aᵣ : Matrix (Xᵣ \ {x'}).Elem (Yᵣ \ {y₀, y₁}).Elem ℚ := Bᵣ.submatrix Set.diff_subset.elem Set.diff_subset.elem
    -- pieces of bottom left submatrix
    let D₀ₗ : Matrix (Fin 2) (Fin 2) ℚ := !![Bₗ x₀ₗ y₀ₗ, Bₗ x₀ₗ y₁ₗ; Bₗ x₁ₗ y₀ₗ, Bₗ x₁ₗ y₁ₗ]
    let D₀ᵣ : Matrix (Fin 2) (Fin 2) ℚ := !![Bᵣ x₀ᵣ y₀ᵣ, Bᵣ x₀ᵣ y₁ᵣ; Bᵣ x₁ᵣ y₀ᵣ, Bᵣ x₁ᵣ y₁ᵣ]
    let Dₗ : Matrix (Fin 2) (Yₗ \ {y₀, y₁, y'}).Elem ℚ :=
      ![Bₗ x₀ₗ ∘ Set.diff_subset.elem, Bₗ x₁ₗ ∘ Set.diff_subset.elem]
    let Dᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Fin 2) ℚ :=
      Matrix.of (fun i => ![Bᵣ (Set.diff_subset.elem i) y₀ᵣ, Bᵣ (Set.diff_subset.elem i) y₁ᵣ])
    let Dₗᵣ : Matrix (Xᵣ \ {x₀, x₁, x'}).Elem (Yₗ \ {y₀, y₁, y'}).Elem ℚ := Dᵣ * D₀ₗ⁻¹ * Dₗ
    -- initial bottom left submatrix
    let D' : Matrix (Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem) ((Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2) ℚ := ⊞ Dₗ D₀ₗ Dₗᵣ Dᵣ
    -- reindexing for bottom left submatrix
    let fᵣ : (Xᵣ \ {x'}).Elem → Fin 2 ⊕ (Xᵣ \ {x₀, x₁, x'}).Elem := fun i => (
      if hi₀ : i.val = x₀ then ◩0 else
      if hi₁ : i.val = x₁ then ◩1 else
      if hi : i.val ∈ Xᵣ \ {x₀, x₁, x'} then ◪⟨i, hi⟩ else
      (impossible_nmem_sdiff_triplet hi hi₀ hi₁).elim)
    let fₗ : (Yₗ \ {y'}).Elem → (Yₗ \ {y₀, y₁, y'}).Elem ⊕ Fin 2 := fun j => (
      if hj₀ : j.val = y₀ then ◪0 else
      if hj₁ : j.val = y₁ then ◪1 else
      if hj : j.val ∈ Yₗ \ {y₀, y₁, y'} then ◩⟨j, hj⟩ else
      (impossible_nmem_sdiff_triplet hj hj₀ hj₁).elim)
    -- final bottom left submatrix
    let D : Matrix (Xᵣ \ {x'}).Elem (Yₗ \ {y'}).Elem ℚ := D'.submatrix fᵣ fₗ
    -- special rows and columns
    let c₀ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₀ᵣ
    let c₁ : (Xᵣ \ {x'}).Elem → ℚ := fun j => Bᵣ (Set.diff_subset.elem j) y₁ᵣ
    let d₀ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₀ₗ (Set.diff_subset.elem i)
    let d₁ : (Yₗ \ {y'}).Elem → ℚ := fun i => Bₗ x₁ₗ (Set.diff_subset.elem i)
    let D₀' : Matrix (Fin 3) (Fin 3) ℚ :=
      |Bₗ'.submatrix3x3mems hXX.mem3₀ₗ hXX.mem3₁ₗ hXX.mem3₂ₗ hYY.mem3₀ₗ hYY.mem3₁ₗ hYY.mem3₂ₗ|
    let r₀ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ - d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₁ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then -d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₁ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    let r₂ : (Yₗ \ {y'}).Elem → ℚ :=
      if hD₀₀ : D₀' = matrix3x3unsigned₀ then d₀ - d₁ else
      if hD₀₁ : D₀' = matrix3x3unsigned₁ then d₀ else
      (False.elim (by
        simp_all only [D₀']
        cases hBₗ' with
        | inl => simp_all only [not_true_eq_false, D₀']
        | inr => simp_all only [not_true_eq_false, D₀']))
    -- actual statement
    (Aₗ ⊟ D).IsTotallyUnimodular := by
  sorry


-- ## The 3-sum of matroids

/-- The 3-sum composition of two binary matroids given by their stanard representations. -/
noncomputable def standardRepr3sumComposition_standard {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    StandardRepr α Z2 × Prop :=
  ⟨
    ⟨
      (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x'}),
      (Sₗ.Y \ {y'}) ∪ (Sᵣ.Y \ {y₀, y₁}),
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨Sₗ.hXY.disjoint_sdiff_left.disjoint_sdiff_right, hYX.symm.disjoint_sdiff_left.disjoint_sdiff_right⟩,
          ⟨hXY.disjoint_sdiff_left.disjoint_sdiff_right, Sᵣ.hXY.disjoint_sdiff_left.disjoint_sdiff_right⟩⟩,
      (matrix3sumComposition_standard Sₗ.B Sᵣ.B hXX hYY).fst.toMatrixUnionUnion,
      inferInstance,
      inferInstance,
    ⟩,
    (matrix3sumComposition_standard Sₗ.B Sᵣ.B hXX hYY).snd
  ⟩

lemma standardRepr3sumComposition_standard_X {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.X = (Sₗ.X \ {x₀, x₁}) ∪ (Sᵣ.X \ {x'}) :=
  rfl

lemma standardRepr3sumComposition_standard_Y {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.Y = (Sₗ.Y \ {y'}) ∪ (Sᵣ.Y \ {y₀, y₁}) :=
  rfl

/-- Decomposition of (binary) matroid `M` as a 3-sum of (binary) matroids `Mₗ` and `Mᵣ`. -/
structure Matroid.Is3sumOf (M : Matroid α) (Mₗ Mᵣ : Matroid α) where
  S : StandardRepr α Z2
  Sₗ : StandardRepr α Z2
  Sᵣ : StandardRepr α Z2
  hSₗ : Finite Sₗ.X
  hSᵣ : Finite Sᵣ.X
  hM : S.toMatroid = M
  hMₗ : Sₗ.toMatroid = Mₗ
  hMᵣ : Sᵣ.toMatroid = Mᵣ
  (x₁ x₂ x₃ y₁ y₂ y₃ : α)
  hXX : Sₗ.X ∩ Sᵣ.X = {x₁, x₂, x₃}
  hYY : Sₗ.Y ∩ Sᵣ.Y = {y₁, y₂, y₃}
  hXY : Sₗ.X ⫗ Sᵣ.Y
  hYX : Sₗ.Y ⫗ Sᵣ.X
  IsSum : (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst = S
  IsValid : (standardRepr3sumComposition_standard hXX hYY hXY hYX).snd

instance Matroid.Is3sumOf.finS {M Mₗ Mᵣ : Matroid α} (hM : M.Is3sumOf Mₗ Mᵣ) : Finite hM.S.X := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [standardRepr3sumComposition_standard_X]
  apply Finite.Set.finite_union

lemma standardRepr3sumComposition_hasTuSigning {Sₗ Sᵣ : StandardRepr α Z2} {x₀ x₁ x' y₀ y₁ y' : α}
    (hXX : Sₗ.X ∩ Sᵣ.X = {x₀, x₁, x'}) (hYY : Sₗ.Y ∩ Sᵣ.Y = {y₀, y₁, y'}) (hXY : Sₗ.X ⫗ Sᵣ.Y) (hYX : Sₗ.Y ⫗ Sᵣ.X)
    (hSₗ : Sₗ.B.HasTuSigning) (hSᵣ : Sᵣ.B.HasTuSigning) :
    (standardRepr3sumComposition_standard hXX hYY hXY hYX).fst.B.HasTuSigning := by
  obtain ⟨Bₗ, hBₗ, hBBₗ⟩ := hSₗ
  obtain ⟨Bᵣ, hBᵣ, hBBᵣ⟩ := hSᵣ
  sorry

/-- Any 3-sum of regular matroids is a regular matroid.
    This is the final part of the easy direction of the Seymour's theorem. -/
theorem Matroid.Is3sumOf.isRegular {M Mₗ Mᵣ : Matroid α}
    (hM : M.Is3sumOf Mₗ Mᵣ) (hMₗ : Mₗ.IsRegular) (hMᵣ : Mᵣ.IsRegular) :
    M.IsRegular := by
  have := hM.finS
  obtain ⟨_, _, _, _, _, rfl, rfl, rfl, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hM
  rw [StandardRepr.toMatroid_isRegular_iff_hasTuSigning] at hMₗ hMᵣ ⊢
  apply standardRepr3sumComposition_hasTuSigning
  · exact hMₗ
  · exact hMᵣ
