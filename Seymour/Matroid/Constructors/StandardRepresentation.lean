import Seymour.Basic.Sets
import Seymour.Matrix.LinearIndependence
import Seymour.Matroid.Constructors.BinaryMatroid

open scoped Matrix Set.Notation


/-- Standard matrix representation of a vector matroid. -/
structure StandardRepr (α R : Type) [DecidableEq α] where
  /-- Row indices. -/
  X : Set α
  /-- Col indices. -/
  Y : Set α
  /-- Basis and nonbasis elements are disjoint -/
  hXY : X ⫗ Y
  /-- Standard representation matrix. -/
  B : Matrix X Y R
  /-- The computer can determine whether certain element is a row. -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- The computer can determine whether certain element is a col. -/
  decmemY : ∀ a, Decidable (a ∈ Y)

attribute [instance] StandardRepr.decmemX
attribute [instance] StandardRepr.decmemY


variable {α R : Type} [DecidableEq α]

/-- Vector matroid constructed from the standard representation. -/
def StandardRepr.toVectorMatroid [Zero R] [One R] (S : StandardRepr α R) : VectorMatroid α R :=
  ⟨S.X, S.X ∪ S.Y, (S.B.prependId · ∘ Subtype.toSum)⟩

/-- Converting standard representation to full representation does not change the set of row indices. -/
@[simp]
lemma StandardRepr.toVectorMatroid_X [Zero R] [One R] (S : StandardRepr α R) :
    S.toVectorMatroid.X = S.X :=
  rfl

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_Y [Zero R] [One R] (S : StandardRepr α R) :
    S.toVectorMatroid.Y = S.X ∪ S.Y :=
  rfl

/-- If a vector matroid has a standard representation matrix `B`, its full representation matrix is `[1 | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A [Zero R] [One R] (S : StandardRepr α R) :
    S.toVectorMatroid.A = (S.B.prependId · ∘ Subtype.toSum) :=
  rfl

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E [DivisionRing R] (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.E = S.X ∪ S.Y :=
  rfl

instance {S : StandardRepr α R} [Zero R] [One R] [hSX : Finite S.X] : Finite S.toVectorMatroid.X :=
  hSX

instance {S : StandardRepr α R} [Zero R] [One R] [Finite S.X] [Finite S.Y] : Finite S.toVectorMatroid.Y :=
  Finite.Set.finite_union S.X S.Y

lemma StandardRepr.toVectorMatroid_indep_iff [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

@[simp]
lemma StandardRepr.toVectorMatroid_indep_iff' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) := by
  simp_rw [←Matrix.prependId_transpose] -- TODO reëxamine simp-normal form!
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ hI.elem.range := by
  rw [StandardRepr.toVectorMatroid_indep_iff]
  unfold HasSubset.Subset.elem
  aesop

lemma StandardRepr.toVectorMatroid_indep_iff_elem' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem I

lemma StandardRepr.toVectorMatroid_indep_iff_elem'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) hI.elem.range := by
  simpa using S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem))ᵀ := by
  simp only [StandardRepr.toVectorMatroid, VectorMatroid.toMatroid_indep, VectorMatroid.indepCols_iff_submatrix]
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependIdᵀ.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  StandardRepr.toVectorMatroid_indep_iff_submatrix S I

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.Bᵀ.uppendId.submatrix (Subtype.toSum ∘ hI.elem) id) := by
  simpa using S.toVectorMatroid_indep_iff_submatrix' I

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_isBase [DivisionRing R] {B : Set α}
    (M : VectorMatroid α R) (hMB : M.toMatroid.IsBase B) :
    ∃ S : StandardRepr α R, M.X = B ∧ S.toVectorMatroid = M := by
  have hBY := hMB.subset_ground
  sorry

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr [DivisionRing R] (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, S.toVectorMatroid = M := by
  peel VectorMatroid.exists_standardRepr_isBase M M.toMatroid.exists_isBase.choose_spec with hS
  exact hS.2

/-- Construct a matroid from a standard representation. -/
def StandardRepr.toMatroid [DivisionRing R] (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

attribute [local ext] StandardRepr

/-- Kinda extensionality on `StandardRepr` but `@[ext]` cannot be here. -/
lemma standardRepr_eq_standardRepr_of_B_eq_B [DivisionRing R] {S₁ S₂ : StandardRepr α R}
    (hX : S₁.X = S₂.X) (hY : S₁.Y = S₂.Y) (hB : S₁.B = hX ▸ hY ▸ S₂.B) :
    S₁ = S₂ := by
  ext1
  · exact hX
  · exact hY
  · aesop
  · apply Function.hfunext rfl
    intro a₁ a₂ haa
    apply Subsingleton.helim
    if ha₁ : a₁ ∈ S₁.X then
      have ha₂ : a₂ ∈ S₂.X
      · rw [heq_eq_eq] at haa
        rwa [haa, hX] at ha₁
      simp [ha₁, ha₂]
    else
      have ha₂ : a₂ ∉ S₂.X
      · rw [heq_eq_eq] at haa
        rwa [haa, hX] at ha₁
      simp [ha₁, ha₂]
  · apply Function.hfunext rfl
    intro a₁ a₂ haa
    apply Subsingleton.helim
    if ha₁ : a₁ ∈ S₁.Y then
      have ha₂ : a₂ ∈ S₂.Y
      · rw [heq_eq_eq] at haa
        rwa [haa, hY] at ha₁
      simp [ha₁, ha₂]
    else
      have ha₂ : a₂ ∉ S₂.Y
      · rw [heq_eq_eq] at haa
        rwa [haa, hY] at ha₁
      simp [ha₁, ha₂]

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp high]
lemma StandardRepr.toMatroid_E [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.E = S.X ∪ S.Y :=
  rfl

lemma StandardRepr.toMatroid_indep_iff [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff I

lemma StandardRepr.toMatroid_indep_iff' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff' I

lemma StandardRepr.toMatroid_indep_iff'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff'' I

lemma StandardRepr.toMatroid_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem I

@[simp high]
lemma StandardRepr.toMatroid_indep_iff_elem' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toMatroid_indep_iff_elem'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem'' I

lemma StandardRepr.toMatroid_indep_iff_submatrix [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem))ᵀ :=
  S.toVectorMatroid_indep_iff_submatrix I

lemma StandardRepr.toMatroid_indep_iff_submatrix' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependIdᵀ.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  S.toVectorMatroid_indep_iff_submatrix' I

lemma StandardRepr.toMatroid_indep_iff_submatrix'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.Bᵀ.uppendId.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  S.toVectorMatroid_indep_iff_submatrix'' I

@[simp]
lemma StandardRepr.toMatroid_indep [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.Indep = (∃ hI : · ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range) := by
  ext I
  exact S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toMatroid_indep' [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.Indep = (∃ hI : · ⊆ S.X ∪ S.Y, LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) hI.elem.range) := by
  simp

/-- The identity matrix has linearly independent rows. -/
lemma Matrix.one_linearIndependent [Ring R] : LinearIndependent R (1 : Matrix α α R) := by
  -- Riccardo Brasca proved:
  rw [linearIndependent_iff]
  intro l hl
  ext j
  simpa [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum_apply', Matrix.one_apply] using congr_fun hl j

/-- The set of all rows of a standard representation is a base in the resulting matroid. -/
lemma StandardRepr.toMatroid_isBase_X [Field R] (S : StandardRepr α R) [Fintype S.X] :
    S.toMatroid.IsBase S.X := by
  apply Matroid.Indep.isBase_of_forall_insert
  · rw [StandardRepr.toMatroid_indep_iff_submatrix]
    use Set.subset_union_left
    simp [Matrix.submatrix]
    show @LinearIndependent S.X R _ 1ᵀ ..
    rw [Matrix.transpose_one]
    exact Matrix.one_linearIndependent
  · intro e he
    rw [StandardRepr.toMatroid_indep_iff_submatrix]
    push_neg
    intro _
    apply Matrix.not_linearIndependent_of_too_many_rows
    have heX : e ∉ S.X.toFinset := (Set.not_mem_of_mem_diff he <| Set.mem_toFinset.→ ·)
    simp [heX]

set_option maxHeartbeats 400000 in
private lemma B_eq_B_of_same_matroid_same_X_aux {X Y : Set α} {B : Matrix Y X Z2}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} (hXXY : X ⊆ X ∪ Y) (hYXY : Y ⊆ X ∪ Y) -- redundant but keep
    {D : Set X} {y : Y} (hyDXY : ↑y ᕃ Subtype.val '' D ⊆ X ∪ Y)
    {l : (X ∪ Y).Elem →₀ Z2} (hl : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D) (hly : l (hYXY.elem y) = 0)
    [Fintype (X ↓∩ l.support.toSet).Elem]
    {i : (X ∪ Y).Elem} (hil : i ∈ l.support) (hiX : i.val ∈ X) (hlBi : ∑ a ∈ l.support, l a • B.uppendId a.toSum ⟨i, hiX⟩ = 0) :
    ∑ a ∈ (X ↓∩ Subtype.val '' l.support.toSet).toFinset, l (hXXY.elem a) • B.uppendId (hXXY.elem a).toSum ⟨i, hiX⟩ = 0 := by
  have hlXXY : l.support.toSet ⊆ hXXY.elem.range
  · intro a ha
    specialize hl a ha
    rw [Set.mem_insert_iff] at hl
    cases hl with
    | inl hay =>
      exfalso
      have hay' : a = hYXY.elem y := SetCoe.ext hay
      rw [←hay'] at hly
      exact Finsupp.not_mem_support_iff.← hly ha
    | inr =>
      rw [HasSubset.Subset.elem_range]
      aesop
  rw [←Set.left_eq_inter] at hlXXY
  have hlX : l.support.toSet = hXXY.elem '' (X ↓∩ l.support.toSet)
  · conv => lhs; rw [hlXXY]
    ext
    aesop
  rw [←Finset.sum_finset_coe, finset_toSet_sum hlX (fun a : (X ∪ Y).Elem => l a • B.uppendId a.toSum ⟨i, hiX⟩)] at hlBi
  convert hlBi
  apply Finset.sum_bij (fun a ha => ⟨hXXY.elem a, by simpa using ha⟩)
  · simp
  · intro _ _ _ _ collision
    apply SetCoe.ext
    simpa using collision
  · simp
  · intro _ _
    rfl

set_option maxHeartbeats 1200000 in
private lemma B_eq_B_of_same_matroid_same_X {X Y : Set α} {hXY : X ⫗ Y} {B₁ B₂ : Matrix X Y Z2}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
    (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
    B₁ = B₂ := by
  rw [←Matrix.transpose_inj]
  apply Matrix.ext_col
  intro y
  have hXXY : X ⊆ X ∪ Y := Set.subset_union_left
  have hYXY : Y ⊆ X ∪ Y := Set.subset_union_right
  have hSS' := congr_arg Matroid.Indep hSS
  let D₁ := { x : X | B₁ᵀ y x ≠ 0 }
  let D₂ := { x : X | B₂ᵀ y x ≠ 0 }
  suffices hDD : D₁ = D₂
  · ext x
    if hx₁ : B₁ᵀ y x = 1 then
      have hx₂ : x ∈ D₂
      · rw [←hDD]
        simp only [D₁, Set.mem_setOf_eq]
        rw [hx₁]
        norm_num
      rw [hx₁, Fin2_eq_1_of_ne_0 hx₂]
    else
      have hx₂ : x ∉ D₂
      · rw [←hDD]
        simpa [D₁] using Fin2_eq_0_of_ne_1 hx₁
      simp only [D₂, Set.mem_setOf_eq, not_not] at hx₂
      rw [Fin2_eq_0_of_ne_1 hx₁, hx₂]
  apply Set.eq_of_subset_of_subset
  · -- show `D₁ ⊆ D₂`
    by_contra hD
    rw [Set.not_subset_iff_exists_mem_not_mem] at hD
    -- otherwise `y ᕃ D₂` is dependent in `M₂` but indep in `M₁`
    have hM₂ : ¬ (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid.Indep (y.val ᕃ D₂)
    · rw [StandardRepr.toMatroid_indep_iff_elem', not_exists]
      intro hD₂
      erw [not_linearIndependent_iff]
      refine ⟨Finset.univ, 1, ?_, ⟨hYXY.elem y, by simp_all⟩, Finset.mem_univ _, Ne.symm (zero_ne_one' Z2)⟩
      -- there are exactly two `1`s in rows from `D₂` and all `0`s otherwise
      ext x
      simp only at x hD₂
      simp only [D₁, D₂, Matrix.transpose_apply, Pi.one_apply, Function.comp_apply, one_smul, Finset.sum_apply]
      show ∑ i : hD₂.elem.range.Elem, B₂.prependId x i.val.toSum = 0 -- in `Z2`
      suffices separated : B₂ x y + ∑ i : D₂.Elem, (1 : Matrix X X Z2) x i.val = 0
      · rw [Finset.sum_set_coe (f := (fun i : (X ∪ Y).Elem => B₂.prependId x i.toSum)),
          Set.toFinset_range,
          show Finset.univ.image hD₂.elem = hYXY.elem y ᕃ Finset.map ⟨hXXY.elem, hXXY.elem_injective⟩ { x : X | B₂ᵀ y x ≠ 0 } by
            aesop,
          Finset.sum_insert (by
            simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_map, exists_and_right, not_exists, not_not]
            intro a ⟨_, contradictory⟩
            have hay : a.val = y.val
            · simpa using contradictory
            have impossible : y.val ∈ X ∩ Y := ⟨hay ▸ a.property, y.property⟩
            rw [hXY.inter_eq] at impossible
            exact impossible)]
        convert separated
        · convert_to B₂.prependId x ◪y = B₂ x y
          · congr
            simpa [Subtype.toSum] using hXY.not_mem_of_mem_right y.property
          simp
        · simp [D₂]
          show
            ∑ i ∈ Finset.univ.filter (fun x : X => B₂ x y ≠ 0), (1 : Matrix X X Z2) x i =
            ∑ i : { x : X // B₂ x y ≠ 0 }, (1 : Matrix X X Z2) x i
          apply Finset.sum_subtype
          simp
      if hx : x ∈ D₂ then
        convert_to 1 + 1 = (0 : Z2) using 2
        · apply Fin2_eq_1_of_ne_0
          simpa [D₂] using hx
        · exact sum_elem_matrix_row_of_mem hx
        decide
      else
        convert_to 0 + 0 = (0 : Z2) using 2
        · simpa [D₂] using hx
        · exact sum_elem_matrix_row_of_nmem hx
        decide
    have hM₁ : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid.Indep (y.val ᕃ D₂)
    · obtain ⟨d, hd₁, hd₂⟩ := hD
      simp
      have hDXY : Subtype.val '' D₂ ⊆ X ∪ Y := (Subtype.coe_image_subset X D₂).trans hXXY
      have hyXY : y.val ∈ X ∪ Y := hYXY y.property
      have hyDXY : y.val ᕃ Subtype.val '' D₂ ⊆ X ∪ Y := Set.insert_subset hyXY hDXY
      use Set.insert_subset hyXY hDXY
      -- if the coefficient in front of `y` is `0` then all coefficients must be `0`
      -- if the coefficient in front of `y` is `1` then the sum will always have `1` on `d` position
      rw [linearIndepOn_iff]
      intro l hl hlB
      have hl' : l.support.toSet ⊆ hyDXY.elem.range
      · rwa [Finsupp.mem_supported] at hl
      have hl'' : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D₂ :=
        fun e he => (hyDXY.elem_range ▸ hl') he
      if hly : l (hYXY.elem y) = 0 then
        ext i
        if hil : i ∈ l.support then
          if hiX : i.val ∈ X then
            have hlBi := congr_fun hlB ⟨i.val, hiX⟩
            rw [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum, Finset.sum_apply] at hlBi
            simp_rw [Pi.smul_apply, Function.comp_apply] at hlBi
            have : Fintype (X ↓∩ l.support.toSet).Elem
            · exact Set.Finite.fintype Subtype.finite
            have hlBi' : ∑ x ∈ (X ↓∩ Subtype.val '' l.support.toSet).toFinset, l (hXXY.elem x) • (1 : Matrix X X Z2) x ⟨i, hiX⟩ = 0
            · simpa using B_eq_B_of_same_matroid_same_X_aux hXXY hYXY hyDXY hl'' hly hil hiX hlBi
            rwa [
              (X ↓∩ Subtype.val '' l.support.toSet).toFinset.sum_of_single_nonzero
                (fun a : X.Elem => l (hXXY.elem a) • (1 : Matrix X X Z2) a ⟨i, hiX⟩)
                ⟨i, hiX⟩ (by aesop) (by aesop),
              Matrix.one_apply_eq,
              smul_eq_mul,
              mul_one
            ] at hlBi'
          else if hiY : i.val ∈ Y then
            have hiy : i = hYXY.elem y
            · cases hl'' i hil with
              | inl hiy => exact SetCoe.ext hiy
              | inr hiD => simp_all
            rw [hiy]
            exact hly
          else
            exfalso
            exact i.property.casesOn hiX hiY
        else
          exact l.not_mem_support_iff.→ hil
      else
        exfalso
        have hlBd := congr_fun hlB d
        rw [Finsupp.linearCombination_apply] at hlBd
        have hlBd' : l.sum (fun i a => a • Matrix.fromRows 1 B₁ᵀ i.toSum d) = 0
        · simpa [Finsupp.sum] using hlBd
        have untransposed : l.sum (fun i a => a • B₁.prependId d i.toSum) = 0
        · rwa [←Matrix.transpose_transpose B₁.prependId, Matrix.prependId_transpose]
        have hyl : hYXY.elem y ∈ l.support
        · rwa [Finsupp.mem_support_iff]
        have hy1 : l (hYXY.elem y) • B₁.prependId d (hYXY.elem y).toSum = 1
        · rw [Fin2_eq_1_of_ne_0 hly, one_smul]
          simpa [hXY.not_mem_of_mem_right y.property] using Fin2_eq_1_of_ne_0 hd₁
        have h0 : ∀ a ∈ l.support, a.val ≠ y.val → l a • B₁.prependId d a.toSum = 0
        · intro a ha hay
          have hal := hl'' a ha
          if haX : a.val ∈ X then
            convert_to l a • B₁.prependId d ◩⟨a.val, haX⟩ = 0
            · simp [Subtype.toSum, haX]
            simp_rw [Matrix.fromCols_apply_inl]
            rw [smul_eq_mul, mul_eq_zero]
            right
            apply Matrix.one_apply_ne
            intro had
            rw [had] at hd₂
            apply hd₂
            aesop
          else if haY : a.val ∈ Y then
            exfalso
            cases hal with
            | inl hay' => exact hay hay'
            | inr haD₂ => simp_all
          else
            exfalso
            exact a.property.casesOn haX haY
        apply @one_ne_zero Z2
        rwa [Finsupp.sum,
          l.support.sum_of_single_nonzero (fun a : (X ∪ Y).Elem => l a • B₁.prependId d a.toSum) (hYXY.elem y) hyl,
          hy1] at untransposed
        intro i hil hiy
        apply h0 i hil
        intro contr
        apply hiy
        exact SetCoe.ext contr
    exact hM₂ (hSS' ▸ hM₁)
  · -- show `D₂ ⊆ D₁`
    by_contra hD
    rw [Set.not_subset_iff_exists_mem_not_mem] at hD
    -- otherwise `y ᕃ D₁` is dependent in `M₁` but indep in `M₂`
    have hM₁ : ¬ (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid.Indep (y.val ᕃ D₁)
    · rw [StandardRepr.toMatroid_indep_iff_elem', not_exists]
      intro hD₁
      erw [not_linearIndependent_iff]
      refine ⟨Finset.univ, 1, ?_, ⟨hYXY.elem y, by simp_all⟩, Finset.mem_univ _, Ne.symm (zero_ne_one' Z2)⟩
      -- there are exactly two `1`s in rows from `D₁` and all `0`s otherwise
      ext x
      simp only at x hD₁
      simp only [D₁, D₂, Matrix.transpose_apply, Pi.one_apply, Function.comp_apply, one_smul, Finset.sum_apply]
      show ∑ i : hD₁.elem.range.Elem, B₁.prependId x i.val.toSum = 0 -- in `Z2`
      suffices separated : B₁ x y + ∑ i : D₁.Elem, (1 : Matrix X X Z2) x i.val = 0
      · rw [Finset.sum_set_coe (f := (fun i : (X ∪ Y).Elem => B₁.prependId x i.toSum)),
          Set.toFinset_range,
          show Finset.univ.image hD₁.elem = hYXY.elem y ᕃ Finset.map ⟨hXXY.elem, hXXY.elem_injective⟩ { x : X | B₁ᵀ y x ≠ 0 } by
            aesop,
          Finset.sum_insert (by
            simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_map, exists_and_right, not_exists, not_not]
            intro a ⟨_, contradictory⟩
            have hay : a.val = y.val
            · simpa using contradictory
            have impossible : y.val ∈ X ∩ Y := ⟨hay ▸ a.property, y.property⟩
            rw [hXY.inter_eq] at impossible
            exact impossible)]
        convert separated
        · convert_to B₁.prependId x ◪y = B₁ x y
          · congr
            simpa [Subtype.toSum] using hXY.not_mem_of_mem_right y.property
          simp
        · simp [D₁]
          show
            ∑ i ∈ Finset.univ.filter (fun x : X => B₁ x y ≠ 0), (1 : Matrix X X Z2) x i =
            ∑ i : { x : X // B₁ x y ≠ 0 }, (1 : Matrix X X Z2) x i
          apply Finset.sum_subtype
          simp
      if hx : x ∈ D₁ then
        convert_to 1 + 1 = (0 : Z2) using 2
        · apply Fin2_eq_1_of_ne_0
          simpa [D₁] using hx
        · exact sum_elem_matrix_row_of_mem hx
        decide
      else
        convert_to 0 + 0 = (0 : Z2) using 2
        · simpa [D₁] using hx
        · exact sum_elem_matrix_row_of_nmem hx
        decide
    have hM₂ : (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid.Indep (y.val ᕃ D₁)
    · obtain ⟨d, hd₂, hd₁⟩ := hD
      simp
      have hDXY : Subtype.val '' D₁ ⊆ X ∪ Y := (Subtype.coe_image_subset X D₁).trans hXXY
      have hyXY : y.val ∈ X ∪ Y := hYXY y.property
      have hyDXY : y.val ᕃ Subtype.val '' D₁ ⊆ X ∪ Y := Set.insert_subset hyXY hDXY
      use Set.insert_subset hyXY hDXY
      -- if the coefficient in front of `y` is `0` then all coefficients must be `0`
      -- if the coefficient in front of `y` is `1` then the sum will always have `1` on `d` position
      rw [linearIndepOn_iff]
      intro l hl hlB
      have hl' : l.support.toSet ⊆ hyDXY.elem.range
      · rwa [Finsupp.mem_supported] at hl
      have hl'' : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D₁ :=
        fun e he => (hyDXY.elem_range ▸ hl') he
      if hly : l (hYXY.elem y) = 0 then
        ext i
        if hil : i ∈ l.support then
          if hiX : i.val ∈ X then
            have hlBi := congr_fun hlB ⟨i.val, hiX⟩
            rw [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum, Finset.sum_apply] at hlBi
            simp_rw [Pi.smul_apply, Function.comp_apply] at hlBi
            have : Fintype (X ↓∩ l.support.toSet).Elem
            · exact Set.Finite.fintype Subtype.finite
            have hlBi' : ∑ x ∈ (X ↓∩ Subtype.val '' l.support.toSet).toFinset, l (hXXY.elem x) • (1 : Matrix X X Z2) x ⟨i, hiX⟩ = 0
            · simpa using B_eq_B_of_same_matroid_same_X_aux hXXY hYXY hyDXY hl'' hly hil hiX hlBi
            rwa [
              (X ↓∩ Subtype.val '' l.support.toSet).toFinset.sum_of_single_nonzero
                (fun a : X.Elem => l (hXXY.elem a) • (1 : Matrix X X Z2) a ⟨i, hiX⟩)
                ⟨i, hiX⟩ (by aesop) (by aesop),
              Matrix.one_apply_eq,
              smul_eq_mul,
              mul_one
            ] at hlBi'
          else if hiY : i.val ∈ Y then
            have hiy : i = hYXY.elem y
            · cases hl'' i hil with
              | inl hiy => exact SetCoe.ext hiy
              | inr hiD => simp_all
            rw [hiy]
            exact hly
          else
            exfalso
            exact i.property.casesOn hiX hiY
        else
          exact l.not_mem_support_iff.→ hil
      else
        exfalso
        have hlBd := congr_fun hlB d
        rw [Finsupp.linearCombination_apply] at hlBd
        have hlBd' : l.sum (fun i a => a • Matrix.fromRows 1 B₂ᵀ i.toSum d) = 0
        · simpa [Finsupp.sum] using hlBd
        have untransposed : l.sum (fun i a => a • B₂.prependId d i.toSum) = 0
        · rwa [←Matrix.transpose_transpose B₂.prependId, Matrix.prependId_transpose]
        have hyl : hYXY.elem y ∈ l.support
        · rwa [Finsupp.mem_support_iff]
        have hy1 : l (hYXY.elem y) • B₂.prependId d (hYXY.elem y).toSum = 1
        · rw [Fin2_eq_1_of_ne_0 hly, one_smul]
          simpa [hXY.not_mem_of_mem_right y.property] using Fin2_eq_1_of_ne_0 hd₂
        have h0 : ∀ a ∈ l.support, a.val ≠ y.val → l a • B₂.prependId d a.toSum = 0
        · intro a ha hay
          have hal := hl'' a ha
          if haX : a.val ∈ X then
            convert_to l a • B₂.prependId d ◩⟨a.val, haX⟩ = 0
            · simp [Subtype.toSum, haX]
            simp_rw [Matrix.fromCols_apply_inl]
            rw [smul_eq_mul, mul_eq_zero]
            right
            apply Matrix.one_apply_ne
            intro had
            rw [had] at hd₁
            apply hd₁
            aesop
          else if haY : a.val ∈ Y then
            exfalso
            cases hal with
            | inl hay' => exact hay hay'
            | inr haD₁ => simp_all
          else
            exfalso
            exact a.property.casesOn haX haY
        apply @one_ne_zero Z2
        rwa [Finsupp.sum,
          l.support.sum_of_single_nonzero (fun a : (X ∪ Y).Elem => l a • B₂.prependId d a.toSum) (hYXY.elem y) hyl,
          hy1] at untransposed
        intro i hil hiy
        apply h0 i hil
        intro contr
        apply hiy
        exact SetCoe.ext contr
    exact (hSS' ▸ hM₁) hM₂

/-- If two standard representations of the same binary matroid have the same base, they are identical. -/
lemma ext_standardRepr_of_same_matroid_same_X {S₁ S₂ : StandardRepr α Z2} [Fintype S₁.X]
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    S₁ = S₂ := by
  have hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
  apply standardRepr_eq_standardRepr_of_B_eq_B hXX hYY
  apply B_eq_B_of_same_matroid_same_X
  convert hSS
  cc
