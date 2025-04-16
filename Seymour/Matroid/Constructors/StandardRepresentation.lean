import Seymour.Basic.Sets
import Seymour.Matrix.LinearIndependence
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Elementary.Basic
import Seymour.Matroid.Constructors.TODOs

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

/-- Convert standard representation of a vector matroid to a full representation. -/
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
  simp_rw [←Matrix.prependId_transpose]
  rfl -- TODO reëxamine simp-normal form!

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
  rfl -- TODO reëxamine simp-normal form!

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependIdᵀ.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  S.toVectorMatroid_indep_iff_submatrix I

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix'' [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.Bᵀ.uppendId.submatrix (Subtype.toSum ∘ hI.elem) id) := by
  simpa using S.toVectorMatroid_indep_iff_submatrix' I

attribute [local ext] StandardRepr in
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

/-- Construct a matroid from a standard representation. -/
def StandardRepr.toMatroid [DivisionRing R] (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

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

lemma VectorMatroid.isFinitary [Field R] (M : VectorMatroid α R) : M.toMatroid.Finitary := by
  constructor
  intro I hI
  simp
  wlog hIY : I ⊆ M.toMatroid.E
  · exfalso
    rw [Set.not_subset_iff_exists_mem_not_mem] at hIY
    obtain ⟨x, hx, hxE⟩ := hIY
    specialize hI { x } (Set.singleton_subset_iff.← hx) (Set.finite_singleton x)
    exact hxE (hI.subset_ground rfl)
  use hIY
  rw [linearIndepOn_iff]
  intro s hs hAs
  rw [Finsupp.mem_supported] at hs
  specialize hI s.support.toSet (by rw [Set.image_subset_iff]; convert hs; aesop) (Subtype.val '' s.support).toFinite
  simp [VectorMatroid.toMatroid_indep_iff_elem] at hI
  rw [linearIndepOn_iff] at hI
  exact hI s (fun a ha => ⟨⟨a.val, Set.mem_image_of_mem Subtype.val ha⟩, by simp⟩) hAs

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_isBase [Field R] {G : Set α}
    (M : VectorMatroid α R) (hMG : M.toMatroid.IsBase G) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = M.toMatroid := by
  have hGY : G ⊆ M.Y := hMG.subset_ground
  -- First, prove that `G`-cols of `A` span the entire vector space generated by `Y`-cols of `A` (i.e., the entire colspace).
  have hRAGY : Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range = Submodule.span R M.Aᵀ.range
  · have easy : (M.Aᵀ.submatrix hGY.elem id).range ⊆ M.Aᵀ.range
    · intro v ⟨j, hjv⟩
      exact ⟨hGY.elem j, hjv⟩
    have difficult : M.Aᵀ.range ≤ Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range
    · by_contra contr
      obtain ⟨v, ⟨j, hjv⟩, hvG⟩ : ∃ v : M.X → R, v ∈ M.Aᵀ.range ∧ v ∉ Submodule.span R (M.Aᵀ.submatrix hGY.elem id).range :=
        Set.not_subset.→ contr
      have hj : j.val ∉ G
      · intro hjG
        apply hvG
        have hv : v ∈ (M.Aᵀ.submatrix hGY.elem id).range
        · aesop
        rw [Submodule.mem_span]
        exact (fun _ hR => hR hv)
      have hMvG : M.toMatroid.Indep (j.val ᕃ G)
      · obtain ⟨-, hAG⟩ := hMG.indep
        use Set.insert_subset_iff.← ⟨j.property, hGY⟩
        convert_to LinearIndepOn R M.Aᵀ (j ᕃ (M.Y ↓∩ G))
        · aesop
        rw [linearIndepOn_insert_iff]
        use hAG
        intro hjR
        exfalso
        apply hvG
        rw [←hjv]
        convert hjR
        aesop
      exact M.toMatroid.base_not_ssubset_indep hMG hMvG (Set.ssubset_insert hj)
    exact le_antisymm (Submodule.span_mono easy) (Submodule.span_le.← difficult)
  obtain ⟨-, lin_indep⟩ := hMG.indep
  let B : Basis G R (Submodule.span R M.Aᵀ.range)
  · apply Basis.mk (v := fun j : G.Elem => ⟨M.Aᵀ (hGY.elem j), in_submoduleSpan_range M.Aᵀ (hGY.elem j)⟩)
    · unfold LinearIndepOn at lin_indep
      rw [linearIndependent_iff'] at lin_indep ⊢
      intro s g hsg i hi
      let e : (M.Y ↓∩ G).Elem ≃ G.Elem :=
        ⟨G.restrictPreimage Subtype.val, (⟨hGY.elem ·, by simp⟩), congr_fun rfl, congr_fun rfl⟩
      have hsA : ∑ i ∈ s.map e.symm.toEmbedding, (g ∘ e) i • M.Aᵀ i = 0
      · rw [Subtype.ext_iff_val, ZeroMemClass.coe_zero] at hsg
        rw [←hsg]
        convert_to ∑ x ∈ s, g x • M.Aᵀ (e.symm x) = ∑ x ∈ s, g x • M.Aᵀ (hGY.elem x)
        · simp
        · simp
        rfl
      exact lin_indep (s.map e.symm.toEmbedding) (g ∘ e) hsA (e.symm i) (Finset.mem_map_equiv.← hi)
    · apply le_of_eq
      -- Christian Merten's idea:
      apply Submodule.map_injective_of_injective (Submodule.span R M.Aᵀ.range).subtype_injective
      simp [Submodule.map_span, ←hRAGY, ←Set.range_comp, Function.comp_def]
      rfl
  let C : Matrix G M.Y R := Matrix.of (fun i : G => fun j : M.Y => B.coord i ⟨M.Aᵀ j, in_submoduleSpan_range M.Aᵀ j⟩)
  have hYGY : M.Y \ G ⊆ M.Y := Set.diff_subset
  use ⟨G, M.Y \ G, Set.disjoint_sdiff_right, C.submatrix id hYGY.elem,
    (Classical.propDecidable <| · ∈ G), (Classical.propDecidable <| · ∈ M.Y \ G)⟩
  constructor
  · simp
  ext I hIGY
  · aesop
  have hB :
    ∀ j : α, ∀ g : G, ∀ hjy : j ∈ M.Y, ∀ hjg : j ∈ G, ∀ hjR : M.Aᵀ ⟨j, hjy⟩ ∈ Submodule.span R M.Aᵀ.range,
      B.repr ⟨M.Aᵀ ⟨j, hjy⟩, hjR⟩ g = B.repr (B ⟨j, hjg⟩) g
  · simp [B]
  simp only [StandardRepr.toMatroid_indep_iff_elem', VectorMatroid.toMatroid_indep_iff_elem,
    Matrix.prependId_transpose, Matrix.transpose_submatrix, Set.union_diff_self]
  have hGYY : G ∪ M.Y = M.Y := Set.union_eq_self_of_subset_left hGY
  constructor
  · intro ⟨hI, hRCI⟩
    use hGYY ▸ hI
    classical
    apply todo_right lin_indep hGY hYGY (hGYY ▸ hI) hIGY hB
    convert hRCI
  · intro ⟨hI, hRAI⟩
    use hGYY.symm ▸ hI
    classical
    convert todo_left hGY hYGY hI hIGY hB hRAI

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr [Field R] (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, S.toMatroid = M.toMatroid := by
  peel M.exists_standardRepr_isBase M.toMatroid.exists_isBase.choose_spec with hS
  exact hS.right

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

private lemma B_eq_B_of_same_matroid_same_X_aux {X Y : Set α} {B : Matrix Y X Z2} {D : Set X} {y : Y}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} (hXXY : X ⊆ X ∪ Y) (hYXY : Y ⊆ X ∪ Y) -- redundant but keep
    {l : (X ∪ Y).Elem →₀ Z2} (hl : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D) (hly : l (Set.inclusion hYXY y) = 0)
    {i : (X ∪ Y).Elem} (hiX : i.val ∈ X) (hlBi : ∑ a ∈ l.support, l a • B.uppendId a.toSum ⟨i, hiX⟩ = 0) :
    ∑ a ∈ (l.support.image Subtype.val).subtype (· ∈ X),
      l (hXXY.elem a) • B.uppendId (Set.inclusion hXXY a).toSum ⟨i, hiX⟩ = 0 := by
  rw [←Finset.sum_finset_coe] at hlBi
  convert hlBi
  apply Finset.sum_bij (fun a ha => ⟨hXXY.elem a, by simpa using ha⟩)
  · simp
  · simp
  · intro h p
    simp only [Finset.coe_sort_coe, HasSubset.Subset.elem, Finset.mem_subtype, Finset.mem_image,
      Finsupp.mem_support_iff, ne_eq, Subtype.exists, Set.mem_union, exists_and_right,
      exists_eq_right, Subtype.coe_prop, true_or, exists_true_left]
    use h
    simp only [Subtype.coe_eta, exists_prop, and_true]
    refine ⟨?_, (l.mem_support_toFun h).→ (by simp)⟩
    have h₁ : ↑h.val ∈ Subtype.val '' D := by
      rcases hl h (by simp) with (hp | hp)
      · have : h.val = Set.inclusion hYXY y := by
          suffices h.val.val = (Set.inclusion hYXY y).val by exact Subtype.coe_inj.→ this
          rw [Set.coe_inclusion hYXY y]
          exact hp
        rw [← this] at hly
        exact absurd hly (l.mem_support_iff.→ (by simp))
      · exact hp
    have h₂ : Subtype.val '' D ⊆ X := by
      rw [Set.image, Set.setOf_subset]
      rintro hx ⟨⟨_, ha⟩, ⟨_, rfl⟩⟩
      exact ha
    exact Set.mem_of_mem_of_subset h₁ h₂
  · intro _ _
    rfl

set_option maxHeartbeats 1000000 in
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
        simp_rw [D₁, Set.mem_setOf_eq]
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
  on_goal 1 => let D := D₁; let Dₒ := D₂; let B := B₁; let Bₒ := B₂
  on_goal 2 => let D := D₂; let Dₒ := D₁; let B := B₂; let Bₒ := B₁
  all_goals
    by_contra hD
    rw [Set.not_subset_iff_exists_mem_not_mem] at hD
    -- otherwise `y ᕃ Dₒ` is dependent in `Mₒ` but indep in `M`
    have hMₒ : ¬ (StandardRepr.mk X Y hXY Bₒ hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · rw [StandardRepr.toMatroid_indep_iff_elem', not_exists]
      intro hDₒ
      erw [not_linearIndependent_iff]
      refine ⟨Finset.univ, 1, ?_, ⟨hYXY.elem y, by simp_all⟩, Finset.mem_univ _, Ne.symm (zero_ne_one' Z2)⟩
      -- there are exactly two `1`s in rows from `Dₒ` and all `0`s otherwise
      ext x
      simp only at x hDₒ
      simp only [D, Dₒ, Matrix.transpose_apply, Pi.one_apply, Function.comp_apply, one_smul, Finset.sum_apply]
      show ∑ i : hDₒ.elem.range.Elem, Bₒ.prependId x i.val.toSum = 0 -- in `Z2`
      suffices separated : Bₒ x y + ∑ i : Dₒ.Elem, (1 : Matrix X X Z2) x i.val = 0
      · rw [Finset.sum_set_coe (f := (fun i : (X ∪ Y).Elem => Bₒ.prependId x i.toSum)),
          Set.toFinset_range,
          show Finset.univ.image hDₒ.elem = hYXY.elem y ᕃ Finset.map ⟨hXXY.elem, hXXY.elem_injective⟩ { x : X | Bₒᵀ y x ≠ 0 } by
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
        · convert_to Bₒ.prependId x ◪y = Bₒ x y
          · congr
            simpa [Subtype.toSum] using hXY.not_mem_of_mem_right y.property
          simp
        · simp [Dₒ]
          show
            ∑ i ∈ Finset.univ.filter (fun x : X => Bₒ x y ≠ 0), (1 : Matrix X X Z2) x i =
            ∑ i : { x : X // Bₒ x y ≠ 0 }, (1 : Matrix X X Z2) x i
          apply Finset.sum_subtype
          simp
      if hx : x ∈ Dₒ then
        convert_to 1 + 1 = (0 : Z2) using 2
        · apply Fin2_eq_1_of_ne_0
          simpa [Dₒ] using hx
        · exact sum_elem_matrix_row_of_mem hx
        decide
      else
        convert_to 0 + 0 = (0 : Z2) using 2
        · simpa [Dₒ, D₁, D₂] using hx
        · exact sum_elem_matrix_row_of_nmem hx
        decide
    have hM : (StandardRepr.mk X Y hXY B hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · obtain ⟨d, hd, hdₐ⟩ := hD
      simp
      have hDXY : Subtype.val '' Dₒ ⊆ X ∪ Y := (Subtype.coe_image_subset X Dₒ).trans hXXY
      have hyXY : y.val ∈ X ∪ Y := hYXY y.property
      have hyDXY : y.val ᕃ Subtype.val '' Dₒ ⊆ X ∪ Y := Set.insert_subset hyXY hDXY
      use Set.insert_subset hyXY hDXY
      -- if the coefficient in front of `y` is `0` then all coefficients must be `0`
      -- if the coefficient in front of `y` is `1` then the sum will always have `1` on `d` position
      rw [linearIndepOn_iff]
      intro l hl hlB
      have hl' : l.support.toSet ⊆ hyDXY.elem.range
      · rwa [Finsupp.mem_supported] at hl
      have hl'' : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' Dₒ :=
        fun e he => (hyDXY.elem_range ▸ hl') he
      if hly : l (hYXY.elem y) = 0 then
        ext i
        if hil : i ∈ l.support then
          if hiX : i.val ∈ X then
            have hlBi := congr_fun hlB ⟨i.val, hiX⟩
            rw [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum, Finset.sum_apply] at hlBi
            simp_rw [Pi.smul_apply, Function.comp_apply] at hlBi
            have hlBi' : ∑ x ∈ (l.support.image Subtype.val).subtype (· ∈ X), l (hXXY.elem x) • (1 : Matrix X X Z2) x ⟨i, hiX⟩ = 0
            · simpa using B_eq_B_of_same_matroid_same_X_aux hXXY hYXY hl'' hly hiX hlBi
            rwa [
              ((l.support.image Subtype.val).subtype (· ∈ X)).sum_of_single_nonzero
                (fun a : X.Elem => l (hXXY.elem a) • (1 : Matrix X X Z2) a ⟨i, hiX⟩)
                ⟨i, hiX⟩ (by simp_all) (fun _ _ _ ↦ by simp_all),
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
        have hlBd' : l.sum (fun i a => a • Matrix.fromRows 1 Bᵀ i.toSum d) = 0
        · simpa [Finsupp.sum] using hlBd
        have untransposed : l.sum (fun i a => a • B.prependId d i.toSum) = 0
        · rwa [←Matrix.transpose_transpose B.prependId, Matrix.prependId_transpose]
        have hyl : hYXY.elem y ∈ l.support
        · rwa [Finsupp.mem_support_iff]
        have hy1 : l (hYXY.elem y) • B.prependId d (hYXY.elem y).toSum = 1
        · rw [Fin2_eq_1_of_ne_0 hly, one_smul]
          simpa [hXY.not_mem_of_mem_right y.property] using Fin2_eq_1_of_ne_0 hd
        have h0 : ∀ a ∈ l.support, a.val ≠ y.val → l a • B.prependId d a.toSum = 0
        · intro a ha hay
          have hal := hl'' a ha
          if haX : a.val ∈ X then
            convert_to l a • B.prependId d ◩⟨a.val, haX⟩ = 0
            · simp [Subtype.toSum, haX]
            simp_rw [Matrix.fromCols_apply_inl]
            rw [smul_eq_mul, mul_eq_zero]
            right
            apply Matrix.one_apply_ne
            intro had
            rw [had] at hd
            apply hd
            aesop
          else if haY : a.val ∈ Y then
            exfalso
            cases hal with
            | inl hay' => exact hay hay'
            | inr haDₒ => simp_all
          else
            exfalso
            exact a.property.casesOn haX haY
        apply @one_ne_zero Z2
        rwa [Finsupp.sum,
          l.support.sum_of_single_nonzero (fun a : (X ∪ Y).Elem => l a • B.prependId d a.toSum) (hYXY.elem y) hyl,
          hy1] at untransposed
        intro i hil hiy
        apply h0 i hil
        intro contr
        apply hiy
        exact SetCoe.ext contr
  · exact hMₒ (hSS' ▸ hM)
  · exact (hSS' ▸ hMₒ) hM

/-- If two standard representations of the same binary matroid have the same base, they are identical. -/
lemma ext_standardRepr_of_same_matroid_same_X {S₁ S₂ : StandardRepr α Z2} [Fintype S₁.X]
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    S₁ = S₂ := by
  have hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
  apply standardRepr_eq_standardRepr_of_B_eq_B hXX hYY
  apply B_eq_B_of_same_matroid_same_X
  convert hSS
  cc
