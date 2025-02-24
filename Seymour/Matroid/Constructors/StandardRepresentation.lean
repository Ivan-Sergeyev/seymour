import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.ForMathlib.MatrixLI

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
lemma StandardRepr.toVectorMatroid_X [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.X = S.X :=
  rfl

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_Y [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.Y = S.X ∪ S.Y :=
  rfl

/-- If a vector matroid has a standard representation matrix `B`, its full representation matrix is `[1 | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.A = (S.B.prependId · ∘ Subtype.toSum) :=
  rfl

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.E = S.X ∪ S.Y :=
  rfl

instance {S : StandardRepr α R} [Zero R] [One R] [hSX : Finite S.X] : Finite S.toVectorMatroid.X :=
  hSX

lemma StandardRepr.toVectorMatroid_indep_iff [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

@[simp]
lemma StandardRepr.toVectorMatroid_indep_iff' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) := by
  simp

lemma StandardRepr.toVectorMatroid_indep_iff_elem [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ hI.elem.range := by
  rw [StandardRepr.toVectorMatroid_indep_iff]
  unfold HasSubset.Subset.elem
  aesop

lemma StandardRepr.toVectorMatroid_indep_iff_elem' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem I

lemma StandardRepr.toVectorMatroid_indep_iff_elem'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) hI.elem.range := by
  simpa using S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem))ᵀ := by
  simp only [StandardRepr.toVectorMatroid, VectorMatroid.toMatroid_indep, VectorMatroid.indepCols_iff_submatrix]
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependIdᵀ.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  StandardRepr.toVectorMatroid_indep_iff_submatrix S I

lemma StandardRepr.toVectorMatroid_indep_iff_submatrix'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.Bᵀ.uppendId.submatrix (Subtype.toSum ∘ hI.elem) id) := by
  simpa using S.toVectorMatroid_indep_iff_submatrix' I

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr [Semiring R] (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, S.toVectorMatroid = M := by
  sorry

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_isBase [Semiring R] {B : Set α}
    (M : VectorMatroid α R) (hMB : M.toMatroid.IsBase B) :
    ∃ S : StandardRepr α R, M.X = B ∧ S.toVectorMatroid = M := by
  have hBY := hMB.subset_ground
  sorry

/-- Construct a matroid from a standard representation. -/
def StandardRepr.toMatroid [Semiring R] (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp high]
lemma StandardRepr.toMatroid_E [Semiring R] (S : StandardRepr α R) :
    S.toMatroid.E = S.X ∪ S.Y :=
  rfl

lemma StandardRepr.toMatroid_indep_iff [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff I

lemma StandardRepr.toMatroid_indep_iff' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff' I

lemma StandardRepr.toMatroid_indep_iff'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff'' I

lemma StandardRepr.toMatroid_indep_iff_elem [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependId · ∘ Subtype.toSum)ᵀ hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem I

@[simp high]
lemma StandardRepr.toMatroid_indep_iff_elem' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toMatroid_indep_iff_elem'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R (S.Bᵀ.uppendId ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem'' I

lemma StandardRepr.toMatroid_indep_iff_submatrix [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem))ᵀ :=
  S.toVectorMatroid_indep_iff_submatrix I

lemma StandardRepr.toMatroid_indep_iff_submatrix' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependIdᵀ.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  S.toVectorMatroid_indep_iff_submatrix' I

lemma StandardRepr.toMatroid_indep_iff_submatrix'' [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.Bᵀ.uppendId.submatrix (Subtype.toSum ∘ hI.elem) id) :=
  S.toVectorMatroid_indep_iff_submatrix'' I

@[simp]
lemma StandardRepr.toMatroid_indep [Semiring R] (S : StandardRepr α R) :
    S.toMatroid.Indep = (∃ hI : · ⊆ S.X ∪ S.Y, LinearIndepOn R (S.B.prependIdᵀ ∘ Subtype.toSum) hI.elem.range) := by
  ext I
  exact S.toVectorMatroid_indep_iff_elem' I

lemma StandardRepr.toMatroid_indep' [Semiring R] (S : StandardRepr α R) :
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
    simp [Matrix.submatrix, Subtype.toSum]
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

/-- If two standard representations of the same matroid have the same base, they are identical. -/
lemma ext_standardRepr_of_same_matroid_same_X [Semiring R] {S₁ S₂ : StandardRepr α R}
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    S₁ = S₂ := by
  sorry
