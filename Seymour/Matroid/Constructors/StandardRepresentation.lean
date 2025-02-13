import Seymour.Matroid.Constructors.BinaryMatroid


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

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.toMatroid.E = S.X ∪ S.Y :=
  rfl

/-- Full representation matrix of vector matroid is `[1 | B]`. -/
@[simp]
lemma StandardRepr.toVectorMatroid_A [Semiring R] (S : StandardRepr α R) :
    S.toVectorMatroid.A = (S.B.prependId · ∘ Subtype.toSum) :=
  rfl

/-- Set is independent in the vector matroid iff
    the corresponding multiset of columns of `[1 | B]` is linearly independent over `R`. -/
lemma StandardRepr.toVectorMatroid_indep_iff [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (fun i : I => (S.B.prependId · (hI.elem i).toSum)) := by
  rfl

/-- Every vector matroid has a standard representation. -/
lemma VectorMatroid.exists_standardRepr [Semiring R] (M : VectorMatroid α R) :
    ∃ S : StandardRepr α R, S.toVectorMatroid = M := by
  sorry

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma VectorMatroid.exists_standardRepr_base [Semiring R] {B : Set α}
    (M : VectorMatroid α R) (hMB : M.toMatroid.Base B) (hBY : B ⊆ M.Y) :
    ∃ S : StandardRepr α R, M.X = B ∧ S.toVectorMatroid = M := by
  sorry

/-- Construct a matroid from standard representation. -/
def StandardRepr.toMatroid [Semiring R] (S : StandardRepr α R) : Matroid α :=
  S.toVectorMatroid.toMatroid

/-- Set is independent in the resulting matroid iff
    the corresponding multiset of columns of `[1 | B]` is linearly independent over `R`. -/
@[simp]
lemma StandardRepr.toMatroid_indep_iff [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (fun i : I => (S.B.prependId · (hI.elem i).toSum)) := by
  rfl

lemma StandardRepr.toMatroid_indep_iff_submatrix [Semiring R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R (S.B.prependId.submatrix id (Subtype.toSum ∘ hI.elem)).transpose := by
  rfl

/-- The identity matrix has linearly independent rows. -/
lemma Matrix.one_linearIndependent [Ring R] : LinearIndependent R (1 : Matrix α α R) := by
-- Riccardo Brasca proved:
  rw [linearIndependent_iff]
  intro l hl
  ext j
  simpa [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum_apply', Matrix.one_apply] using congr_fun hl j

/-- The image of all rows of a standard representation is a base in the resulting matroid. -/
lemma StandardRepr.toMatroid_base [Ring R] (S : StandardRepr α R) :
    S.toMatroid.Base (Set.range (Subtype.val ∘ Sum.toUnion ∘ @Sum.inl S.X S.Y)) := by
  apply Matroid.Indep.base_of_forall_insert
  · rw [StandardRepr.toMatroid_indep_iff_submatrix]
    use (fun a ha => by simp [Sum.toUnion] at ha; aesop)
    show LinearIndependent R (S.B.prependId.transpose.submatrix _ id)
    rw [Matrix.transpose_fromCols, Matrix.transpose_one]
    convert @Matrix.one_linearIndependent S.X R _ _
    · aesop
    sorry
  · intro e he
    sorry --  if you add anything extra to the identity matrix, it becomes singular
