import Seymour.Matroid.Constructors.VectorMatroid


variable {α : Type} [DecidableEq α]

-- Having both `Matroid.IsRepresentedBy` and `Matroid.IsRepresentableOver` is sus since the defs are independent of each other.

/-- Matroid `M` is represented by matrix `A` if vector matroid `M[A]` is exactly `M` -/
def Matroid.IsRepresentedBy {R X Y : Type} [Ring R] (M : Matroid α) (A : Matrix X Y R) : Prop :=
  ∃ c : Y ↪ α, M = (VectorMatroid.mk X Y A c).toMatroid

/-- Matroid `M` can be represented over ring `R` if it can be represented by some matrix with entries in `R` -/
def Matroid.IsRepresentableOver (M : Matroid α) (R : Type) [Ring R] : Prop :=
  ∃ M' : VectorMatroid α R, M'.toMatroid = M

lemma Matroid.isRepresentableOver_iff (M : Matroid α) (R : Type) [Ring R] :
    M.IsRepresentableOver R ↔ ∃ X Y : Type, ∃ hY : Fintype Y, ∃ A : Matrix X Y R, M.IsRepresentedBy A := by
  sorry -- TODO important sanity check

/-- Matroid `M` is representable if it is representable over some field -/
def Matroid.IsRepresentable (M : Matroid α) : Prop :=
  ∃ R : Type, ∃ _R : Ring R, M.IsRepresentableOver R

/-- If a matroid is representable over a field, then its dual is also representable over that field -/
lemma Matroid.isRepresentable_iff_dual_isRepresentable {R : Type} [Ring R] {M : Matroid α} :
    M.IsRepresentableOver R → M✶.IsRepresentableOver R := by
  sorry
  -- todo: want to apply `VectorMatroid.dual_exists_standard_repr`, but this requires `[DecidableEq α]`
