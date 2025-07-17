import Seymour.Basic.Fin

/-!
# SignType and its images

This file provides lemmas about `SignType.cast.range` (that is, `{0, ±1}` in various types) that are not present in Mathlib.
-/

lemma zero_iff_ratCast_zero_of_in_signTypeCastRange {a : ℚ} (ha : a ∈ SignType.cast.range) :
    a = 0 ↔ (a.cast : Z2) = 0 := by
  constructor <;> intro h0
  · rw [h0, Rat.cast_zero]
  · obtain ⟨s, rfl⟩ := ha
    cases s <;> simp_all

variable {R : Type*}

@[simp high]
lemma zero_in_signTypeCastRange [NonAssocRing R] : (0 : R) ∈ SignType.cast.range :=
  ⟨0, rfl⟩

@[simp high]
lemma one_in_signTypeCastRange [NonAssocRing R] : (1 : R) ∈ SignType.cast.range :=
  ⟨1, rfl⟩

@[simp high]
lemma neg_one_in_signTypeCastRange [NonAssocRing R] : (-1 : R) ∈ SignType.cast.range :=
  ⟨-1, rfl⟩

@[simp]
lemma SignType.cast_ne_one_add_one [Ring R] [CharZero R] (s : SignType) : s.cast ≠ (1 : R) + (1 : R) := by
  cases s <;> norm_num

@[simp]
lemma SignType.cast_ne_neg_one_sub_one [Ring R] [CharZero R] (s : SignType) : s.cast ≠ (-1 : R) - (1 : R) := by
  cases s <;> norm_num

@[simp]
lemma SignType.cast_ne_neg_one_add_neg_one [Ring R] [CharZero R] (s : SignType) : s.cast ≠ (-1 : R) + (-1 : R) := by
  cases s <;> norm_num

lemma in_signTypeCastRange_mul_in_signTypeCastRange [NonAssocRing R] {a b : R}
    (ha : a ∈ SignType.cast.range) (hb : b ∈ SignType.cast.range) :
    a * b ∈ SignType.cast.range := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨_, SignType.coe_mul a' b'⟩

lemma neg_one_mul_in_signTypeCastRange [NonAssocRing R] {a : R}
    (ha : a ∈ SignType.cast.range) :
    (-1) * a ∈ SignType.cast.range :=
  in_signTypeCastRange_mul_in_signTypeCastRange ⟨-1, rfl⟩ ha

lemma neg_in_signTypeCastRange [NonAssocRing R] {a : R}
    (ha : a ∈ SignType.cast.range) :
    -a ∈ SignType.cast.range := by
  rw [neg_eq_neg_one_mul]
  exact neg_one_mul_in_signTypeCastRange ha

lemma in_signTypeCastRange_of_neg_one_mul [NonAssocRing R] {a : R}
    (ha : (-1) * a ∈ SignType.cast.range) :
    a ∈ SignType.cast.range := by
  rw [←neg_neg a, neg_eq_neg_one_mul]
  apply neg_one_mul_in_signTypeCastRange
  rwa [neg_eq_neg_one_mul]

lemma in_signTypeCastRange_of_neg [NonAssocRing R] {a : R}
    (ha : -a ∈ SignType.cast.range) :
    a ∈ SignType.cast.range := by
  rw [neg_eq_neg_one_mul] at ha
  exact in_signTypeCastRange_of_neg_one_mul ha

lemma in_signTypeCastRange_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ SignType.cast.range ↔ |a| ∈ SignType.cast.range := by
  constructor
  · rintro ⟨(-|-|-), rfl⟩ <;> simp
  · intro ⟨s, hs⟩
    symm at hs
    cases s with
    | zero =>
      rw [SignType.zero_eq_zero, SignType.coe_zero, abs_eq_zero] at hs
      exact ⟨0, hs.symm⟩
    | pos =>
      rw [SignType.pos_eq_one, abs_eq_max_neg, max_eq_iff] at hs
      cases hs with
      | inl poz =>
        exact ⟨1, poz.left.symm⟩
      | inr nig =>
        use -1
        rw [neg_eq_iff_eq_neg] at nig
        exact nig.left.symm
    | neg =>
      exfalso
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      have h0 := (abs_nonneg a).trans_eq hs
      norm_num at h0

lemma inv_eq_self_of_in_signTypeCastRange [DivisionRing R] {a : R} (ha : a ∈ SignType.cast.range) :
    1 / a = a := by
  obtain ⟨s, rfl⟩ := ha
  cases s <;> simp

lemma neg_one_pow_in_signTypeCastRange [Ring R] (k : ℕ) :
    (-1 : R) ^ k ∈ SignType.cast.range := by
  if hk : Even k then
    rw [hk.neg_one_pow]
    simp
  else
    rw [Nat.not_even_iff_odd] at hk
    simp [hk.neg_one_pow]

lemma neg_one_pow_mul_in_signTypeCastRange [Ring R] {a : R} (ha : a ∈ SignType.cast.range) (k : ℕ) :
    (-1) ^ k * a ∈ SignType.cast.range :=
  in_signTypeCastRange_mul_in_signTypeCastRange (neg_one_pow_in_signTypeCastRange k) ha
