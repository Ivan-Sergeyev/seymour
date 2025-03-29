import Seymour.Basic.Basic


lemma zero_iff_ratCast_zero_of_in_signTypeCastRange {a : ℚ} (ha : a ∈ SignType.cast.range) :
    a = 0 ↔ (a.cast : Z2) = 0 := by
  constructor <;> intro h0
  · rw [h0, Rat.cast_zero]
  · obtain ⟨s, rfl⟩ := ha
    cases s <;> simp_all

lemma ratCast_eq_intCast_ratFloor_of_in_signTypeCastRange {a : ℚ} (ha : a ∈ SignType.cast.range) :
    (a.cast : Z2) = (a.floor.cast : Z2) := by
  obtain ⟨s, hs⟩ := ha
  cases s <;> aesop

variable {R : Type}

@[simp high]
lemma zero_in_signTypeCastRange [Ring R] : (0 : R) ∈ SignType.cast.range :=
  ⟨0, rfl⟩

@[simp high]
lemma neg_one_in_signTypeCastRange [Ring R] : (-1 : R) ∈ SignType.cast.range :=
  ⟨-1, rfl⟩

@[simp high]
lemma one_in_signTypeCastRange [Ring R] : (1 : R) ∈ SignType.cast.range :=
  ⟨1, rfl⟩

lemma in_signTypeCastRange_mul_in_signTypeCastRange [Ring R] {a b : R}
    (ha : a ∈ SignType.cast.range) (hb : b ∈ SignType.cast.range) :
    a * b ∈ SignType.cast.range := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨_, SignType.coe_mul a' b'⟩

lemma neg_one_mul_in_signTypeCastRange [Ring R] {a : R}
    (ha : a ∈ SignType.cast.range) :
    (-1) * a ∈ SignType.cast.range :=
  in_signTypeCastRange_mul_in_signTypeCastRange ⟨-1, rfl⟩ ha

lemma in_signTypeCastRange_of_neg_one_mul_self [Ring R] {a : R}
    (ha : (-1) * a ∈ SignType.cast.range) :
    a ∈ SignType.cast.range := by
  rw [←neg_neg a, neg_eq_neg_one_mul]
  apply neg_one_mul_in_signTypeCastRange
  rwa [neg_eq_neg_one_mul]

lemma in_signTypeCastRange_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ SignType.cast.range ↔ |a| ∈ SignType.cast.range := by
  constructor
  · rintro ⟨(h | h | h), rfl⟩ <;> simp
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
      | inr neg =>
        use -1
        rw [neg_eq_iff_eq_neg] at neg
        exact neg.left.symm
    | neg =>
      exfalso
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      have h0 := (abs_nonneg a).trans_eq hs
      norm_num at h0

lemma inv_eq_self_of_in_signTypeCastRange [Field R] {a : R} (ha : a ∈ SignType.cast.range) :
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
