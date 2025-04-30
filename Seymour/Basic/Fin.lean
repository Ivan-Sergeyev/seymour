import Seymour.Basic.Basic


lemma fin1_eq_fin1 (a b : Fin 1) : a = b := by
  omega

lemma fin2_eq_1_of_ne_0 {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  omega

lemma fin2_eq_0_of_ne_1 {a : Fin 2} (ha : a ≠ 1) : a = 0 := by
  omega

lemma fin3_eq_2_of_ne_0_1 {a : Fin 3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 := by
  omega

lemma fin3_eq_1_of_ne_0_2 {a : Fin 3} (ha0 : a ≠ 0) (ha2 : a ≠ 2) : a = 1 := by
  omega

lemma fin3_eq_0_of_ne_1_2 {a : Fin 3} (ha1 : a ≠ 1) (ha2 : a ≠ 2) : a = 0 := by
  omega

@[aesop unsafe 50% forward]
lemma Z2_eq_1_of_ne_0 {a : Z2} (ha : a ≠ 0) : a = 1 :=
  fin2_eq_1_of_ne_0 ha

@[aesop unsafe 50% forward]
lemma Z2_eq_0_of_ne_1 {a : Z2} (ha : a ≠ 1) : a = 0 :=
  fin2_eq_0_of_ne_1 ha

lemma Z3_eq_2_of_ne_0_1 {a : Z3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 :=
  fin3_eq_2_of_ne_0_1 ha0 ha1

lemma Z3_eq_1_of_ne_0_2 {a : Z3} (ha0 : a ≠ 0) (ha2 : a ≠ 2) : a = 1 :=
  fin3_eq_1_of_ne_0_2 ha0 ha2

lemma Z3_eq_0_of_ne_1_2 {a : Z3} (ha1 : a ≠ 1) (ha2 : a ≠ 2) : a = 0 :=
  fin3_eq_0_of_ne_1_2 ha1 ha2

lemma Z2_eq_0_or_1 (a : Z2) : a = 0 ∨ a = 1 := by
  rw [←ZMod.val_eq_zero]
  by_cases ha : a.val = 0
  · left
    exact ha
  · fin_cases a
    · absurd ha
      rfl
    · right
      rfl

lemma Z2_ext {a b : Z2} : a = b ↔ a.val = b.val := by
  constructor
  <;> intro hab
  · exact congr_arg ZMod.val hab
  · cases a
    cases b
    simp only [ZMod.val, Nat.reduceAdd] at hab
    simp only [hab]

lemma Z2val_toRat_mul_Z2val_toRat (a b : Z2) : (a.val : ℚ) * (b.val : ℚ) = ((a*b).val : ℚ) := by
  fin_cases a <;> fin_cases b <;> simp
  apply one_mul
