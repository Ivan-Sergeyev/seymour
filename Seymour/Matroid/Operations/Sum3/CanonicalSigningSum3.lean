import Seymour.Matroid.Operations.Sum3.CanonicalSigning
import Seymour.Matroid.Operations.Sum3.Basic


/-! # Canonical signing of 3-sum of matrices -/

/-! ## Additional notation for special rows and columns -/

/-- First special column of `S.Bᵣ` used to generate `S.D`. -/
def MatrixSum3.c₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Fin 2 ⊕ Xᵣ → F :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 0)

/-- Second special column of `S.Bᵣ` used to generate `S.D`. -/
def MatrixSum3.c₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Fin 2 ⊕ Xᵣ → F :=
  ((S.D₀ᵣ ⊟ S.Dᵣ) · 1)

/-- Third special column of `S.Bᵣ` used to generate `S.D`. -/
def MatrixSum3.c₂ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Sub F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Fin 2 ⊕ Xᵣ → F :=
  S.c₀ - S.c₁

/-- First special row of `S.Bₗ` used to generate `S.D`. -/
def MatrixSum3.d₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Yₗ ⊕ Fin 2 → F :=
  (S.Dₗ ◫ S.D₀ₗ) 0

/-- Second special row of `S.Bₗ` used to generate `S.D`. -/
def MatrixSum3.d₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Yₗ ⊕ Fin 2 → F :=
  (S.Dₗ ◫ S.D₀ₗ) 1

/-- Third special row of `S.Bₗ` used to generate `S.D`. -/
def MatrixSum3.d₂ {Xₗ Yₗ Xᵣ Yᵣ : Type} {F : Type} [Sub F] (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ F) :
    Yₗ ⊕ Fin 2 → F :=
  S.d₀ - S.d₁


/-! ## Lemmas about extending bottom-right matrix with special rows and columns -/

lemma MatrixSum3.HasTuBᵣ_special_form_cols {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    ∀ i, ![S.c₀ i, S.c₁ i] ≠ ![1, -1] ∧ ![S.c₀ i, S.c₁ i] ≠ ![-1, 1] := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- omit [DecidableEq α] in
-- lemma Matrix.IsTotallyUnimodular.special_form_cols {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
--     {x₂ : X} {y₀ y₁ : Y} (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     ∀ i : X.drop1 x₂, ![c₀ i, c₁ i] ≠ ![1, -1] ∧ ![c₀ i, c₁ i] ≠ ![-1, 1] := by
--   intro c₀ c₁ i
--   constructor <;>
--   · intro contr
--     simp only [c₀, c₁] at contr
--     have := congr_fun contr 0
--     have := congr_fun contr 1
--     have := hQ.det ![x₂, Set.diff_subset.elem i] ![y₀, y₁]
--     simp_all [Matrix.det_fin_two]

lemma MatrixSum3.HasTuBᵣ_c₀_c₂_Aᵣ_IsTotallyUnimodular₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    (▮S.c₀ ◫ ▮S.c₂ ◫ S.Aᵣ).IsTotallyUnimodular := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- set_option maxHeartbeats 333333 in
-- lemma Matrix.IsTotallyUnimodular.signing_expansion₀ {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
--     {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
--     (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     let Q' := Q.Aᵣ x₂ y₀ y₁
--     (Q' ◫ ▮c₀ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
--   intro c₀ c₁ Q'
--   let B : Matrix X Y ℚ := Q.shortTableauPivot x₂ y₀
--   let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
--   let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
--     (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₀) ↓y₁),
--     fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◩◪() else if hy₁ : y = y₁ then ◪() else ◩◩⟨y, by simp [*]⟩,
--     ↓(by aesop),
--     ↓(by aesop)⟩
--   have B'_eq : B' = (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).submatrix id e.symm
--   · ext i j
--     have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
--     have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
--     if hjy₀ : j = y₀ then
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀]
--     else if hjy₁ : j = y₁ then
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
--     else
--       have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
--       have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
--   have hB : B.IsTotallyUnimodular
--   · apply hQ.shortTableauPivot
--     rw [hQy₀]
--     exact Rat.zero_ne_one.symm
--   have hB' : B'.IsTotallyUnimodular
--   · apply hB.submatrix
--   rw [B'_eq] at hB'
--   have hQcc : (Q' ◫ ▮(-c₀) ◫ ▮(c₁ - c₀)).IsTotallyUnimodular
--   · simpa using hB'.submatrix id e
--   let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) (-1))
--   have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
--   · rintro ((_|_)|_) <;> simp [q]
--   convert hQcc.mul_cols hq
--   ext _ ((_|_)|_) <;> simp [q]

lemma MatrixSum3.HasTuBᵣ_c₁_c₂_Aᵣ_IsTotallyUnimodular₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    (▮S.c₁ ◫ ▮S.c₂ ◫ S.Aᵣ).IsTotallyUnimodular := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- set_option maxHeartbeats 333333 in
-- lemma Matrix.IsTotallyUnimodular.signing_expansion₁ {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ} (hQ : Q.IsTotallyUnimodular)
--     {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
--     (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     let Q' := Q.Aᵣ x₂ y₀ y₁
--     (Q' ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
--   intro c₀ c₁ Q'
--   let B := Q.shortTableauPivot x₂ y₁
--   let B' : Matrix (X.drop1 x₂) Y ℚ := B.submatrix Set.diff_subset.elem id
--   let e : (Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit ≃ Y := ⟨
--     (·.casesOn (·.casesOn Set.diff_subset.elem ↓y₁) ↓y₀),
--     fun ⟨y, hy⟩ => if hy₀ : y = y₀ then ◪() else if hy₁ : y = y₁ then ◩◪() else ◩◩⟨y, by simp [*]⟩,
--     ↓(by aesop),
--     ↓(by aesop)⟩
--   have B'_eq : B' = (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).submatrix id e.symm
--   · ext i j
--     have : undrop1 i ≠ x₂ := i.property.right ∘ congr_arg Subtype.val
--     have : y₁.val ≠ y₀.val := Subtype.coe_ne_coe.← (Ne.symm hyy)
--     if hjy₀ : j = y₀ then
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
--     else if hjy₁ : j = y₁ then
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', c₀, c₁]
--     else
--       have : j.val ≠ y₀.val := Subtype.coe_ne_coe.← hjy₀
--       have : j.val ≠ y₁.val := Subtype.coe_ne_coe.← hjy₁
--       simp_all [Matrix.shortTableauPivot_eq, e, B, B', Q']
--   have hB : B.IsTotallyUnimodular
--   · apply hQ.shortTableauPivot
--     rw [hQy₁]
--     exact Rat.zero_ne_one.symm
--   have hB' : B'.IsTotallyUnimodular
--   · apply hB.submatrix
--   rw [B'_eq] at hB'
--   have hQcc : (Q' ◫ ▮(-c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular
--   · simpa using hB'.submatrix id e
--   let q : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit → ℚ := (·.casesOn (·.casesOn 1 (-1)) 1)
--   have hq : ∀ i : ((Y.drop2 y₀ y₁) ⊕ Unit) ⊕ Unit, q i ∈ SignType.cast.range
--   · rintro ((_|_)|_) <;> simp [q]
--   convert hQcc.mul_cols hq
--   ext _ ((_|_)|_) <;> simp [q]

lemma MatrixSum3.HasTuBᵣ_c₀_c₁_c₂_Aᵣ_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮S.c₂ ◫ S.Aᵣ).IsTotallyUnimodular := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_weak {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ}
--     (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
--     (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     let Q' := Q.Aᵣ x₂ y₀ y₁
--     (Q' ◫ ▮c₀ ◫ ▮c₁ ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
--   sorry

lemma MatrixSum3.HasTuBᵣ_dup_c₀_c₁_c₂_Aᵣ_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    (▮S.c₀ ◫ ▮S.c₀ ◫ ▮S.c₁ ◫ ▮S.c₁ ◫ ▮S.c₂ ◫ ▮S.c₂ ◫ S.Aᵣ).IsTotallyUnimodular := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- lemma Matrix.IsTotallyUnimodular.signing_expansion_cols_aux {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ}
--     (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
--     (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     let Q' := Q.Aᵣ x₂ y₀ y₁
--     (Q' ◫ ▮c₀ ◫ ▮c₀ ◫ ▮c₁ ◫ ▮c₁ ◫ ▮(c₀ - c₁) ◫ ▮(c₀ - c₁)).IsTotallyUnimodular := by
--   intros
--   convert (hQ.signing_expansion_cols_weak hyy hQy₀ hQy₁ hQy).comp_cols
--     (fun j : ((((((Y.drop2 y₀ y₁ ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) =>
--       (j.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (◩◩◩·) ↓◩◩◪()) ↓◩◩◪()) ↓◩◪()) ↓◩◪()) ↓◪()) ↓◪()))
--   aesop

lemma MatrixSum3.HasTuBᵣ_pm_c₀_c₁_c₂_Aᵣ_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.HasTuBᵣ) :
    (S.Aᵣ ◫ ▮S.c₀ ◫ ▮(-S.c₀) ◫ ▮S.c₁ ◫ ▮(-S.c₁) ◫ ▮S.c₂ ◫ ▮(-S.c₂)).IsTotallyUnimodular := by
  sorry
-- todo: convert proof below; Q = S.Bᵣ; assumptions are satisfied by construction of S.Bᵣ
-- lemma Matrix.IsTotallyUnimodular.signing_expansion_cols {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ}
--     (hQ : Q.IsTotallyUnimodular) {x₂ : X} {y₀ y₁ : Y} (hyy : y₀ ≠ y₁) (hQy₀ : Q x₂ y₀ = 1) (hQy₁ : Q x₂ y₁ = 1)
--     (hQy : ∀ y : Y, y.val ≠ y₀ ∧ y.val ≠ y₁ → Q x₂ y = 0) :
--     let c₀ := Q._col y₀
--     let c₁ := Q._col y₁
--     let Q' := Q.Aᵣ x₂ y₀ y₁
--     (Q' ◫ ▮c₀ ◫ ▮(-c₀) ◫ ▮c₁ ◫ ▮(-c₁) ◫ ▮(c₀ - c₁) ◫ ▮(c₁ - c₀) ◫ ▮0).IsTotallyUnimodular := by
--   intros
--   convert ((hQ.signing_expansion_cols_aux hyy hQy₀ hQy₁ hQy).mul_cols
--     (show ∀ j, (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn (·.casesOn 1 1) (-1)) 1) (-1)) 1) (-1)) j ∈
--         SignType.cast.range by rintro ((((((_|_)|_)|_)|_)|_)|_) <;> simp)).fromCols_zero Unit
--   aesop

-- lemma MatrixSum3.HasTuBₗ_Aₗ_pm_d₀_d₁_d₂_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
--     (hS : S.HasTuBₗ) :
--     (S.Aₗ ⊟ ▬S.d₀ ⊟ ▬(-S.d₀) ⊟ ▬S.d₁ ⊟ ▬(-S.d₁) ⊟ ▬S.d₂ ⊟ ▬(-S.d₂)).IsTotallyUnimodular := by
--   sorry
-- -- todo: convert proof below; Q = S.Bₗ; assumptions are satisfied by construction of S.Bₗ
-- -- lemma Matrix.IsTotallyUnimodular.signing_expansion_rows {α : Type} {X Y : Set α} {Q : Matrix X Y ℚ}
-- --     (hQ : Q.IsTotallyUnimodular) {x₀ x₁ : X} {y₂ : Y} (hxx : x₀ ≠ x₁) (hQx₀ : Q x₀ y₂ = 1) (hQx₁ : Q x₁ y₂ = 1)
-- --     (hQx : ∀ x : X, x.val ≠ x₀ ∧ x.val ≠ x₁ → Q x y₂ = 0) :
-- --     let d₀ := Q._row x₀
-- --     let d₁ := Q._row x₁
-- --     let Q' := Q.Aₗ x₀ x₁ y₂
-- --     (Q' ⊟ ▬d₀ ⊟ ▬(-d₀) ⊟ ▬d₁ ⊟ ▬(-d₁) ⊟ ▬(d₀ - d₁) ⊟ ▬(d₁ - d₀) ⊟ ▬0).IsTotallyUnimodular := by
-- --   intros
-- --   convert (hQ.transpose.signing_expansion_cols hxx hQx₀ hQx₁ hQx).transpose
-- --   aesop


/-! ## Definition -/

/-- Canonical re-signing of a 3-sum of matrices. -/
def MatrixSum3.toCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) :
    MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ :=
  sorry

/-- Proposition that `S` is a canonical signing of a 3-sum of matrices. -/
def MatrixSum3.IsCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ) : Prop :=
  sorry

/-- Sufficient condition for existence of a canonical signing of a 3-sum of matrices. -/
def MatrixSum3.HasCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} (S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2) : Prop :=
  (S.Bₗ.HasTuSigning ∧ S.Bᵣ.HasTuSigning) ∧
    ((S.Sₗ = matrix3x3unsigned₀ Z2 ∧ S.Sᵣ = matrix3x3unsigned₀ Z2) ∨
     (S.Sₗ = matrix3x3unsigned₁ Z2 ∧ S.Sᵣ = matrix3x3unsigned₁ Z2))


/-! ## Correctness -/

/-- Canonical re-signing transforms a 3-sum of matrices into its canonically signed version. -/
lemma MatrixSum3.HasCanonicalSigning.isCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2}
    (hS : S.HasCanonicalSigning) :
    S.toCanonicalSigning.IsCanonicalSigning :=
  sorry

/-- Canonical re-signing yields a signing of the original 3-sum of marices. -/
lemma MatrixSum3.HasCanonicalSigning.toCanonicalSigning {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ Z2}
    (hS : S.HasCanonicalSigning) :
    S.toCanonicalSigning.matrix.IsSigningOf S.matrix :=
  sorry


/-! ## Properties -/

/-- The bottom-left block of a canonical signing of a 3-sum of matrices in the first special case. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₀ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (hS₀ : S.Sₗ = matrix3x3signed₀) :
    S.D = S.c₀ ⊗ S.d₀ - S.c₁ ⊗ S.d₁ :=
  sorry

/-- The bottom-left block of a canonical signing of a 3-sum of matrices in the second special case. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_sum_outer₁ {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) (hS₁ : S.Sₗ = matrix3x3signed₁) :
    S.D = S.c₀ ⊗ S.d₀ - S.c₀ ⊗ S.d₁ + S.c₁ ⊗ S.d₁ :=
  sorry

/-- Every column of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±c₀, ±c₁, ±c₂}`. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_cols {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    ∀ j, (S.D · j) = 0 ∨ (S.D · j) = S.c₀ ∨ (S.D · j) = -S.c₀ ∨ (S.D · j) = S.c₁ ∨ (S.D · j) = -S.c₁
         ∨ (S.D · j) = S.c₀ - S.c₁ ∨ (S.D · j) = S.c₁ - S.c₀ :=
  sorry

/-- Every row of the bottom-left block of a canonical signing of a 3-sum of matrices is in `{0, ±d₀, ±d₁, ±d₂}`. -/
lemma MatrixSum3.IsCanonicalSigning.D_eq_rows {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    ∀ i, S.D i = 0 ∨ S.D i = S.d₀ ∨ S.D i = -S.d₀ ∨ S.D i = S.d₁ ∨ S.D i = -S.d₁ ∨ S.D i = S.d₂ ∨ S.D i = -S.d₂ :=
  sorry

/-- The left block of a canonical signing of a 3-sum of matrices is totally unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.Aₗ_D_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    (S.Aₗ ⊟ S.D).IsTotallyUnimodular :=
  sorry

/-- The extension of the bottom-right block of a canonical signing of a 3-sum of matrices with special columns is totally
    unimodular. -/
lemma MatrixSum3.IsCanonicalSigning.c₀_c₁_c₂_Aᵣ_IsTotallyUnimodular {Xₗ Yₗ Xᵣ Yᵣ : Type} {S : MatrixSum3 Xₗ Yₗ Xᵣ Yᵣ ℚ}
    (hS : S.IsCanonicalSigning) :
    (▮S.c₀ ◫ ▮S.c₁ ◫ ▮S.c₂ ◫ S.Aᵣ).IsTotallyUnimodular :=
  sorry
