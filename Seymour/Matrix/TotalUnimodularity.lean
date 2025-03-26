import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic.FunctionDecompose
import Seymour.Basic.SignTypeCast
import Seymour.Matrix.Basic


/-- Every matrix over `Z2` is TU. -/
lemma Matrix.overZ2_isTotallyUnimodular {X Y : Type} (A : Matrix X Y Z2) : A.IsTotallyUnimodular := by
  intro k f g hf hg
  if h0 : (A.submatrix f g).det = 0 then
    use 0
    rewrite [h0]
    rfl
  else
    use 1
    rewrite [Fin2_eq_1_of_ne_0 h0]
    rfl

/-- Every matrix over `Z3` is TU. -/
lemma Matrix.overZ3_isTotallyUnimodular {X Y : Type} (A : Matrix X Y Z3) : A.IsTotallyUnimodular := by
  intro k f g hf hg
  if h0 : (A.submatrix f g).det = 0 then
    use 0
    rewrite [h0]
    rfl
  else if h1 : (A.submatrix f g).det = 1 then
    use 1
    rewrite [h1]
    rfl
  else
    use -1
    rewrite [Fin3_eq_2_of_ne_0_1 h0 h1]
    rfl

-- Not every matrix over `Z4` is TU.
example : ¬ (!![2] : Matrix _ _ (ZMod 4)).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff]
  push_neg
  use 1, id, id
  decide

lemma Matrix.IsTotallyUnimodular.neg {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    (-A).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  peel hA
  rw [Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply, Matrix.det_neg]
  apply neg_one_pow_mul_in_signTypeCastRange
  assumption

lemma Matrix.IsTotallyUnimodular.det_eq_map_ratFloor_det {X : Type} [DecidableEq X] [Fintype X] {A : Matrix X X ℚ}
    (hA : A.IsTotallyUnimodular) :
    A.det = (A.map Rat.floor).det := by
  rw [Matrix.det_int_coe, Matrix.map_map]
  congr
  ext i j
  rw [Matrix.map_apply]
  obtain ⟨s, hs⟩ := hA.apply i j
  cases s <;> simp at hs <;> rw [←hs] <;> rfl

lemma Matrix.IsTotallyUnimodular.map_ratFloor {X Y : Type} {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    (A.map Rat.floor).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff]
  intro k f g
  rw [Matrix.submatrix_map]
  have hAfg := (hA.submatrix f g).det_eq_map_ratFloor_det
  rw [Matrix.isTotallyUnimodular_iff] at hA
  if h0 : ((A.submatrix f g).map Rat.floor).det = 0 then
    rewrite [h0]
    exact ⟨0, rfl⟩
  else if h1 : ((A.submatrix f g).map Rat.floor).det = 1 then
    rewrite [h1]
    exact ⟨1, rfl⟩
  else if h9 : ((A.submatrix f g).map Rat.floor).det = -1 then
    rewrite [h9]
    exact ⟨-1, rfl⟩
  else
    exfalso
    obtain ⟨s, hs⟩ := hAfg ▸ hA k f g
    cases s with
    | zero =>
      apply h0
      convert hs.symm
      simp
    | pos =>
      apply h1
      convert hs.symm
      simp
    | neg =>
      apply h9
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, neg_eq_iff_eq_neg, ←Int.cast_neg] at hs
      symm at hs
      rw [Int.cast_eq_one] at hs
      rwa [←neg_eq_iff_eq_neg]

variable {Z : Type}

lemma Matrix.IsTotallyUnimodular.comp_rows {X Y R : Type} [CommRing R] {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) (e : Z → X) :
    Matrix.IsTotallyUnimodular (A ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  exact hA k (e ∘ f) g

lemma Matrix.IsTotallyUnimodular.comp_cols {X Y R : Type} [CommRing R] {A : Matrix X Y R}
    (hA : A.IsTotallyUnimodular) (e : Z → Y) :
    Matrix.IsTotallyUnimodular (A · ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  exact hA k f (e ∘ g)

-- The rest of the file deals with a block matrix made of two TU matrices and two `0` matrices.

variable {X₁ X₂ : Type}

noncomputable instance [Fintype Z] {f : Z → X₁ ⊕ X₂} : Fintype { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } := by
  apply Fintype.ofInjective (·.val.fst)
  intro ⟨⟨u, u₁⟩, hu⟩ ⟨⟨v, v₁⟩, hv⟩ huv
  dsimp only at hu hv huv
  rw [Subtype.mk_eq_mk, Prod.mk_inj]
  refine ⟨huv, ?_⟩
  rw [←Sum.inl.injEq, ←hu, ←hv, huv]

noncomputable instance [Fintype Z] {f : Z → X₁ ⊕ X₂} : Fintype { x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } := by
  apply Fintype.ofInjective (·.val.fst)
  intro ⟨⟨u, u₁⟩, hu⟩ ⟨⟨v, v₁⟩, hv⟩ huv
  dsimp only at hu hv huv
  rw [Subtype.mk_eq_mk, Prod.mk_inj]
  refine ⟨huv, ?_⟩
  rw [←Sum.inr.injEq, ←hu, ←hv, huv]

lemma decomposeSum_card_eq [Fintype Z] (f : Z → X₁ ⊕ X₂) :
    #{ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } + #{ x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } = #Z := by
  rw [←Fintype.card_sum]
  exact Fintype.card_congr f.decomposeSum.symm

variable {Y₁ Y₂ R : Type}

/-- `Matrix.fromBlocks_isTotallyUnimodular` preprocessing. -/
private lemma Matrix.fromBlocks_submatrix [Zero R] (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R)
    (f : Z → X₁ ⊕ X₂) (g : Z → Y₁ ⊕ Y₂) :
    (fromBlocks A₁ 0 0 A₂).submatrix f g =
    (fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } → X₁)
        ((·.val.snd) : { y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } → Y₁)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } → X₂)
        ((·.val.snd) : { y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd } → Y₂)
      )
    ).submatrix f.decomposeSum g.decomposeSum := by
  rw [
    f.eq_comp_decomposeSum,
    g.eq_comp_decomposeSum,
    ←Matrix.submatrix_submatrix]
  aesop

/-
In the comments bellow, we will use the following shorthands:

`Z` is the next indexing type (for both rows and cols of the big square submatrix), typically `Fin k`

`▫X₁` denotes `{ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd }`
`▫X₂` denotes `{ x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd }`
`▫Y₁` denotes `{ y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd }`
`▫Y₂` denotes `{ y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd }`

`X'` is a specific subset of `▫X₂` converted to a type
`(▫X₂ \ X')` is its complement as a type, formally written as `{ x // x ∉ X' }` (where `x : ▫X₂` implicitly)

`I` is `Equiv.refl _`
` | ` denotes `Equiv.sumCongr`
`|S|` denotes `#S` for any `{S : Type} [Fintype S]`
-/
variable [LinearOrderedCommRing R] [Fintype Z] [DecidableEq Z] [DecidableEq X₁] [DecidableEq X₂]

/-- `Matrix.fromBlocks_isTotallyUnimodular` square case. -/
private lemma Matrix.fromBlocks_submatrix_det_in_signTypeCastRange_of_isTotallyUnimodular_of_card_eq
    {A₁ : Matrix X₁ Y₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix X₂ Y₂ R} (hA₂ : A₂.IsTotallyUnimodular)
    {f : Z → X₁ ⊕ X₂} {g : Z → Y₁ ⊕ Y₂}
    (hfg₁ : #{ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } = #{ y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd })
    (hfg₂ : #{ x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } = #{ y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd }) :
    ((fromBlocks A₁ 0 0 A₂).submatrix f g).det ∈
      SignType.cast.range := by
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hA₁ hA₂
  rw [Matrix.fromBlocks_submatrix]
  let e₁ : { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } ≃ { y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } :=
    Fintype.equivOfCardEq hfg₁
  let e₂ : { x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } ≃ { y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd } :=
    Fintype.equivOfCardEq hfg₂
/-
  ` f :  Z -> X₁ ⊕ X₂ `
  ` g :  Z -> Y₁ ⊕ Y₂ `
  are decomposed into
  ` f₁ :  ▫X₁ -> X₁ `
  ` f₂ :  ▫X₂ -> X₂ `
  ` g₁ :  ▫Y₁ -> Y₁ `
  ` g₂ :  ▫Y₂ -> Y₂ `

  Here we have ` |▫X₁| = |▫Y₁| ` and ` |▫X₂| = |▫Y₂| `

  ` ▫X₁ ⊕ ▫X₂ = Z = ▫Y₁ ⊕ ▫Y₂ `

  ` e₁ :  ▫X₁ ≃ ▫Y₁ `
  ` e₂ :  ▫X₂ ≃ ▫Y₂ `

  ` g₁ ∘ e₁ :  ▫X₁ -> Y₁ `
  ` g₂ ∘ e₂ :  ▫X₂ -> Y₂ `

  ` (g₁ ∘ e₁) | (g₂ ∘ e₂) :  Z -> Y₁ ⊕ Y₂ `   (note that `f` has the same type)
-/
  have hAfg : -- make the outer submatrix bijective
    (fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } → X₁)
        ((·.val.snd) : { y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } → Y₁)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } → X₂)
        ((·.val.snd) : { y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd } → Y₂)
      )
    ).submatrix f.decomposeSum g.decomposeSum
    =
    (fromBlocks
      (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0 0
      (A₂.submatrix (·.val.snd) ((·.val.snd) ∘ e₂))
    ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
  · ext
    simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
      Matrix.submatrix, Matrix.of_apply]
    split <;> split <;> simp
  rw [hAfg,
  -- absolute value of determinant was preserved by previous mappings,
    in_signTypeCastRange_iff_abs, Matrix.abs_det_submatrix_equiv_equiv,
  -- we now express it as a product of determinants of submatrices in blocks
    Matrix.det_fromBlocks_zero₁₂, ←in_signTypeCastRange_iff_abs]
  -- determinants of submatrices in blocks are in `SignType.cast.range` by TUness of `A₁` and `A₂`
  apply in_signTypeCastRange_mul_in_signTypeCastRange
  · apply hA₁
  · apply hA₂

/-- `Matrix.fromBlocks_isTotallyUnimodular` non-square case. -/
private lemma Matrix.fromBlocks_submatrix_det_in_signTypeCastRange_of_card_lt
    (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R) {f : Z → X₁ ⊕ X₂} {g : Z → Y₁ ⊕ Y₂}
    (hfg :
      #{ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } <
      #{ y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd }) :
    ((fromBlocks A₁ 0 0 A₂).submatrix f g).det ∈ SignType.cast.range := by
  -- we will show that the submatrix is singular
  convert zero_in_signTypeCastRange
  rw [Matrix.fromBlocks_submatrix]
  -- we need a new indexing type [`▫X₁ ⊕ ` a part of `▫X₂`] of the same cardinality as `▫Y₁` for the "top half"
  -- then the bottom left blocks will be all `0`s, hence we can multiply the two determinants, and the top left block will
  -- have at least one row made of `0`s, hence its determinant is `0`
  have hZY₁ :
      #{ y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } ≤
      #{ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } +
      #{ x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd }
  · rw [decomposeSum_card_eq]
    apply Fintype.card_le_of_embedding
    use (·.val.fst)
    intro ⟨⟨_, u⟩, _⟩ ⟨⟨_, v⟩, _⟩ huv
    simp_rw [Subtype.mk.injEq] at huv ⊢
    simp_all only [Sum.inl.injEq]
  obtain ⟨X', hY₁, hX'⟩ := finset_of_cardinality_between hfg hZY₁
  have hY₂ : #{ y // y ∉ X' } = #{ y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd }
  · suffices :
        #{ y // y ∉ X' } + #({ x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } ⊕ X') =
        #{ y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } +
        #{ y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd }
    · omega
    rw [Fintype.card_sum, add_comm, add_assoc, ←Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl (· ∈ X')),
      decomposeSum_card_eq, decomposeSum_card_eq]
  let e₁ := Fintype.equivOfCardEq hY₁
  let e₂ := Fintype.equivOfCardEq hY₂
  let e₃ := (Equiv.sumAssoc { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } X' { x // x ∉ X' }).symm
  let e' := (Equiv.sumCompl (· ∈ X')).symm
/-
  ` f :  Z -> X₁ ⊕ X₂ `
  ` g :  Z -> Y₁ ⊕ Y₂ `
  are decomposed into
  ` f₁ :  ▫X₁ -> X₁ `
  ` f₂ :  ▫X₂ -> X₂ `
  ` g₁ :  ▫Y₁ -> Y₁ `
  ` g₂ :  ▫Y₂ -> Y₂ `

  ` ▫X₁ ⊕ ▫X₂ = Z = ▫Y₁ ⊕ ▫Y₂ `

  Here we have ` |▫X₁| < |▫Y₁| ` and so ` |▫X₂| > |▫Y₂| `

  We choose `X'` so that ` |▫X₁ ⊕ X'| = |▫Y₁| `(hY₁) and therefore ` |▫X₂ \ X'| = |▫Y₂| `(hY₂)

  ` e₁ :  ▫X₁ ⊕ X' ≃ ▫Y₁ `
  ` e₂ :  ▫X₂ \ X' ≃ ▫Y₂ `

  ` e₃ :  ▫X₁ ⊕ (X' ⊕ (▫X₂ \ X')) ≃ (▫X₁ ⊕ X') ⊕ (▫X₂ \ X') `

  ` e' :  ▫X₂ ≃ X' ⊕ (▫X₂ \ X') `

  ` I | e' :  ▫X₁ ⊕ ▫X₂ ≃ ▫X₁ ⊕ (X' ⊕ (▫X₂ \ X')) `

  ` e₃ ∘ (I | e') :  Z ≃ (▫X₁ ⊕ X') ⊕ (▫X₂ \ X') `
-/
  have hAfg : -- make the outer submatrix bijective
    (fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : Z × X₁ // f x₁.fst = ◩x₁.snd } → X₁)
        ((·.val.snd) : { y₁ : Z × Y₁ // g y₁.fst = ◩y₁.snd } → Y₁)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : Z × X₂ // f x₂.fst = ◪x₂.snd } → X₂)
        ((·.val.snd) : { y₂ : Z × Y₂ // g y₂.fst = ◪y₂.snd } → Y₂)
      )
    ).submatrix f.decomposeSum g.decomposeSum
    =
    (fromBlocks
      (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0)
      (fromRows 0 (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)))
      0
      (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂))
    ).submatrix
      ((f.decomposeSum.trans ((Equiv.refl _).sumCongr e')).trans e₃)
      (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
  · ext
    simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
      Matrix.submatrix, Matrix.of_apply, e₃, e']
    split
    · split <;> simp [Equiv.sumCompl, Equiv.sumAssoc, Matrix.fromBlocks, Matrix.fromRows]
    · split <;>
        simp only [Matrix.fromBlocks, Matrix.fromRows, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr,
          Equiv.sumAssoc, Equiv.sumCompl, Equiv.coe_fn_symm_mk, Set.mem_range, Matrix.zero_apply] <;> split <;>
        simp
  rw [hAfg, ←abs_eq_zero, Matrix.abs_det_submatrix_equiv_equiv, abs_eq_zero]
  convert_to
    (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0).det * (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)).det
      = 0
  · convert -- none of `exact` `apply` `rw` `erw` `simp_rw` works with `Matrix.det_fromBlocks_zero₂₁` here
      Matrix.det_fromBlocks_zero₂₁
        (fromRows (A₁.submatrix (·.val.snd) ((·.val.snd) ∘ e₁)) 0)
        (fromRows 0 (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂)))
        (A₂.submatrix (·.val.val.snd) ((·.val.snd) ∘ e₂))
  convert zero_mul _
  exact Matrix.det_eq_zero_of_row_eq_zero ◪(Classical.choice hX') (fun _ => rfl)

omit Z
variable [DecidableEq Y₁] [DecidableEq Y₂]

/-- The block matrix that has two totally unimodular matrices along the diagonal and zeros elsewhere is totally unimodular. -/
lemma Matrix.fromBlocks_isTotallyUnimodular {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular :=
  fun k f g _ _ =>
    if hxy :
      #{ x₁ : Fin k × X₁ // f x₁.fst = ◩x₁.snd } = #{ y₁ : Fin k × Y₁ // g y₁.fst = ◩y₁.snd } ∧
      #{ x₂ : Fin k × X₂ // f x₂.fst = ◪x₂.snd } = #{ y₂ : Fin k × Y₂ // g y₂.fst = ◪y₂.snd }
    then
      Matrix.fromBlocks_submatrix_det_in_signTypeCastRange_of_isTotallyUnimodular_of_card_eq hA₁ hA₂ hxy.1 hxy.2
    else if hxy₁ :
      #{ x₁ : Fin k × X₁ // f x₁.fst = ◩x₁.snd } < #{ y₁ : Fin k × Y₁ // g y₁.fst = ◩y₁.snd }
    then
      Matrix.fromBlocks_submatrix_det_in_signTypeCastRange_of_card_lt A₁ A₂ hxy₁
    else by
      rw [←Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
      apply Matrix.fromBlocks_submatrix_det_in_signTypeCastRange_of_card_lt
      have := decomposeSum_card_eq f
      have := decomposeSum_card_eq g
      omega

-- Alternative proof is here (the auxiliary definition is different but the main ideas are identical):
-- https://github.com/madvorak/matrix-tu-experimental/blob/082206a6cf744d3bc80513494781a05451da5717/MatrixTuExperimental.lean#L262
-- It will be probably upstreamed to Mathlib someday.
