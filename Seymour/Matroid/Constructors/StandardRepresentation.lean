import Seymour.Basic.Fin
import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.Pivoting
import Seymour.Matrix.Support
import Seymour.Matroid.Constructors.BinaryMatroid
import Seymour.Matroid.Elementary.Basic

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

variable {α : Type}

private noncomputable abbrev Set.equivFin (S : Set α) [Fintype S] : Fin #S ≃ S :=
  (Fintype.equivFin S.Elem).symm

@[app_unexpander Set.equivFin]
def Set.equivFin_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `equivFin))
  | _ => throw ()

private abbrev Equiv.leftCongr {ι₁ ι₂ : Type} (e : ι₁ ≃ ι₂) : ι₁ ⊕ α ≃ ι₂ ⊕ α :=
  Equiv.sumCongr e (Equiv.refl α)

@[app_unexpander Equiv.leftCongr]
def Equiv.leftCongr_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($(x).$(Lean.mkIdent `leftCongr))
  | _ => throw ()

variable [DecidableEq α] {R : Type}

/-- Convert standard representation of a vector matroid to a full representation. -/
def StandardRepr.toVectorMatroid [Zero R] [One R] (S : StandardRepr α R) : VectorMatroid α R :=
  ⟨S.X, S.X ∪ S.Y, ((1 ◫ S.B) · ∘ Subtype.toSum)⟩

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
    S.toVectorMatroid.A = ((1 ◫ S.B) · ∘ Subtype.toSum) :=
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
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

lemma StandardRepr.toVectorMatroid_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toVectorMatroid.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ hI.elem.range := by
  rw [StandardRepr.toVectorMatroid_indep_iff]
  unfold HasSubset.Subset.elem
  aesop

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
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) :=
  S.toVectorMatroid_indep_iff I

lemma StandardRepr.toMatroid_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B)ᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toVectorMatroid_indep_iff_elem I

lemma StandardRepr.toMatroid_indep_iff_submatrix [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R ((1 ◫ S.B).submatrix id (Subtype.toSum ∘ hI.elem))ᵀ := by
  simp only [
    StandardRepr.toMatroid, StandardRepr.toVectorMatroid, VectorMatroid.toMatroid_indep, VectorMatroid.indepCols_iff_submatrix]
  rfl

@[simp]
lemma StandardRepr.toMatroid_indep [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.Indep = (∃ hI : · ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B)ᵀ ∘ Subtype.toSum) hI.elem.range) := by
  ext I
  exact S.toVectorMatroid_indep_iff_elem I

lemma VectorMatroid.isFinitary [DivisionRing R] (M : VectorMatroid α R) : M.toMatroid.Finitary := by
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
  exact hI s (⟨⟨·.val, Set.mem_image_of_mem Subtype.val ·⟩, by simp⟩) hAs

lemma VectorMatroid.longTableauPivot [Field R] (V : VectorMatroid α R) {x : V.X} {y : V.Y} (hVxy : V.A x y ≠ 0) :
    (VectorMatroid.mk V.X V.Y (V.A.longTableauPivot x y)).toMatroid = V.toMatroid := by
  ext
  · rfl
  · rw [VectorMatroid.toMatroid_indep, VectorMatroid.toMatroid_indep, VectorMatroid.IndepCols, VectorMatroid.IndepCols,
      and_congr_right_iff]
    exact ↓(V.A.longTableauPivot_linearIndepenOn hVxy _)

set_option maxHeartbeats 666666 in
/-- Implicit Gaussian elimination for the proof of the lemma below. -/
private lemma VectorMatroid.exists_standardRepr_isBase_isTotallyUnimodular_aux [Field R] {G : Set α} [Fintype G]
    (V : VectorMatroid α R) (hVG : V.toMatroid.IsBase G) (hVA : V.A.IsTotallyUnimodular) {k : ℕ} (hk : k ≤ #G) :
    ∃ W : VectorMatroid α R,
      W.toMatroid = V.toMatroid ∧ W.A.IsTotallyUnimodular ∧ ∃ hGY : G ⊆ W.Y, ∃ f : Fin k → W.X, f.Injective ∧
        ∀ i : W.X, ∀ j : Fin k,
          if i = f j
          then W.A i (hGY.elem (G.equivFin ⟨j.val, by omega⟩)) = 1
          else W.A i (hGY.elem (G.equivFin ⟨j.val, by omega⟩)) = 0
    := by
  induction k with
  | zero =>
    use V, rfl, hVA, hVG.subset_ground, (Nat.not_succ_le_zero _ ·.isLt |>.elim), ↓↓↓(by omega)
    intro _ ⟨_, _⟩
    omega
  | succ n ih =>
    obtain ⟨W, hWV, hWA, hGY, f, hf, hfA⟩ := ih (by omega)
    have hnG : n < #G
    · omega
    wlog hgf : ∃ x : W.X, W.A x (hGY.elem (G.equivFin ⟨n, hnG⟩)) ≠ 0 ∧ x ∉ f.range
    · push_neg at hgf
      exfalso
      let X' := { x : W.X | W.A x (hGY.elem (G.equivFin ⟨n, hnG⟩)) ≠ 0 }
      let G' := { G.equivFin ⟨i.val, by omega⟩ | (i : Fin n) (hi : f i ∈ X') } -- essentially `G' = g (f⁻¹ X')`
      let G'' : Set G := G.equivFin ⟨n, hnG⟩ ᕃ G' -- essentially `G'' = g (n ᕃ f⁻¹ X')`
      have hgG' : G.equivFin ⟨n, hnG⟩ ∉ G'
      · intro ⟨i, hfi, hgi⟩
        apply G.equivFin.injective at hgi
        exact (congr_arg Fin.val hgi ▸ i.isLt).false
      have hG'' : ¬ W.toMatroid.Indep G''
      · simp
        intro _
        rw [linearDepOn_iff]
        classical
        let c : W.Y → R := fun j : W.Y =>
          if hjG : j.val ∈ G then
            let j' : G := ⟨j.val, hjG⟩
            if hj' : j' ∈ G' then W.A (f hj'.choose) (hGY.elem (G.equivFin ⟨n, hnG⟩))
            else if j' = G.equivFin ⟨n, hnG⟩ then -1 else 0
          else 0
        have hc : c.support = hGY.elem '' G''
        · ext j
          simp [G'', c, Function.support]
          clear * -
          by_cases hjG : j.val ∈ G
          · simp [hjG]
            let j' : G := ⟨j.val, hjG⟩
            by_cases hj' : j' ∈ G'
            · convert_to True ↔ True
              · rw [iff_true, dite_of_true hj']
                generalize_proofs _ hf
                exact hf.choose_spec.left
              · aesop
              rfl
            by_cases hj'' : j' = G.equivFin ⟨n, hnG⟩
            · convert_to True ↔ True
              · rw [iff_true, dite_of_false hj']
                simp
                exact hj''
              · rw [iff_true]
                left
                ext
                exact (congr_arg Subtype.val hj'').symm
              rfl
            · convert_to False ↔ False
              · simp_all [j']
              · aesop
              rfl
          · aesop
        use Finsupp.ofSupportFinite c (hc ▸ (hGY.elem '' G'').toFinite)
        constructor
        · simp [c, Finsupp.supported, Finsupp.ofSupportFinite]
          intro j hjY hjG hj
          let j' : G := ⟨j, hjG⟩
          if hj' : j' ∈ G' then
            use hjG
            right
            exact hj'
          else if hj'' : j' = G.equivFin ⟨n, hnG⟩ then
            use hjG
            left
            exact hj''
          else
            exfalso
            apply hj
            split
            · contradiction
            · rfl
        constructor
        · have hc' : (Finsupp.ofSupportFinite c (hc ▸ (hGY.elem '' G'').toFinite)).support = (hGY.elem '' G'').toFinset
          · apply eq_toFinset_of_toSet_eq
            exact ofSupportFinite_support_eq (Finite.Set.finite_image G'' hGY.elem) hc
          rw [Finsupp.ofSupportFinite_coe, hc']
          ext x
          rw [Finset.sum_apply]
          show ∑ j ∈ hGY.elem '' G'', c j • W.Aᵀ j x = 0
          have hG'' :
              (hGY.elem '' G'').toFinset =
              hGY.elem (G.equivFin ⟨n, hnG⟩) ᕃ G'.toFinset.map ⟨hGY.elem, hGY.elem_injective⟩
          · simp only [G'']
            clear * -
            aesop
          rw [hG'', Finset.sum_insert (hgG' <| by simpa using ·)]
          if hx : x ∈ X' then
            rw [add_eq_zero_iff_eq_neg', Finset.sum_map, ←Finset.sum_attach]
            specialize hfA x
            simp [c, hgG']
            conv_lhs => congr; rfl; ext x; rw [dite_of_true (Set.mem_toFinset.→ x.property)]
            obtain ⟨i, hi⟩ := hgf x hx
            have hiG' : G.equivFin ⟨i.val, by omega⟩ ∈ G'
            · use i, hi ▸ hx
            rw [G'.toFinset.attach.sum_of_single_nonzero _ ⟨G.equivFin ⟨i.val, by omega⟩, G'.mem_toFinset.← hiG'⟩]
            · specialize hfA i
              simp [hi] at hfA
              rw [hfA]
              convert mul_one _
              generalize_proofs _ _ _ _ hgi
              obtain ⟨_, hgg⟩ := hgi.choose_spec
              rw [←hi]
              apply congr_arg
              ext
              exact (congr_arg Fin.val (G.equivFin.injective hgg)).symm
            · simp
            · intro z _ hzi
              convert mul_zero _
              have hz := z.property
              simp [G'] at hz
              obtain ⟨a, ha, haz⟩ := hz
              specialize hfA a
              rw [←hi] at hfA ⊢
              have hfifa : f i ≠ f a
              · intro hia
                apply hf at hia
                apply hzi
                ext
                rw [←haz]
                simp [hia]
              simp [hfifa] at hfA
              exact haz ▸ hfA
          else
            convert add_zero (0 : R)
            · exact smul_eq_zero_of_right _ (by simpa [X'] using hx)
            · rw [Finset.sum_map]
              -- TODO prove using a variant of `sum_elem_smul_matrix_row_of_nmem` instead of the manual labor below
              apply Finset.sum_eq_zero
              intro a ha
              simp [X'] at hx
              rw [Set.mem_toFinset] at ha
              obtain ⟨j, hfj, hgja⟩ := ha
              if hxj : x = f j then
                apply smul_eq_zero_of_left
                simp [c, ←hgja]
                rw [dite_of_false]
                · simp
                  omega
                intro ⟨z, hz, hgz⟩
                have hzj : z = j
                · ext
                  simpa using G.equivFin.injective hgz
                exact (hzj ▸ hz) (hxj ▸ hx)
              else
                exact smul_eq_zero_of_right _ (hgja ▸ (by simpa [hxj] using hfA x j))
        · simp only [Finsupp.ofSupportFinite, ne_eq, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int]
          intro hc0
          rw [Finsupp.ext_iff] at hc0
          specialize hc0 (hGY.elem (G.equivFin ⟨n, hnG⟩))
          simp [c, hgG'] at hc0
      have hGG'' : Subtype.val '' G'' ⊆ G
      · simp
      exact hG'' (hWV ▸ hVG.indep.subset hGG'')
    obtain ⟨x, hx, hxf⟩ := hgf
    let f' : Fin n.succ → W.X := Fin.snoc f x
    use ⟨W.X, W.Y, W.A.longTableauPivot x (hGY.elem (G.equivFin ⟨n, hnG⟩))⟩,
      hWV ▸ W.longTableauPivot hx, hWA.longTableauPivot _ _ hx, hGY, f'
    constructor
    · intro a b hab
      if ha : a.val = n then
        if hb : b.val = n then
          ext
          rw [ha, hb]
        else
          have ha' : a = n
          · ext
            simp [ha]
          exfalso
          rw [ha'] at hab
          simp only [f', Fin.snoc_last, Fin.natCast_eq_last] at hab
          rw [hab] at hxf
          apply hxf
          have hb' : b.val < n
          · omega
          use ⟨b.val, hb'⟩
          simp [hb', Fin.snoc]
          rfl
      else
        if hb : b.val = n then
          have hb' : b = n
          · ext
            simp [hb]
          exfalso
          rw [hb'] at hab
          simp only [f', Fin.snoc_last, Fin.natCast_eq_last] at hab
          rw [←hab] at hxf
          apply hxf
          have ha' : a.val < n
          · omega
          use ⟨a.val, ha'⟩
          simp [ha', Fin.snoc]
          rfl
        else
          have ha' : a.val < n
          · omega
          have hb' : b.val < n
          · omega
          simp [ha', hb', f', Fin.snoc] at hab
          apply hf at hab
          ext
          simpa [Fin.castLT] using hab
    intro i j
    if hj : j.val < n then
      have hxj : x ≠ f' j := (have hxf' := · ▸ hxf; by simp [f', hj, Fin.snoc] at hxf')
      let jₙ : Fin n := ⟨j.val, by omega⟩
      have hjjₙ : f' j = f jₙ
      · simp [f', hj, Fin.snoc]
        rfl
      if hij : i = f' j then
        have hijₙ : i = f jₙ := hjjₙ ▸ hij
        have hxjₙ : x ≠ f jₙ := hijₙ ▸ hij ▸ hxj
        simp [hij]
        rw [W.A.longTableauPivot_elem_of_zero_in_pivot_row hxj.symm (by simpa [hxjₙ] using hfA x jₙ)]
        simpa [hijₙ, hjjₙ] using hfA i jₙ
      else
        have hijₙ : i ≠ f jₙ := hjjₙ ▸ hij
        have hxjₙ : x ≠ f jₙ := hjjₙ ▸ hxj
        simp [hij]
        if hix : i = x then
          rw [←hix]
          apply W.A.longTableauPivot_elem_in_pivot_row_eq_zero
          simpa [hijₙ] using hfA i jₙ
        else
          rw [W.A.longTableauPivot_elem_of_zero_in_pivot_row hix]
          · simpa [hijₙ] using hfA i jₙ
          · simpa [hxjₙ] using hfA x jₙ
    else
      have hjn : j.val = n
      · omega
      have hgjgn : G.equivFin ⟨j.val, by omega⟩ = G.equivFin ⟨n, hnG⟩
      · simp [hjn]
      have hxj : x = f' j
      · simp [f', hjn, Fin.snoc]
      if hij : i = f' j then
        simpa [hij, hgjgn, hxj] using W.A.longTableauPivot_elem_pivot_eq_one (hxj ▸ hx)
      else
        simpa [hij, hgjgn, hxj] using W.A.longTableauPivot_elem_in_pivot_col_eq_zero hij (hxj ▸ hx)

set_option maxHeartbeats 300000 in
/-- Every vector matroid whose full representation matrix is totally unimodular has a standard representation whose rows are
    a given base and the standard representation matrix is totally unimodular. -/
lemma VectorMatroid.exists_standardRepr_isBase_isTotallyUnimodular [Field R] {G : Set α} [Fintype G]
    (V : VectorMatroid α R) (hVG : V.toMatroid.IsBase G) (hVA : V.A.IsTotallyUnimodular) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = V.toMatroid ∧ S.B.IsTotallyUnimodular := by
  obtain ⟨W, hWV, hWA, hGY, f, hf, hfA⟩ := V.exists_standardRepr_isBase_isTotallyUnimodular_aux hVG hVA (le_refl #G)
  have hWG := hWV ▸ hVG
  rw [←hWV] at *
  clear hVA hVG hWV V
  have hYGY : W.Y \ G ⊆ W.Y := Set.diff_subset
  have hGYY : G ∪ W.Y = W.Y := Set.union_eq_self_of_subset_left hGY
  let g : G ↪ W.X := ⟨f ∘ Fintype.equivFin G, ((Fintype.equivFin G).injective_comp f).← hf⟩
  let g' : G.Elem → (Subtype.val '' g.toFun.range).Elem := (⟨g ·, by simp⟩)
  let g'' : (Subtype.val '' g.toFun.range).Elem → G.Elem
  · intro ⟨i, hi⟩
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right] at hi
    exact ⟨hi.choose_spec.choose, hi.choose_spec.choose_spec.choose⟩
  have hXgX : W.X \ g.toFun.range ⊆ W.X := Set.diff_subset
  let ξ : (W.X \ g.toFun.range).Elem → W.X := hXgX.elem
  classical
  let e : (Subtype.val '' g.toFun.range) ⊕ (W.X \ g.toFun.range).Elem ≃ W.X :=
    (Subtype.coe_image_subset W.X g.toFun.range).equiv
  let e' : G ≃ (Subtype.val '' g.toFun.range) := ⟨
    g',
    g'',
    ↓(by simp [g'', g']),
    fun ⟨i, hi⟩ => by simp [g'', g']; simp at hi; have := hi.choose_spec.choose_spec; aesop
  ⟩
  have hA₁₁ : W.A.submatrix g hGY.elem = 1
  · ext i j
    if hij : i = j then
      rw [hij, Matrix.one_apply_eq]
      simpa [g] using hfA (g j) ((Fintype.equivFin G) j)
    else
      rw [Matrix.one_apply_ne hij]
      have hfifj : f ((Fintype.equivFin G) i) ≠ f ((Fintype.equivFin G) j)
      · exact (hij <| by simpa using hf ·)
      simpa [hfifj] using hfA (f ((Fintype.equivFin G) i)) ((Fintype.equivFin G) j)
  have hA₂₁ : W.A.submatrix ξ hGY.elem = 0
  · ext ⟨i, hi⟩ j
    have hiX : i ∈ W.X := hXgX hi
    have hij : ⟨i, hiX⟩ ≠ f ((Fintype.equivFin G) j)
    · simp at hi
      aesop
    simpa [hij] using hfA ⟨i, hiX⟩ ((Fintype.equivFin G) j)
  have hA₂₂ : W.A.submatrix ξ hYGY.elem = 0
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    have hiX : i ∈ W.X := hXgX hi
    have hjY : j ∈ W.Y := hYGY hj
    simp only [Function.Embedding.toFun_eq_coe, HasSubset.Subset.elem, Matrix.submatrix_apply, Matrix.zero_apply]
    by_contra hAij
    have hWjG : W.toMatroid.Indep (j ᕃ G)
    · simp only [VectorMatroid.toMatroid_indep_iff_elem]
      have hjGY : j ᕃ G ⊆ W.Y := Set.insert_subset (hYGY hj) hGY
      use hjGY
      rw [linearIndepOn_iff]
      intro c hc hc0
      rw [Finsupp.linearCombination_apply] at hc0
      unfold Finsupp.sum at hc0
      have hcj : c ⟨j, hjY⟩ = 0
      · by_contra hcj0
        have hci0 := congr_fun hc0 ⟨i, hiX⟩
        simp at hci0
        rw [c.support.sum_of_single_nonzero _ ⟨j, hjY⟩] at hci0
        · simp at hci0
          exact hci0.casesOn hcj0 hAij
        · exact c.mem_support_iff.← hcj0
        · intro z hzc hza
          rw [mul_eq_zero]
          right
          have hzG : z.val ∈ G := Set.mem_of_mem_insert_of_ne (show z.val ∈ j ᕃ G by have := hc hzc; aesop) (by
            apply hza
            ext
            exact ·)
          have hiz : ⟨i, hiX⟩ ≠ f ((Fintype.equivFin G) ⟨z.val, hzG⟩)
          · intro hiXz
            have hifz := congr_arg (Subtype.val) hiXz
            simp at hifz
            simp [hifz, g] at hi
          simpa [hiz] using hfA ⟨i, hiX⟩ ((Fintype.equivFin G) ⟨z.val, hzG⟩)
      have hjc : ⟨j, hjY⟩ ∉ c.support := Finsupp.not_mem_support_iff.← hcj
      ext a
      rw [Finsupp.coe_zero, Pi.zero_apply]
      by_contra hca
      have haj : a.val ≠ j := (by apply hca; subst ·; exact hcj)
      have haG : a.val ∈ G := Set.mem_of_mem_insert_of_ne (by have := hc (Finsupp.mem_support_iff.← hca); aesop) haj
      have hca0 := congr_fun hc0 (g ⟨a.val, haG⟩)
      simp only [Finset.sum_apply, smul_eq_mul, Pi.smul_apply, Pi.zero_apply] at hca0
      rw [c.support.sum_of_single_nonzero _ a] at hca0
      · simp only [Matrix.transpose_apply, mul_eq_zero] at hca0
        have hAaa : W.A (g ⟨a.val, haG⟩) a ≠ 0
        · intro h0
          specialize hfA (g ⟨a.val, haG⟩) ((Fintype.equivFin G) ⟨a.val, haG⟩)
          have haa : g ⟨a.val, haG⟩ = f ((Fintype.equivFin G) ⟨a.val, haG⟩)
          · rfl
          simp [←haa, h0] at hfA
        exact hca0.casesOn hca hAaa
      · exact Finsupp.mem_support_iff.← hca
      · intro z hzc hza
        rw [mul_eq_zero]
        if hzj : z = j then
          left
          convert hcj
        else
          right
          have hzG : z.val ∈ G := Set.mem_of_mem_insert_of_ne (by have := hc hzc; aesop) hzj
          specialize hfA (g ⟨a.val, haG⟩) ((Fintype.equivFin G) ⟨z.val, hzG⟩)
          have haz : g ⟨a.val, haG⟩ ≠ f ((Fintype.equivFin G) ⟨z.val, hzG⟩) := (by
            apply hza
            ext
            simpa using g.injective ·.symm)
          simpa [haz] using hfA
    apply W.toMatroid.base_not_ssubset_indep hWG hWjG
    exact ⟨G.subset_insert j, Set.not_subset.← ⟨j, G.mem_insert j, hj.right⟩⟩
  have hA :
    W.A.submatrix (e'.leftCongr.trans e) hGY.equiv =
    ⊞ (W.A.submatrix g hGY.elem) (W.A.submatrix g hYGY.elem)
      (W.A.submatrix ξ hGY.elem) (W.A.submatrix ξ hYGY.elem)
  · rw [←(W.A.submatrix (e'.leftCongr.trans e) hGY.equiv).fromBlocks_toBlocks, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> rfl
  rw [hA₁₁, hA₂₁, hA₂₂, ←Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromCols_zero] at hA
  have hW : W.toMatroid =
      (VectorMatroid.mk _ _ (((1 ◫ W.A.submatrix g hYGY.elem) ⊟ 0).reindex (e'.leftCongr.trans e) hGY.equiv)).toMatroid
  · rw [←((Matrix.reindex (e'.leftCongr.trans e) hGY.equiv).symm_apply_eq).→ hA]
  use ⟨G, W.Y \ G, Set.disjoint_sdiff_right, W.A.submatrix g hYGY.elem,
    G.decidableMemOfFintype, (Classical.propDecidable <| · ∈ W.Y \ G)⟩
  refine ⟨by simp, ?_, hWA.submatrix g hYGY.elem⟩
  rw [hW]
  simp only [StandardRepr.toMatroid, StandardRepr.toVectorMatroid]
  convert (Matrix.fromCols 1 (W.A.submatrix g hYGY.elem)).fromRows_zero_reindex_toMatroid hGY (e'.leftCongr.trans e)

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

omit R

private lemma sum_support_image_subtype_eq_zero {X Y : Set α} {F : Type} [Field F] {B : Matrix Y X F} {D : Set X} {y : Y}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} (hXXY : X ⊆ X ∪ Y) (hYXY : Y ⊆ X ∪ Y) -- redundant but keep
    {l : (X ∪ Y).Elem →₀ F} (hl : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D) (hly : l (hYXY.elem y) = 0)
    {i : (X ∪ Y).Elem} (hiX : i.val ∈ X) (hlBi : ∑ a ∈ l.support, l a • (1 ⊟ B) a.toSum ⟨i, hiX⟩ = 0) :
    ∑ a ∈ (l.support.image Subtype.val).subtype (· ∈ X),
      l (hXXY.elem a) • (1 ⊟ B) (hXXY.elem a).toSum ⟨i, hiX⟩ = 0 := by
  rw [←Finset.sum_finset_coe] at hlBi
  convert hlBi
  apply Finset.sum_bij (fun a ha => ⟨hXXY.elem a, by simpa using ha⟩)
  · simp
  · simp
  · intro z _
    simp only [HasSubset.Subset.elem, Finset.coe_sort_coe, Finset.mem_subtype, Finset.mem_image, Finsupp.mem_support_iff,
      Subtype.exists, Subtype.coe_prop, Set.mem_union, exists_and_right, exists_true_left, exists_eq_right, true_or]
    use z
    simp only [exists_prop, and_true]
    refine ⟨?_, (l.mem_support_toFun z).→ (Finset.coe_mem z)⟩
    have hzD : z.val.val ∈ Subtype.val '' D
    · cases hl z (by simp) with
      | inl hp =>
        have hzy : z.val = hYXY.elem y := Subtype.coe_inj.→ hp
        rw [←hzy] at hly
        exact absurd hly (l.mem_support_iff.→ (Finset.coe_mem z))
      | inr hp => exact hp
    have hDX : Subtype.val '' D ⊆ X
    · rw [Set.image, Set.setOf_subset]
      rintro _ ⟨⟨_, ha⟩, ⟨_, rfl⟩⟩
      exact ha
    exact Set.mem_of_mem_of_subset hzD hDX
  · intros
    rfl

set_option maxHeartbeats 1000000 in
private lemma support_eq_support_of_same_matroid_aux {F₁ F₂ : Type} [Field F₁] [Field F₂] [DecidableEq F₁] [DecidableEq F₂]
    {X Y : Set α} {hXY : X ⫗ Y} {B₁ : Matrix X Y F₁} {B₂ : Matrix X Y F₂}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
    (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
    B₁.support = B₂.support := by
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
    if hx₁ : B₁ᵀ y x = 0 then
      have hx₂ : x ∉ D₂
      · rw [←hDD]
        simp_rw [D₁, Set.mem_setOf_eq, not_not]
        exact hx₁
      simp_all [D₂]
    else
      have hx₂ : x ∈ D₂
      · rw [←hDD]
        simp_rw [D₁, Set.mem_setOf_eq]
        exact hx₁
      simp_all [D₂]
  apply Set.eq_of_subset_of_subset
  on_goal 1 => let D := D₁; let Dₒ := D₂; let B := B₁; let Bₒ := B₂; let F := F₁; let F₀ := F₂
  on_goal 2 => let D := D₂; let Dₒ := D₁; let B := B₂; let Bₒ := B₁; let F := F₂; let F₀ := F₁
  all_goals
  · by_contra hD
    rw [Set.not_subset_iff_exists_mem_not_mem] at hD
    -- otherwise `y ᕃ Dₒ` is dependent in `Mₒ` but indep in `M`
    have hMₒ : ¬ (StandardRepr.mk X Y hXY Bₒ hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · rw [StandardRepr.toMatroid_indep_iff_elem, not_exists]
      intro hDₒ
      erw [not_linearIndependent_iff]
      refine ⟨Finset.univ, (·.val.toSum.casesOn (- Bₒᵀ y) 1), ?_, ⟨hYXY.elem y, by simp_all⟩, Finset.mem_univ _, by
        dsimp only
        cases _ : (hYXY.elem y).toSum with
        | inl => simp_all [Subtype.toSum, hXY.not_mem_of_mem_right y.property]
        | inr => exact ne_zero_of_eq_one rfl⟩
      ext x
      simp only at x hDₒ
      simp_rw [Function.comp_apply]
      rw [Finset.sum_apply]
      show ∑ i : hDₒ.elem.range.Elem, (i.val.toSum.casesOn (- Bₒᵀ y) 1 : F₀) • (1 ◫ Bₒ) x i.val.toSum = 0
      suffices separated : Bₒ x y + ∑ i : Dₒ.Elem, (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i.val = 0
      · rw [Finset.sum_set_coe (f := (fun i : (X ∪ Y).Elem => (i.toSum.casesOn (- Bₒᵀ y) 1 : F₀) • (1 ◫ Bₒ) x i.toSum)),
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
        · convert_to ((1 : Matrix X X F₀) ◫ Bₒ) x ◪y = Bₒ x y
          · cases _ : (hYXY.elem y).toSum <;> simp_all [Subtype.toSum, hXY.not_mem_of_mem_right y.property]
          rfl
        · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, HasSubset.Subset.elem, Subtype.coe_prop, toSum_left]
          show
            ∑ i ∈ Finset.univ.filter (fun x : X => Bₒ x y ≠ 0), (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i =
            ∑ i : { x : X // Bₒ x y ≠ 0 }, (- Bₒᵀ y i) • (1 : Matrix X X F₀) x i
          apply Finset.sum_subtype
          simp
      if hx : x ∈ Dₒ then
        exact add_eq_zero_iff_eq_neg'.← (sum_elem_smul_matrix_row_of_mem (- Bₒᵀ y) hx)
      else
        convert_to 0 + 0 = (0 : F₀) using 2
        · simpa [Dₒ, D₁, D₂] using hx
        · exact sum_elem_smul_matrix_row_of_nmem (- Bₒᵀ y) hx
        simp
    have hM : (StandardRepr.mk X Y hXY B hX hY).toMatroid.Indep (y.val ᕃ Dₒ)
    · obtain ⟨d, hd, hd₀⟩ := hD
      simp
      have hDXY : Subtype.val '' Dₒ ⊆ X ∪ Y := (Subtype.coe_image_subset X Dₒ).trans hXXY
      have hyXY : y.val ∈ X ∪ Y := hYXY y.property
      have hyDXY : y.val ᕃ Subtype.val '' Dₒ ⊆ X ∪ Y := Set.insert_subset hyXY hDXY
      use Set.insert_subset hyXY hDXY
      rw [linearIndepOn_iff]
      intro l hl hlB
      have hl' : l.support.toSet ⊆ hyDXY.elem.range
      · rwa [Finsupp.mem_supported] at hl
      have hl'' : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' Dₒ := ↓((hyDXY.elem_range ▸ hl') ·)
      if hly : l (hYXY.elem y) = 0 then
        ext i
        if hil : i ∈ l.support then
          if hiX : i.val ∈ X then
            have hlBiX := congr_fun hlB ⟨i.val, hiX⟩
            rw [Finsupp.linearCombination_apply, Pi.zero_apply, Finsupp.sum, Finset.sum_apply] at hlBiX
            simp_rw [Pi.smul_apply, Function.comp_apply] at hlBiX
            have hlBi : ∑ x ∈ (l.support.image Subtype.val).subtype (· ∈ X), l (hXXY.elem x) • (1 : Matrix X X F) x ⟨i, hiX⟩ = 0
            · simpa using sum_support_image_subtype_eq_zero hXXY hYXY hl'' hly hiX hlBiX
            rwa [
              ((l.support.image Subtype.val).subtype (· ∈ X)).sum_of_single_nonzero
                (fun a : X.Elem => l (hXXY.elem a) • (1 : Matrix X X F) a ⟨i, hiX⟩)
                ⟨i, hiX⟩ (by simp_all) ↓↓↓(by simp_all),
              Matrix.one_apply_eq,
              smul_eq_mul,
              mul_one
            ] at hlBi
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
        have untransposed : l.sum (fun i a => a • ((1 : Matrix X X F) ◫ B) d i.toSum) = 0
        · rwa [←Matrix.transpose_transpose (1 ◫ B), Matrix.one_fromCols_transpose]
        have hyl : hYXY.elem y ∈ l.support
        · rwa [Finsupp.mem_support_iff]
        have h0 : ∀ a ∈ l.support, a.val ≠ y.val → l a • ((1 : Matrix X X F) ◫ B) d a.toSum = 0
        · intro a ha hay
          have hal := hl'' a ha
          if haX : a.val ∈ X then
            convert_to l a • ((1 : Matrix X X F) ◫ B) d ◩⟨a.val, haX⟩ = 0
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
        have hlyd : l (hYXY.elem y) • ((1 : Matrix X X F) ◫ B) d (hYXY.elem y).toSum ≠ 0
        · intro contr
          refine hly ((mul_eq_zero_iff_right ?_).→ contr)
          have := hXY.not_mem_of_mem_right y.property
          simp_all [B, Dₒ, D₁, D₂]
        rw [Finsupp.sum,
          l.support.sum_of_single_nonzero (fun a : (X ∪ Y).Elem => l a • (1 ◫ B) d a.toSum) (hYXY.elem y) hyl]
        at untransposed
        · rw [untransposed] at hlyd
          exact hlyd rfl
        intro i hil hiy
        apply h0 i hil
        intro contr
        apply hiy
        exact SetCoe.ext contr
    exact (hSS' ▸ hMₒ) hM

private lemma B_eq_B_of_same_matroid_same_X {X Y : Set α} {hXY : X ⫗ Y} {B₁ B₂ : Matrix X Y Z2}
    {hX : ∀ a, Decidable (a ∈ X)} {hY : ∀ a, Decidable (a ∈ Y)} [Fintype X]
    (hSS : (StandardRepr.mk X Y hXY B₁ hX hY).toMatroid = (StandardRepr.mk X Y hXY B₂ hX hY).toMatroid) :
    B₁ = B₂ := by
  rw [←B₁.support_Z2, ←B₂.support_Z2]
  exact support_eq_support_of_same_matroid_aux hSS

/-- If two standard representations of the same binary matroid have the same base, they are identical. -/
lemma ext_standardRepr_of_same_matroid_same_X {S₁ S₂ : StandardRepr α Z2} [Fintype S₁.X]
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    S₁ = S₂ := by
  have hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
  apply standardRepr_eq_standardRepr_of_B_eq_B hXX hYY
  apply B_eq_B_of_same_matroid_same_X
  convert hSS
  cc

/-- If two standard representations of the same matroid have the same base, then the standard representation matrices have
    the same support. -/
lemma support_eq_support_of_same_matroid_same_X {F₁ F₂ : Type} [Field F₁] [Field F₂] [DecidableEq F₁] [DecidableEq F₂]
    {S₁ : StandardRepr α F₁} {S₂ : StandardRepr α F₂} [Fintype S₂.X]
    (hSS : S₁.toMatroid = S₂.toMatroid) (hXX : S₁.X = S₂.X) :
    let hYY : S₁.Y = S₂.Y := right_eq_right_of_union_eq_union hXX S₁.hXY S₂.hXY (congr_arg Matroid.E hSS)
    hXX ▸ hYY ▸ S₁.B.support = S₂.B.support := by
  intro hYY
  obtain ⟨X₁, Y₁, _, B₁, _, _⟩ := S₁
  obtain ⟨X₂, Y₂, _, B₂, _, _⟩ := S₂
  simp only at hXX hYY
  let B₀ := hXX ▸ hYY ▸ B₁
  have hB₀ : B₀ = hXX ▸ hYY ▸ B₁
  · rfl
  convert_to B₀.support = B₂.support
  · cc
  have hSS' : (StandardRepr.mk X₂ Y₂ _ B₀ _ _).toMatroid = (StandardRepr.mk X₂ Y₂ _ B₂ _ _).toMatroid
  · convert hSS <;> cc
  exact support_eq_support_of_same_matroid_aux hSS'
