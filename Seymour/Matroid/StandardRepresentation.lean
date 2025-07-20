import Seymour.Basic.Fin
import Seymour.Matrix.SubmoduleBasis
import Seymour.Matrix.LinearIndependence
import Seymour.Matrix.Pivoting
import Seymour.Matrix.Support
import Seymour.Matroid.FromMatrix

/-!
# Standard Representation

Here we study the standard representation of vector matroids.
-/

open scoped Matrix Set.Notation


/-! ## Definition and API -/

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

private abbrev mkStandardRepr {α R : Type} [DecidableEq α]
    {X : Set α} [hX : ∀ a, Decidable (a ∈ X)]
    {Y : Set α} [hY : ∀ a, Decidable (a ∈ Y)]
    (hXY : X ⫗ Y) (B : Matrix X Y R) :
    StandardRepr α R :=
  ⟨X, Y, hXY, B, hX, hY⟩

attribute [instance] StandardRepr.decmemX
attribute [instance] StandardRepr.decmemY


variable {α : Type}

lemma Matroid.IsBase.not_ssubset_indep {M : Matroid α} {G I : Set α} (hMG : M.IsBase G) (hMI : M.Indep I) : ¬(G ⊂ I) :=
  (M.isBase_iff_maximal_indep.→ hMG).not_ssuperset hMI

private noncomputable abbrev Set.equivFin (S : Set α) [Fintype S] : Fin #S ≃ S :=
  (Fintype.equivFin S.Elem).symm

@[app_unexpander Set.equivFin]
private def Set.equivFin_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $S) => `($(S).$(Lean.mkIdent `equivFin))
  | _ => throw ()


variable [DecidableEq α] {R : Type}

/-- Convert standard representation of a vector matroid to a full representation. -/
def StandardRepr.toFull [Zero R] [One R] (S : StandardRepr α R) : Matrix S.X (S.X ∪ S.Y).Elem R :=
  ((1 ◫ S.B) · ∘ Subtype.toSum)

lemma StandardRepr.toFull_indep_iff [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toFull.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) := by
  rfl

lemma StandardRepr.toFull_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toFull.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ hI.elem.range := by
  rw [StandardRepr.toFull_indep_iff]
  unfold HasSubset.Subset.elem
  aesop

attribute [local ext] StandardRepr in
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
  S.toFull.toMatroid

/-- Ground set of a vector matroid is the union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toMatroid_E [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.E = S.X ∪ S.Y :=
  rfl

lemma StandardRepr.toMatroid_indep_iff [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    I ⊆ S.X ∪ S.Y ∧ LinearIndepOn R ((1 ◫ S.B) · ∘ Subtype.toSum)ᵀ ((S.X ∪ S.Y) ↓∩ I) :=
  S.toFull_indep_iff I

lemma StandardRepr.toMatroid_indep_iff_elem [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B)ᵀ ∘ Subtype.toSum) hI.elem.range :=
  S.toFull_indep_iff_elem I

lemma StandardRepr.toMatroid_indep_iff_submatrix [DivisionRing R] (S : StandardRepr α R) (I : Set α) :
    S.toMatroid.Indep I ↔
    ∃ hI : I ⊆ S.X ∪ S.Y, LinearIndependent R ((1 ◫ S.B).submatrix id (Subtype.toSum ∘ hI.elem))ᵀ :=
  S.toFull.indepCols_iff_submatrix I

@[simp]
lemma StandardRepr.toMatroid_indep [DivisionRing R] (S : StandardRepr α R) :
    S.toMatroid.Indep = (∃ hI : · ⊆ S.X ∪ S.Y, LinearIndepOn R ((1 ◫ S.B)ᵀ ∘ Subtype.toSum) hI.elem.range) := by
  ext I
  exact S.toFull_indep_iff_elem I

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


/-! ## Guaranteeing that a standard representation of desired properties exists -/

lemma Matrix.longTableauPivot_toMatroid [Field R] {X Y : Set α} (A : Matrix X Y R) {x : X} {y : Y} (hAxy : A x y ≠ 0) :
    (A.longTableauPivot x y).toMatroid = A.toMatroid := by
  ext
  · rfl
  · exact and_congr_right_iff.← ↓(A.longTableauPivot_linearIndepenOn hAxy _)

private lemma exists_standardRepr_isBase_aux_left {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)]
    [DivisionRing R] {A : Matrix X Y R} {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hAI : LinearIndepOn R A hIX.elem.range) :
    LinearIndepOn R
      ((1 ⊟ ((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id))
        ∘ Subtype.toSum)
      hIGX.elem.range := by
  have hX : G ∪ (X \ G) = X := Set.union_diff_cancel' (by tauto) hGX
  let e : hIGX.elem.range → hIX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert (B.linearIndepOn_in_submodule hAI).comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · simp_rw [hij]
        simp only [hij, if_true] at hBij
        convert hBij
        ext
        apply hB
    else
      convert Eq.refl (0 : R)
      · simpa [Matrix.one_apply, hiG] using hij
      · convert hBij
        · ext
          apply hB
        · symm
          simpa using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [hiX, hiG, e, Matrix.submatrix, Subtype.toSum]

private lemma exists_standardRepr_isBase_aux_right {X Y G I : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ G)]
    [DivisionRing R] {A : Matrix X Y R} {B : Basis G R (Submodule.span R A.range)}
    (hGX : G ⊆ X) (hXGX : X \ G ⊆ X) -- tautological but keep
    (hIX : I ⊆ X) (hIGX : I ⊆ G ∪ (X \ G)) -- redundant but keep
    (hB : ∀ i : α, ∀ g : G, ∀ hiX : i ∈ X, ∀ hiG : i ∈ G, ∀ hiR : A ⟨i, hiX⟩ ∈ Submodule.span R A.range,
      B.repr ⟨A ⟨i, hiX⟩, hiR⟩ g = B.repr (B ⟨i, hiG⟩) g)
    (hBI : LinearIndepOn R
      ((1 ⊟ ((Matrix.of (fun x : X => fun g : G => B.repr ⟨A x, in_submoduleSpan_range A x⟩ g)).submatrix hXGX.elem id))
        ∘ Subtype.toSum) hIGX.elem.range) :
    LinearIndepOn R A hIX.elem.range := by
  apply B.linearIndepOn_of_in_submodule
  have hX : X = G ∪ (X \ G) := (Set.union_diff_cancel' (by tauto) hGX).symm
  let e : hIX.elem.range → hIGX.elem.range := fun ⟨⟨i, hi⟩, hhi⟩ => ⟨⟨i, hX ▸ hi⟩, by simpa using hhi⟩
  unfold LinearIndepOn
  convert hBI.comp e (fun _ _ hee => by ext; simpa [e] using hee) with ⟨⟨i, hi⟩, -⟩
  ext ⟨j, hj⟩
  if hiG : i ∈ G then
    have hBij := B.repr_self_apply ⟨i, hiG⟩ ⟨j, hj⟩
    if hij : i = j then
      convert Eq.refl (1 : R)
      · simp [*]
      · simp [hiG, e, Matrix.submatrix, Subtype.toSum]
        simpa [hiG, e, Matrix.one_apply] using hij
    else
      convert Eq.refl (0 : R)
      · simp [*]
      · simp [hiG, e, Matrix.submatrix, Subtype.toSum]
        simpa [Matrix.one_apply] using hij
  else
    have hiX : i ∈ X := hX ▸ hi
    simp [hiX, hiG, e, Matrix.submatrix, Subtype.toSum]

/-- Every vector matroid has a standard representation whose rows are a given base. -/
lemma Matrix.exists_standardRepr_isBase [DivisionRing R] {X Y G : Set α}
    (A : Matrix X Y R) (hAG : A.toMatroid.IsBase G) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = A.toMatroid := by
  have hGY : G ⊆ Y := hAG.subset_ground
  -- First, prove that `G`-cols of `A` span the entire vector space generated by `Y`-cols of `A` (i.e., the entire colspace).
  have hRAGY : Submodule.span R (Aᵀ.submatrix hGY.elem id).range = Submodule.span R Aᵀ.range
  · have easy : (Aᵀ.submatrix hGY.elem id).range ⊆ Aᵀ.range
    · intro v ⟨j, hjv⟩
      exact ⟨hGY.elem j, hjv⟩
    have difficult : Aᵀ.range ≤ Submodule.span R (Aᵀ.submatrix hGY.elem id).range
    · by_contra contr
      obtain ⟨v, ⟨j, hjv⟩, hvG⟩ : ∃ v : X → R, v ∈ Aᵀ.range ∧ v ∉ Submodule.span R (Aᵀ.submatrix hGY.elem id).range :=
        Set.not_subset.→ contr
      have hj : j.val ∉ G
      · intro hjG
        apply hvG
        have hv : v ∈ (Aᵀ.submatrix hGY.elem id).range
        · aesop
        rw [Submodule.mem_span]
        exact ↓(· hv)
      have hMvG : A.toMatroid.Indep (j.val ᕃ G)
      · obtain ⟨-, hAG⟩ := hAG.indep
        use Set.insert_subset_iff.← ⟨j.property, hGY⟩
        convert_to LinearIndepOn R Aᵀ (j ᕃ (Y ↓∩ G))
        · aesop
        rw [linearIndepOn_insert_iff]
        use hAG
        intro hjR
        exfalso
        apply hvG
        rw [←hjv]
        convert hjR
        aesop
      exact hAG.not_ssubset_indep hMvG (Set.ssubset_insert hj)
    exact le_antisymm (Submodule.span_mono easy) (Submodule.span_le.← difficult)
  obtain ⟨-, lin_indep⟩ := hAG.indep
  let B : Basis G R (Submodule.span R Aᵀ.range)
  · apply Basis.mk (v := fun j : G.Elem => ⟨Aᵀ (hGY.elem j), in_submoduleSpan_range Aᵀ (hGY.elem j)⟩)
    · unfold LinearIndepOn at lin_indep
      rw [linearIndependent_iff'] at lin_indep ⊢
      intro s g hsg i hi
      let e : (Y ↓∩ G).Elem ≃ G.Elem :=
        ⟨G.restrictPreimage Subtype.val, (⟨hGY.elem ·, by simp⟩), congr_fun rfl, congr_fun rfl⟩
      have hsA : ∑ i ∈ s.map e.symm.toEmbedding, (g ∘ e) i • Aᵀ i = 0
      · rw [Subtype.ext_iff_val, ZeroMemClass.coe_zero] at hsg
        rw [←hsg]
        convert_to ∑ x ∈ s, g x • Aᵀ (e.symm x) = ∑ x ∈ s, g x • Aᵀ (hGY.elem x)
        · simp
        · simp
        rfl
      exact lin_indep (s.map e.symm.toEmbedding) (g ∘ e) hsA (e.symm i) (Finset.mem_map_equiv.← hi)
    · apply le_of_eq
      -- Christian Merten's idea:
      apply Submodule.map_injective_of_injective (Submodule.span R Aᵀ.range).subtype_injective
      simp [←hRAGY, Submodule.map_span, ←Set.range_comp, Function.comp_def]
      rfl
  let C : Matrix G Y R := (fun i : G => fun j : Y => B.coord i ⟨Aᵀ j, in_submoduleSpan_range Aᵀ j⟩)
  have hYGY : Y \ G ⊆ Y := Set.diff_subset
  use ⟨G, Y \ G, Set.disjoint_sdiff_right, C.submatrix id hYGY.elem,
    (Classical.propDecidable <| · ∈ G), (Classical.propDecidable <| · ∈ Y \ G)⟩
  constructor
  · simp
  ext I hIGY
  · aesop
  have hGYY : G ∪ Y = Y := Set.union_eq_self_of_subset_left hGY
  have hB :
    ∀ j : α, ∀ g : G, ∀ hjy : j ∈ Y, ∀ hjg : j ∈ G, ∀ hjR : Aᵀ ⟨j, hjy⟩ ∈ Submodule.span R Aᵀ.range,
      B.repr ⟨Aᵀ ⟨j, hjy⟩, hjR⟩ g = B.repr (B ⟨j, hjg⟩) g
  · simp [B]
  simp only [Matrix.toMatroid_indep_iff_elem, StandardRepr.toMatroid_indep_iff_elem,
    Matrix.one_fromCols_transpose, Matrix.transpose_submatrix, Set.union_diff_self]
  constructor
  · intro ⟨hI, hRCI⟩
    use hGYY ▸ hI
    classical
    apply exists_standardRepr_isBase_aux_right hGY hYGY (hGYY ▸ hI) hIGY hB
    convert hRCI
  · intro ⟨hI, hRAI⟩
    use hGYY.symm ▸ hI
    classical
    convert exists_standardRepr_isBase_aux_left hGY hYGY hI hIGY hB hRAI

/-- Every vector matroid has a standard representation. -/
lemma Matrix.exists_standardRepr [DivisionRing R] {X Y : Set α} (A : Matrix X Y R) :
    ∃ S : StandardRepr α R, S.toMatroid = A.toMatroid := by
  peel A.exists_standardRepr_isBase A.toMatroid.exists_isBase.choose_spec with hS
  exact hS.right

set_option maxHeartbeats 666666 in
-- Implicit Gaussian elimination for the proof of the lemma below.
private lemma Matrix.exists_standardRepr_isBase_isTotallyUnimodular_aux [Field R] {X Y G : Set α} [Fintype G]
    (A : Matrix X Y R) (hAG : A.toMatroid.IsBase G) (hA : A.IsTotallyUnimodular) {k : ℕ} (hk : k ≤ #G) :
    ∃ X' : Set α, ∃ A' : Matrix X' Y R,
      A'.toMatroid = A.toMatroid ∧ A'.IsTotallyUnimodular ∧ ∃ hGY : G ⊆ Y, ∃ f : Fin k → X', f.Injective ∧
        ∀ i : X', ∀ j : Fin k,
          if i = f j
          then A' i (hGY.elem (G.equivFin ⟨j.val, by omega⟩)) = 1
          else A' i (hGY.elem (G.equivFin ⟨j.val, by omega⟩)) = 0
    := by
  induction k with
  | zero =>
    use X, A, rfl, hA, hAG.subset_ground, (Nat.not_succ_le_zero _ ·.isLt |>.elim), ↓↓↓(by omega)
    intro _ ⟨_, _⟩
    omega
  | succ n ih =>
    obtain ⟨X', A', hAA, hA', hGY, f, hf, hfA'⟩ := ih (by omega)
    have hnG : n < #G
    · omega
    wlog hgf : ∃ x : X', A' x (hGY.elem (G.equivFin ⟨n, hnG⟩)) ≠ 0 ∧ x ∉ f.range
    · push_neg at hgf
      exfalso
      let X' := { x : X' | A' x (hGY.elem (G.equivFin ⟨n, hnG⟩)) ≠ 0 }
      let G' := { G.equivFin ⟨i.val, by omega⟩ | (i : Fin n) (hi : f i ∈ X') } -- essentially `G' = g (f⁻¹ X')`
      let G'' : Set G := G.equivFin ⟨n, hnG⟩ ᕃ G' -- essentially `G'' = g (n ᕃ f⁻¹ X')`
      have hgG' : G.equivFin ⟨n, hnG⟩ ∉ G'
      · intro ⟨i, hfi, hgi⟩
        apply G.equivFin.injective at hgi
        exact (congr_arg Fin.val hgi ▸ i.isLt).false
      have hG'' : ¬ A'.toMatroid.Indep G''
      · simp
        intro _
        rw [linearDepOn_iff]
        classical
        let c : Y → R := fun j : Y =>
          if hjG : j.val ∈ G then
            let j' : G := ⟨j.val, hjG⟩
            if hj' : j' ∈ G' then A' (f hj'.choose) (hGY.elem (G.equivFin ⟨n, hnG⟩))
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
        · have hc' : (Finsupp.ofSupportFinite c (hc ▸ (hGY.elem '' G'').toFinite)).support = (hGY.elem '' G'').toFinset :=
            eq_toFinset_of_toSet_eq (ofSupportFinite_support_eq (Finite.Set.finite_image G'' hGY.elem) hc)
          rw [Finsupp.ofSupportFinite_coe, hc']
          ext x
          rw [Finset.sum_apply]
          show ∑ j ∈ hGY.elem '' G'', c j • A'ᵀ j x = 0
          have hG'' :
              (hGY.elem '' G'').toFinset =
              hGY.elem (G.equivFin ⟨n, hnG⟩) ᕃ G'.toFinset.map ⟨hGY.elem, hGY.elem_injective⟩
          · simp only [G'']
            clear * -
            aesop
          rw [hG'', Finset.sum_insert (hgG' <| by simpa using ·)]
          if hx : x ∈ X' then
            rw [add_eq_zero_iff_eq_neg', Finset.sum_map, ←Finset.sum_attach]
            specialize hfA' x
            simp [c, hgG']
            conv_lhs => congr; rfl; ext x; rw [dite_of_true (Set.mem_toFinset.→ x.property)]
            obtain ⟨i, hi⟩ := hgf x hx
            have hiG' : G.equivFin ⟨i.val, by omega⟩ ∈ G'
            · use i, hi ▸ hx
            rw [G'.toFinset.attach.sum_of_single_nonzero _ ⟨G.equivFin ⟨i.val, by omega⟩, G'.mem_toFinset.← hiG'⟩]
            · specialize hfA' i
              simp [hi] at hfA'
              rw [hfA']
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
              specialize hfA' a
              rw [←hi] at hfA' ⊢
              have hfifa : f i ≠ f a
              · intro hia
                apply hf at hia
                apply hzi
                ext
                rw [←haz]
                simp [hia]
              simp [hfifa] at hfA'
              exact haz ▸ hfA'
          else
            convert add_zero (0 : R)
            · exact smul_eq_zero_of_right _ (by simpa [X'] using hx)
            · rw [Finset.sum_map]
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
                exact smul_eq_zero_of_right _ (hgja ▸ (by simpa [hxj] using hfA' x j))
        · simp only [Finsupp.ofSupportFinite, ne_eq, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int]
          intro hc0
          rw [Finsupp.ext_iff] at hc0
          specialize hc0 (hGY.elem (G.equivFin ⟨n, hnG⟩))
          simp [c, hgG'] at hc0
      have hGG'' : Subtype.val '' G'' ⊆ G
      · simp
      exact hG'' (hAA ▸ hAG.indep.subset hGG'')
    obtain ⟨x, hx, hxf⟩ := hgf
    let f' : Fin n.succ → X' := Fin.snoc f x
    use X', A'.longTableauPivot x (hGY.elem (G.equivFin ⟨n, hnG⟩)),
      hAA ▸ A'.longTableauPivot_toMatroid hx, hA'.longTableauPivot _ _ hx, hGY, f'
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
        rw [A'.longTableauPivot_elem_of_zero_in_pivot_row hxj.symm (by simpa [hxjₙ] using hfA' x jₙ)]
        simpa [hijₙ, hjjₙ] using hfA' i jₙ
      else
        have hijₙ : i ≠ f jₙ := hjjₙ ▸ hij
        have hxjₙ : x ≠ f jₙ := hjjₙ ▸ hxj
        simp [hij]
        if hix : i = x then
          rw [←hix]
          apply A'.longTableauPivot_elem_in_pivot_row_eq_zero
          simpa [hijₙ] using hfA' i jₙ
        else
          rw [A'.longTableauPivot_elem_of_zero_in_pivot_row hix]
          · simpa [hijₙ] using hfA' i jₙ
          · simpa [hxjₙ] using hfA' x jₙ
    else
      have hjn : j.val = n
      · omega
      have hgjgn : G.equivFin ⟨j.val, by omega⟩ = G.equivFin ⟨n, hnG⟩
      · simp [hjn]
      have hxj : x = f' j
      · simp [f', hjn, Fin.snoc]
      if hij : i = f' j then
        simpa [hij, hgjgn, hxj] using A'.longTableauPivot_elem_pivot_eq_one (hxj ▸ hx)
      else
        simpa [hij, hgjgn, hxj] using A'.longTableauPivot_elem_in_pivot_col_eq_zero hij (hxj ▸ hx)

set_option maxHeartbeats 333333 in
/-- Every vector matroid whose full representation matrix is totally unimodular has a standard representation whose rows are
    a given base and the standard representation matrix is totally unimodular.
    Unlike `Matrix.exists_standardRepr_isBase` this lemma does not allow infinite `G` and does not allow `R` to have
    noncommutative multiplication. -/
lemma Matrix.exists_standardRepr_isBase_isTotallyUnimodular [Field R] {X Y G : Set α} [Fintype G]
    (A : Matrix X Y R) (hAG : A.toMatroid.IsBase G) (hA : A.IsTotallyUnimodular) :
    ∃ S : StandardRepr α R, S.X = G ∧ S.toMatroid = A.toMatroid ∧ S.B.IsTotallyUnimodular := by
  obtain ⟨X', A', hAA, hA', hGY, f, hf, hfA'⟩ := A.exists_standardRepr_isBase_isTotallyUnimodular_aux hAG hA (le_refl #G)
  have hGA' := hAA ▸ hAG
  rw [←hAA] at *
  clear hA hAG hAA A
  have hYGY : Y \ G ⊆ Y := Set.diff_subset
  have hGYY : G ∪ Y = Y := Set.union_eq_self_of_subset_left hGY
  let g : G ↪ X' := ⟨f ∘ Fintype.equivFin G, ((Fintype.equivFin G).injective_comp f).← hf⟩
  let g' : G.Elem → (Subtype.val '' g.toFun.range).Elem := (⟨g ·, by simp⟩)
  let g'' : (Subtype.val '' g.toFun.range).Elem → G.Elem
  · intro ⟨i, hi⟩
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_and_right, exists_eq_right] at hi
    exact ⟨hi.choose_spec.choose, hi.choose_spec.choose_spec.choose⟩
  have hXgX : X' \ g.toFun.range ⊆ X' := Set.diff_subset
  let ξ : (X' \ g.toFun.range).Elem → X' := hXgX.elem
  classical
  let e : (Subtype.val '' g.toFun.range) ⊕ (X' \ g.toFun.range).Elem ≃ X' :=
    (Subtype.coe_image_subset X' g.toFun.range).equiv
  let e' : G ≃ (Subtype.val '' g.toFun.range) := ⟨
    g',
    g'',
    ↓(by simp [g'', g']),
    fun ⟨i, hi⟩ => by simp [g'', g']; simp at hi; have := hi.choose_spec.choose_spec; aesop
  ⟩
  have hA₁₁ : A'.submatrix g hGY.elem = 1
  · ext i j
    if hij : i = j then
      rw [hij, Matrix.one_apply_eq]
      simpa [g] using hfA' (g j) ((Fintype.equivFin G) j)
    else
      rw [Matrix.one_apply_ne hij]
      have hfifj : f ((Fintype.equivFin G) i) ≠ f ((Fintype.equivFin G) j)
      · exact (hij <| by simpa using hf ·)
      simpa [hfifj] using hfA' (f ((Fintype.equivFin G) i)) ((Fintype.equivFin G) j)
  have hA₂₁ : A'.submatrix ξ hGY.elem = 0
  · ext ⟨i, hi⟩ j
    have hiX : i ∈ X' := hXgX hi
    have hij : ⟨i, hiX⟩ ≠ f ((Fintype.equivFin G) j)
    · simp at hi
      aesop
    simpa [hij] using hfA' ⟨i, hiX⟩ ((Fintype.equivFin G) j)
  have hA₂₂ : A'.submatrix ξ hYGY.elem = 0
  · ext ⟨i, hi⟩ ⟨j, hj⟩
    have hiX : i ∈ X' := hXgX hi
    have hjY : j ∈ Y := hYGY hj
    simp only [Function.Embedding.toFun_eq_coe, HasSubset.Subset.elem, Matrix.submatrix_apply, Matrix.zero_apply]
    by_contra hAij
    have hAjG : A'.toMatroid.Indep (j ᕃ G)
    · simp only [Matrix.toMatroid_indep_iff_elem]
      have hjGY : j ᕃ G ⊆ Y := Set.insert_subset (hYGY hj) hGY
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
          have hiz : ⟨i, hiX⟩ ≠ f (Fintype.equivFin G ⟨z.val, hzG⟩)
          · intro hiXz
            have hifz := congr_arg Subtype.val hiXz
            simp at hifz
            simp [hifz, g] at hi
          simpa [hiz] using hfA' ⟨i, hiX⟩ (Fintype.equivFin G ⟨z.val, hzG⟩)
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
        have hAaa : A' (g ⟨a.val, haG⟩) a ≠ 0
        · intro h0
          specialize hfA' (g ⟨a.val, haG⟩) (Fintype.equivFin G ⟨a.val, haG⟩)
          have haa : g ⟨a.val, haG⟩ = f (Fintype.equivFin G ⟨a.val, haG⟩)
          · rfl
          simp [←haa, h0] at hfA'
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
          specialize hfA' (g ⟨a.val, haG⟩) (Fintype.equivFin G ⟨z.val, hzG⟩)
          have haz : g ⟨a.val, haG⟩ ≠ f (Fintype.equivFin G ⟨z.val, hzG⟩) := (by
            apply hza
            ext
            simpa using g.injective ·.symm)
          simpa [haz] using hfA'
    apply hGA'.not_ssubset_indep hAjG
    exact ⟨G.subset_insert j, Set.not_subset.← ⟨j, G.mem_insert j, hj.right⟩⟩
  have hA :
    A'.submatrix (e'.leftCongr.trans e) hGY.equiv =
    ⊞ (A'.submatrix g hGY.elem) (A'.submatrix g hYGY.elem)
      (A'.submatrix ξ hGY.elem) (A'.submatrix ξ hYGY.elem)
  · rw [←(A'.submatrix (e'.leftCongr.trans e) hGY.equiv).fromBlocks_toBlocks, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> rfl
  rw [hA₁₁, hA₂₁, hA₂₂, ←Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromCols_zero] at hA
  have hA'' : A'.toMatroid =
      (((1 ◫ A'.submatrix g hYGY.elem) ⊟ 0).reindex (e'.leftCongr.trans e) hGY.equiv).toMatroid
  · rewrite [←((Matrix.reindex (e'.leftCongr.trans e) hGY.equiv).symm_apply_eq).→ hA]
    rfl
  use ⟨G, Y \ G, Set.disjoint_sdiff_right, A'.submatrix g hYGY.elem,
    G.decidableMemOfFintype, (Classical.propDecidable <| · ∈ Y \ G)⟩
  refine ⟨by simp, ?_, hA'.submatrix g hYGY.elem⟩
  rw [hA'']
  simp only [StandardRepr.toMatroid, StandardRepr.toFull]
  convert (Matrix.fromCols 1 (A'.submatrix g hYGY.elem)).fromRows_zero_reindex_toMatroid hGY (e'.leftCongr.trans e)
  ext _ j
  if hjG : j.val ∈ G then
    simp [StandardRepr.toFull, hjG]
  else
    cases j.property <;> simp [*, StandardRepr.toFull] at hjG ⊢


/-! ## Conditional uniqueness of standard representation -/

omit R

private lemma sum_support_image_subtype_eq_zero {X Y : Set α} {F : Type} [Field F] {B : Matrix Y X F} {D : Set X} {y : Y}
    [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXXY : X ⊆ X ∪ Y) (hYXY : Y ⊆ X ∪ Y) -- redundant but keep
    {l : (X ∪ Y).Elem →₀ F} (hl : ∀ e ∈ l.support, e.val ∈ y.val ᕃ Subtype.val '' D) (hly : l (hYXY.elem y) = 0)
    {i : (X ∪ Y).Elem} (hiX : i.val ∈ X) (hlBi : ∑ a ∈ l.support, l a • (1 ⊟ B) a.toSum ⟨i, hiX⟩ = 0) :
    ∑ a ∈ (l.support.image Subtype.val).subtype (· ∈ X),
      l (hXXY.elem a) • (1 ⊟ B) (hXXY.elem a).toSum ⟨i, hiX⟩ = 0 := by
  rw [←Finset.sum_finset_coe] at hlBi
  convert hlBi
  apply Finset.sum_bij (⟨hXXY.elem ·, by simpa using ·⟩)
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
        exfalso
        have hzy : z.val = hYXY.elem y := Subtype.coe_inj.→ hp
        rw [←hzy] at hly
        exact (l.mem_support_iff.→ (Finset.coe_mem z)) hly
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
    [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] [Fintype X]
    (hSS : (mkStandardRepr hXY B₁).toMatroid = (mkStandardRepr hXY B₂).toMatroid) :
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
    have hMₒ : ¬ (mkStandardRepr hXY Bₒ).toMatroid.Indep (y.val ᕃ Dₒ)
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
    have hM : (mkStandardRepr hXY B).toMatroid.Indep (y.val ᕃ Dₒ)
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
    [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] [Fintype X]
    (hSS : (mkStandardRepr hXY B₁).toMatroid = (mkStandardRepr hXY B₂).toMatroid) :
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
  have hSS' : (mkStandardRepr _ B₀).toMatroid = (mkStandardRepr _ B₂).toMatroid
  · convert hSS <;> cc
  exact support_eq_support_of_same_matroid_aux hSS'
