import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Order.Zorn
import Mathlib.Data.Matroid.Loop

-- Adapted from: https://github.com/apnelson1/Matroid

section formathlib_la_linindepon

open Set Submodule

noncomputable def Basis.mkImage {ι R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s)) :
    Basis s R M :=
  Basis.mk hli.linearIndependent <| by rwa [← image_eq_range]

theorem Basis.mkImage_repr {ι R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s))
    (x : M) : (Basis.mkImage hli hsp).repr x =
    hli.repr ⟨x, by rw [← image_eq_range, top_le_iff.1 hsp]; exact mem_top⟩  := by
  simp [Basis.mkImage]

end formathlib_la_linindepon


section matroid_loop

variable {α : Type}

namespace Matroid

/-- A `nonloop` is an element that is not a loop -/
def IsNonloop (M : Matroid α) (e : α) : Prop :=
  ¬M.IsLoop e ∧ e ∈ M.E

lemma IsNonloop.mem_ground {M : Matroid α} {e : α} (h : M.IsNonloop e) : e ∈ M.E :=
  h.2

lemma indep_singleton {M : Matroid α} {e : α} : M.Indep {e} ↔ M.IsNonloop e := by
  rw [IsNonloop, ← singleton_dep, dep_iff, not_and, not_imp_not, Set.singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, Set.singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

end Matroid

end matroid_loop


section matroid_representation_basic

variable {α W 𝔽 : Type} {e : α} {I E X Y : Set α} {M : Matroid α} [DivisionRing 𝔽] [AddCommGroup W] [Module 𝔽 W]

open Set Submodule

namespace Matroid

/-- `M.Rep 𝔽 W` is a function from `α` to a module `W` that represents `M`. -/
@[ext] structure Rep (M : Matroid α) (𝔽 W : Type) [Semiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (indep_iff' : ∀ I, M.Indep I ↔ LinearIndepOn 𝔽 to_fun I)

instance : FunLike (M.Rep 𝔽 W) α W where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

lemma Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndepOn 𝔽 v I :=
  v.indep_iff' I

lemma Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndepOn 𝔽 v I :=
  v.indep_iff.1 hI

lemma Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff]

lemma Rep.eq_zero_of_not_mem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

lemma Rep.isBasis'_iff (v : M.Rep 𝔽 W) :
    M.IsBasis' I X ↔ I ⊆ X ∧ LinearIndepOn 𝔽 v I ∧ v '' X ⊆ span 𝔽 (v '' I) := by
  have aux ⦃I J : Set α⦄ : M.Indep J ∧ J ⊆ X → I ⊆ J → M.Indep I ∧ I ⊆ X :=
    fun h hJI ↦ ⟨h.1.subset hJI, hJI.trans h.2⟩
  simp only [IsBasis', maximal_iff_forall_insert aux, insert_subset_iff, not_and, image_subset_iff]
  simp +contextual only [v.indep_iff, linearIndepOn_insert_iff, imp_false, and_imp, iff_def,
    true_and, not_true_eq_false, not_imp_not, forall_const, and_self]
  refine ⟨fun hI hIX h e heX ↦ (em (e ∈ I)).elim (fun heI ↦ ?_) fun heI ↦ h e heI heX,
    fun hIX hI hX e heI heX ↦ hX heX⟩
  exact mem_of_mem_of_subset heI <| (subset_preimage_image v I).trans <| preimage_mono subset_span

lemma Rep.mem_closure_iff (v : M.Rep 𝔽 W) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ v e ∈ span 𝔽 (v '' X) := by
  obtain ⟨I, hIX⟩ := M.exists_isBasis' X
  have aux : span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
    (span_mono (image_mono hIX.subset)).antisymm <| span_le.2 (v.isBasis'_iff.1 hIX).2.2
  rw [← hIX.closure_eq_closure, ← aux, ← not_iff_not, (v.onIndep hIX.indep).not_mem_span_iff,
    hIX.indep.not_mem_closure_iff, v.indep_iff]

lemma Rep.closure_eq (v : M.Rep 𝔽 W) (X : Set α) : M.closure X = (v ⁻¹' span 𝔽 (v '' X)) ∩ M.E := by
  ext e
  by_cases he : e ∈ M.E
  · rw [v.mem_closure_iff, mem_inter_iff, and_iff_left he, mem_preimage, SetLike.mem_coe]
  simp [he, not_mem_subset (M.closure_subset_ground X) he]

lemma Rep.span_le_of_closure_subset (v : M.Rep 𝔽 W) (hXY : M.closure X ⊆ M.closure Y) :
    span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
  rw [span_le]
  rintro _ ⟨e, he, rfl⟩
  obtain heE | heE := em' (e ∈ M.E)
  · simp [v.eq_zero_of_not_mem_ground heE]
  rw [v.closure_eq Y] at hXY
  exact (hXY (M.mem_closure_of_mem' he heE)).1

lemma Rep.span_closure_congr (v : M.Rep 𝔽 W) (hXY : M.closure X = M.closure Y) :
    span 𝔽 (v '' X) = span 𝔽 (v '' Y) :=
  (v.span_le_of_closure_subset hXY.subset).antisymm (v.span_le_of_closure_subset hXY.symm.subset)

end Matroid

end matroid_representation_basic


section matroid_representation_map

variable {α W W' 𝔽 : Type} {M : Matroid α} [DivisionRing 𝔽] [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Submodule

namespace Matroid

/-- Compose a representation `v` with a linear map that is injective on the range of `v`-/
def Rep.comp (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W')
    (h_inj : Disjoint (span 𝔽 (range v)) (LinearMap.ker ψ)) : M.Rep 𝔽 W' where
  to_fun := ψ ∘ v
  indep_iff' := fun I ↦ by
    rw [LinearMap.linearIndepOn_iff_of_injOn, v.indep_iff]
    exact LinearMap.injOn_of_disjoint_ker (span_mono <| image_subset_range ..) h_inj

/-! ### Maps between representations -/

/-- Compose a representation with a linear injection. -/
def Rep.comp' (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) := v.comp ψ (by simp [hψ])

/-- Compose a representation with a linear equivalence. -/
def Rep.compEquiv (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := v.comp' ψ ψ.ker

@[simp] lemma Rep.compEquiv_apply (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) :
    (v.compEquiv ψ) e = ψ (v e) := rfl

end Matroid

end matroid_representation_map


variable {α W 𝔽 : Type} {B : Set α} {M : Matroid α} [DivisionRing 𝔽] [AddCommGroup W] [Module 𝔽 W]

open Set Submodule Finsupp

namespace Matroid

lemma Rep.span_spanning_eq (v : M.Rep 𝔽 W) {S : Set α} (hS : M.Spanning S) :
    span 𝔽 (v '' S) = span 𝔽 (range v) := by
  rw [← image_univ]
  apply span_closure_congr
  simp [hS.closure_eq]

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (v : M.Rep 𝔽 W) : Prop := ⊤ ≤ span 𝔽 (range v)

/-- Restrict a representation to the submodule spanned by its image -/
@[simps] def Rep.restrictSpan (v : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range v)) where
  to_fun := codRestrict v _ (fun x ↦ subset_span (mem_range_self _))
  indep_iff' := (by
    intro I
    rw [v.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coe_subtype]),
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

lemma Rep.FullRank.span_range {v : M.Rep 𝔽 W} (h : v.FullRank) : span 𝔽 (range v) = ⊤ := by
  rwa [eq_top_iff]

lemma Rep.FullRank.span_spanning {v : M.Rep 𝔽 W} (h : v.FullRank) {S : Set α} (hS : M.Spanning S) :
    span 𝔽 (v '' S) = ⊤ := by
  rw [← h.span_range, v.span_spanning_eq hS]

lemma Rep.restrictSpan_eq_inclusion (v : M.Rep 𝔽 W) :
    (v.restrictSpan : α → _) = Set.inclusion subset_span ∘ rangeFactorization v := by
  ext; rfl

@[simp] lemma Rep.restrict_span_apply (v : M.Rep 𝔽 W) (e : α) :
    v.restrictSpan e = Set.inclusion subset_span (rangeFactorization v e) := rfl

lemma Rep.restrictSpan_fullRank (v : M.Rep 𝔽 W) : v.restrictSpan.FullRank := by
  change _ ≤ span 𝔽 _
  rw [restrictSpan_eq_inclusion]
  change _ ≤ span 𝔽 (range (Set.inclusion subset_span ∘ _))
  rw [range_comp, surjective_onto_range.range_eq, image_univ, Set.range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑v))) ⁻¹' _)
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_isBase {v : M.Rep 𝔽 W} (h : v.FullRank) (hB : M.IsBase B) :
    _root_.Basis B 𝔽 W :=
  Basis.mkImage (v.onIndep hB.indep) (h.span_spanning hB.spanning).symm.le

/-- The natural representation with rows indexed by a base with `Finsupp` -/
noncomputable def Rep.standardRep' (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrictSpan.compEquiv (v.restrictSpan_fullRank.basis_of_isBase hB).repr

section IsStandard

variable {γ : Type} {B : Set α} [FunLike γ B 𝔽] [AddCommGroup γ] [Module 𝔽 γ]

/-- A representation over `B → 𝔽` or `B →₀ 𝔽` `IsStandard` if it is the identity on `B`.
The definition is agnostic as to whether the representation is `Finsupp` or `Function`,
and is phrased without `Function.Pi` to avoid decidability assumptions.

In the `Finsupp` case, this implies that `B` is a base - see `Matroid.Rep.IsStandard.isBase`.

In the `Function` case, we really need a `FiniteRank` assumption for this to be sensible,
since, if `I` is an infinite identity matrix and `1` means the all-ones vector, then `[I | 1]`
represents a free matroid in which `I` doesn't correspond to a base. -/
@[mk_iff]
structure Rep.IsStandard (v : M.Rep 𝔽 γ) : Prop where
  apply_eq : ∀ x : B, v x.1 x = 1
  apply_ne : ∀ ⦃x y : B⦄, x ≠ y → v x.1 y = 0

lemma Rep.standardRep'_isStandard (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep' hB).IsStandard := by
  simp only [standardRep', FullRank.basis_of_isBase, isStandard_iff, compEquiv_apply,
    restrict_span_apply, rangeFactorization, inclusion_mk, Basis.mkImage_repr, ne_eq]
  refine ⟨fun e ↦ ?_, fun e f hne ↦ ?_⟩
  · rw [LinearIndependent.repr_eq_single, single_eq_same]
    rfl
  rw [LinearIndependent.repr_eq_single, single_eq_of_ne hne]
  rfl

end IsStandard


/-- A `Representable` matroid is one that has a representation over `𝔽`.
To avoid quantifying over types, we require that the representation is over the module `α → 𝔽`.
`Rep.Representable`, which is defined later, makes this definition useful.  -/
def Representable (M : Matroid α) (𝔽 : Type) [Semiring 𝔽] : Prop :=
  Nonempty (M.Rep 𝔽 (α → 𝔽))

lemma Representable.exists_isStandard_rep (hM : M.Representable 𝔽) (hB : M.IsBase B) :
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.IsStandard :=
  ⟨hM.some.standardRep' hB, Rep.standardRep'_isStandard (Nonempty.some hM) hB⟩
