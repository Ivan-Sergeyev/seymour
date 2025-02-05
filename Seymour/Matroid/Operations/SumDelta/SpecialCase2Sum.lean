import Seymour.Matroid.Operations.Sum2.Basic
import Seymour.Matroid.Operations.SumDelta.CircuitForms


variable {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}


section CircuitFormsProperties

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma DeltaSumCircuitForm1.sum2_circuit_pred {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    DeltaSumCircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    replace ⟨hC, _⟩ := hC
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    cases hX₂.dep_or_empty with
    | inl X₂_dep =>
      have X₂_eq : X₂ = M₁.E ∩ M₂.E :=
        have symDiff_sub_E₁ := symmDiff_eq_alt X₁ X₂ ▸ hXX ▸ hCC'.trans hC.subset_ground
        have X₂_sub_E₁ := M₁.toMatroid_E ▸ symmDiff_subset_ground_right symDiff_sub_E₁ hX₁.subset_ground
        have X₂_sub_inter := Set.subset_inter X₂_sub_E₁ X₂_dep.subset_ground
        have inter_finite := Set.finite_of_encard_eq_coe assumptions.interSingleton
        have inter_encard_le_X₂_encard := le_of_eq_of_le assumptions.interSingleton
          (Set.one_le_encard_iff_nonempty.← X₂_dep.nonempty)
        inter_finite.eq_of_subset_of_encard_le X₂_sub_inter inter_encard_le_X₂_encard
      have ⟨p, hp⟩ := assumptions.inter_singleton
      have M₂_loop_p : M₂.toMatroid.Loop p := ⟨singleton_inter_in_right hp, hp ▸ X₂_eq ▸ X₂_dep⟩
      exfalso
      exact assumptions.inter_singleton_not_loop_M₂ hp M₂_loop_p
    | inr X₂_empty =>
      rw [X₂_empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hXX
      rw [hXX] at hCC' C'_nonempty ⊢
      have X₁_dep := hX₁.nonempty_dep C'_nonempty
      exact hC.right X₁_dep hCC'

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma DeltaSumCircuitForm2.sum2_circuit_pred {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    DeltaSumCircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    replace ⟨hC, _⟩ := hC
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    cases hX₁.dep_or_empty with
    | inl X₁_dep =>
      have X₁_eq : X₁ = M₁.E ∩ M₂.E :=
        have symDiff_sub_E₂ := symmDiff_eq_alt X₁ X₂ ▸ hXX ▸ hCC'.trans hC.subset_ground
        have X₁_sub_E₂ := M₂.toMatroid_E ▸ symmDiff_subset_ground_left symDiff_sub_E₂ hX₂.subset_ground
        have hX₁sub_inter := Set.subset_inter X₁_dep.subset_ground X₁_sub_E₂
        have inter_finite := Set.finite_of_encard_eq_coe assumptions.interSingleton
        have inter_encard_le_X₁_encard := le_of_eq_of_le assumptions.interSingleton
          (Set.one_le_encard_iff_nonempty.← X₁_dep.nonempty)
        inter_finite.eq_of_subset_of_encard_le hX₁sub_inter inter_encard_le_X₁_encard
      obtain ⟨p, hp⟩ := assumptions.inter_singleton
      have M₁_loop_p : M₁.toMatroid.Loop p := ⟨singleton_inter_in_left hp, hp ▸ X₁_eq ▸ X₁_dep⟩
      exfalso
      exact assumptions.inter_singleton_not_loop_M₁ hp M₁_loop_p
    | inr X₁_empty =>
      rw [X₁_empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hXX
      rw [hXX] at hCC' C'_nonempty ⊢
      have X₂_dep := hX₂.nonempty_dep C'_nonempty
      exact hC.right X₂_dep hCC'

omit [DecidableEq α] in
/-- Under 2-sum assumptions, `{p}` in definition of circuits of form 3 is exactly `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm3.sum2_singleton_eq {C : Set α} {p : α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    M₁.E ∩ M₂.E = {p} := by
  have inter_encard_eq_1 := M₁.toMatroid_E ▸ M₂.toMatroid_E ▸ assumptions.interSingleton
  have inter_finite := Set.finite_of_encard_eq_coe inter_encard_eq_1
  have inter_subsingleton_encard := ((Set.encard_singleton p).symm ▸ inter_encard_eq_1).le
  exact (inter_finite.eq_of_subset_of_encard_le hC.singleton_subset_inter inter_subsingleton_encard).symm

/-- Circuit of form 3 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma DeltaSumCircuitForm3.sum2_circuit_pred {C : Set α} {p : α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    DeltaSumCircuitPred M₁ M₂ C := by
  have hp := hC.sum2_singleton_eq assumptions
  have not_loop_p := (assumptions.inter_singleton_not_loop_M₁ hp)
  rw [M₁.toMatroid.loop_iff_circuit] at not_loop_p
  apply hC.inter_M₁_nonempty at not_loop_p
  apply Set.Nonempty.left at not_loop_p
  constructor
  · exact hC.circuit_form not_loop_p
  · intro D hD hDC
    have ⟨D_nonempty, hDE, X₁, X₂, hDXX, hX₁, hX₂⟩ := hD
    have ⟨hCpM₁, hCpM₂, hCE⟩ := hC
    have hXX := Set.inter_subset_inter hX₁.subset_ground hX₂.subset_ground
    erw [M₁.toMatroid_E, M₂.toMatroid_E, hp] at hXX
    have hCX₁ : X₁ ⊆ C ∩ M₁.E ∪ {p}
    · rw [(Set.diff_union_inter X₁ X₂).symm]
      rw [←symmDiff_eq_alt, symmDiff_def] at hDXX
      simp only [Set.sup_eq_union] at hDXX
      have hXXC := (hDXX ▸ Set.subset_union_left).trans hDC
      have hXXE := Set.diff_subset_iff.← (Set.subset_union_of_subset_right hX₁.subset_ground X₂)
      have hXXCE := Set.subset_inter hXXC hXXE
      exact Set.union_subset_union hXXCE hXX
    have hCX₂ : X₂ ⊆ C ∩ M₂.E ∪ {p}
    · rw [(Set.diff_union_inter X₂ X₁).symm]
      rw [←symmDiff_eq_alt, symmDiff_def] at hDXX
      simp only [Set.sup_eq_union] at hDXX
      have hXXC := (hDXX ▸ Set.subset_union_right).trans hDC
      have hXXE := Set.diff_subset_iff.← (Set.subset_union_of_subset_right hX₂.subset_ground X₁)
      have hXXCE := Set.subset_inter hXXC hXXE
      exact Set.union_subset_union hXXCE (Set.inter_comm X₁ X₂ ▸ hXX)
    cases hX₁.dep_or_empty with
    | inl X₁_dep =>
      replace hCX₁ := hCpM₁.right X₁_dep hCX₁
      cases hX₂.dep_or_empty with
      | inl X₂_dep =>
        replace hCX₂ := hCpM₂.right X₂_dep hCX₂
        have hXXp : X₁ ∩ X₂ = {p} :=
          hXX.antisymm (Set.subset_inter (Set.union_subset_iff.→ hCX₁).right (Set.union_subset_iff.→ hCX₂).right)
        have hCD : (C ∩ M₁.E ∪ {p} ∪ (C ∩ M₂.E ∪ {p})) \ {p} ⊆ (X₁ ∪ X₂) \ {p} :=
          Set.diff_subset_diff_left (Set.union_subset_union hCX₁ hCX₂)
        rwa [Set.union_diff_distrib, Set.union_diff_right, Set.union_diff_right,
            Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₁_inter),
            Disjoint.sdiff_eq_left (hp ▸ hC.disjoint_inter_M₂_inter),
            hC.subset_union.parts_eq, ←hXXp, ←hDXX
        ] at hCD
      | inr X₂_empty =>
        rw [X₂_empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hDXX
        rw [hDXX] at D_nonempty
        have hpX₁ := hDXX ▸ (Set.union_subset_iff.→ hCX₁).right
        have disjoint_D_p := hp ▸ Set.disjoint_of_subset_left hDE Set.disjoint_sdiff_left
        exact (disjoint_D_p hpX₁ Set.Subset.rfl rfl).elim
    | inr X₁_empty =>
      rw [X₁_empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hDXX
      have X₂_dep := hX₂.nonempty_dep (hDXX ▸ D_nonempty)
      have hCX₂ := hCpM₂.right X₂_dep hCX₂
      have hpX₂ := hDXX ▸ (Set.union_subset_iff.→ hCX₂).right
      have disjoint_D_p := hp ▸ Set.disjoint_of_subset_left hDE Set.disjoint_sdiff_left
      exact (disjoint_D_p hpX₂ Set.Subset.rfl rfl).elim

end CircuitFormsProperties


section SpecialCase2sum

/-- If `M₁` and `M₂` satisfy the 2-sum assumptions, then `M₁ Δ M₂ = M₁ ⊕₂ M₂` -/
lemma TwoSumAssumptions.build2sum_eq_deltaSumMatroid
    (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    assumptions.build2sum = deltaSumMatroid M₁ M₂ := by
  apply Matroid.ext_circuit (by rfl)
  intro C hCE
  rw [assumptions.build2sum_circuit, deltaSumCircuitMatroid_circuit_iff]
  unfold twoSumGround
  rw [assumptions.build2sum_E] at hCE
  rw [VectorMatroid.toMatroid_E, VectorMatroid.toMatroid_E] at hCE ⊢
  constructor
  · intro ⟨_, hC⟩
    cases hC with
    | inl hC =>
      have hhC : DeltaSumCircuitForm1 M₁ M₂ C := hC
      exact hhC.sum2_circuit_pred assumptions
    | inr hC => cases hC with
      | inl hC =>
        have hhC : DeltaSumCircuitForm2 M₁ M₂ C := hC
        exact hhC.sum2_circuit_pred assumptions
      | inr hC =>
        obtain ⟨p, hp⟩ := assumptions.inter_singleton
        have hMMCp : DeltaSumCircuitForm3 M₁ M₂ C p := ⟨
          hp ▸ hC.to_circuit_M₁,
          hp ▸ hC.to_circuit_M₂,
          hCE⟩
        exact hMMCp.sum2_circuit_pred assumptions
  · intro hC
    constructor
    · exact hCE
    · have ⟨⟨_, _, X₁, X₂, hCXX, hX₁, hX₂⟩, C_min⟩ := hC
      if is_X₂_empty : X₂ = ∅ then
        left
        rw [is_X₂_empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hCXX
        exact ⟨hC.udc_M₁ (hCXX ▸ hX₁), (Set.subset_diff.→ hCE).right⟩
      else
        right
        if is_X₁_empty : X₁ = ∅ then
          left
          rw [is_X₁_empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hCXX
          exact ⟨hC.udc_M₂ (hCXX ▸ hX₂), (Set.subset_diff.→ hCE).right⟩
        else
          right
          apply Set.nonempty_iff_ne_empty.← at is_X₁_empty
          apply Set.nonempty_iff_ne_empty.← at is_X₂_empty
          have X₁_dep := hX₁.nonempty_dep is_X₁_empty
          have X₂_dep := hX₂.nonempty_dep is_X₂_empty
          obtain ⟨p, hp⟩ := M₁.toMatroid_E ▸ M₂.toMatroid_E ▸ assumptions.inter_singleton
          have hXXp := hp ▸ Set.inter_subset_inter hX₁.subset_ground hX₂.subset_ground
          have hpX₁ : {p} ⊆ X₁
          · by_contra p_notin_X₁
            rw [Set.singleton_subset_iff] at p_notin_X₁
            have disjoint_X₁_p : X₁ ⫗ {p} := Set.disjoint_singleton_right.← p_notin_X₁
            have p_notin_inter : p ∉ X₁ ∩ X₂ := (p_notin_X₁ <| Set.mem_of_mem_inter_left ·)
            have inter_neq_p : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl p_notin_inter).symm
            have hXX : X₁ ∩ X₂ = ∅
            · by_contra contr
              exact (Set.subset_singleton_iff_eq.→ hXXp).casesOn contr inter_neq_p
            have disjoint_X₁_inter : X₁ ⫗ M₁.E ∩ M₂.E := hp ▸ disjoint_X₁_p
            have X₁_sub_C : X₁ ⊆ C := (Set.diff_empty ▸ hXX ▸ hCXX) ▸ Set.subset_union_left
            obtain ⟨-, Y₁, hY₁, Y₁_sub_X₁⟩ := M₁.toMatroid.dep_iff_has_circuit.→ X₁_dep
            have disjoint_Y₁_inter := Set.disjoint_of_subset_left Y₁_sub_X₁ disjoint_X₁_inter
            have hMMY₁ : DeltaSumCircuitForm1 M₁ M₂ Y₁ := ⟨hY₁, disjoint_Y₁_inter⟩
            specialize C_min hMMY₁.circuit_form (Y₁_sub_X₁.trans X₁_sub_C)
            have C_eq_X₁ : C = X₁ := Set.Subset.antisymm (C_min.trans Y₁_sub_X₁) X₁_sub_C
            have C_eq_union := Set.diff_empty ▸ hXX ▸ hCXX
            replace hXX : X₁ ⫗ X₂ := Set.disjoint_iff_inter_eq_empty.← hXX
            rw [C_eq_X₁] at C_eq_union
            have X₂_empty := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.→ C_eq_union.symm)).→ hXX.symm
            exact Set.not_nonempty_empty (X₂_empty ▸ is_X₂_empty)
          have hpX₂ : {p} ⊆ X₂
          · by_contra p_notin_X₂
            rw [Set.singleton_subset_iff] at p_notin_X₂
            have disjoint_X₂_p : X₂ ⫗ {p} := Set.disjoint_singleton_right.← p_notin_X₂
            have p_notin_inter : p ∉ X₁ ∩ X₂ := (p_notin_X₂ <| Set.mem_of_mem_inter_right ·)
            have inter_neq_p : X₁ ∩ X₂ ≠ {p} := (ne_of_mem_of_not_mem' rfl p_notin_inter).symm
            have hXX : X₁ ∩ X₂ = ∅
            · by_contra contr
              exact (Set.subset_singleton_iff_eq.→ hXXp).casesOn contr inter_neq_p
            have disjoint_X₂_inter : X₂ ⫗ M₁.E ∩ M₂.E := hp ▸ disjoint_X₂_p
            have X₂_sub_C : X₂ ⊆ C := (Set.diff_empty ▸ hXX ▸ hCXX) ▸ Set.subset_union_right
            obtain ⟨-, Y₂, hY₂, hY₂X₂⟩ := M₂.toMatroid.dep_iff_has_circuit.→ X₂_dep
            have disjoint_Y₂_inter := Set.disjoint_of_subset_left hY₂X₂ disjoint_X₂_inter
            have hMMY₂ : DeltaSumCircuitForm2 M₁ M₂ Y₂ := ⟨hY₂, disjoint_Y₂_inter⟩
            specialize C_min hMMY₂.circuit_form (hY₂X₂.trans X₂_sub_C)
            have C_eq_X₂ : C = X₂ := Set.Subset.antisymm (C_min.trans hY₂X₂) X₂_sub_C
            have C_eq_union := Set.diff_empty ▸ hXX ▸ hCXX
            rw [C_eq_X₂, Set.union_comm] at C_eq_union
            replace hXX : X₁ ⫗ X₂ := Set.disjoint_iff_inter_eq_empty.← hXX
            have X₁_empty := (Set.disjoint_of_subset_iff_left_eq_empty (Set.union_eq_left.→ C_eq_union.symm)).→ hXX
            exact Set.not_nonempty_empty (X₁_empty ▸ is_X₁_empty)
          have inter_eq_p : X₁ ∩ X₂ = {p} := Set.Subset.antisymm hXXp (Set.subset_inter hpX₁ hpX₂)
          have hCEpX₁ : C ∩ M₁.E ∪ {p} = X₁
          · rw [inter_eq_p] at hCXX
            have hCpXXpp : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congrFun (congrArg Union.union hCXX) {p}
            rw [Set.diff_union_self] at hCpXXpp
            have hpXX : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
            rw [Set.union_eq_left.← hpXX] at hCpXXpp
            have hCpEXXE₁ : (C ∪ {p}) ∩ M₁.E = (X₁ ∪ X₂) ∩ M₁.E := congrFun (congrArg Inter.inter hCpXXpp) M₁.E
            have hXXEXEXE₁ : (X₁ ∪ X₂) ∩ M₁.E = X₁ ∩ M₁.E ∪ X₂ ∩ M₁.E := Set.union_inter_distrib_right X₁ X₂ M₁.E
            have eq_X₁ : X₁ ∩ M₁.E = X₁ := (Set.left_eq_inter.← hX₁.subset_ground).symm
            have inter_sub_inter₂ : X₂ ∩ M₁.E ⊆ M₂.E ∩ M₁.E := Set.inter_subset_inter_left M₁.E hX₂.subset_ground
            have inter_sub_inter' := (Set.inter_comm M₁.E M₂.E) ▸ inter_sub_inter₂
            have inter_sub_X₁ : M₁.E ∩ M₂.E ⊆ X₁ := hp ▸ hpX₁
            have sub_X₁ : X₂ ∩ M₁.E ⊆ X₁ := inter_sub_inter'.trans inter_sub_X₁
            have union_inter_eq_X₁ : X₁ ∪ X₂ ∩ M₁.E = X₁ := Set.union_eq_self_of_subset_right sub_X₁
            have hCpE₁ : (C ∪ {p}) ∩ M₁.E = C ∩ M₁.E ∪ {p} ∩ M₁.E := Set.union_inter_distrib_right C {p} M₁.E
            have p_sub_E₁ : {p} ⊆ M₁.E := singleton_inter_subset_left hp
            have p_inter : {p} ∩ M₁.E = {p} := (Set.left_eq_inter.← p_sub_E₁).symm
            rw [p_inter] at hCpE₁
            rw [←hCpE₁, hCpEXXE₁, hXXEXEXE₁, eq_X₁, union_inter_eq_X₁]
          have hCEpX₂ : C ∩ M₂.E ∪ {p} = X₂
          · rw [inter_eq_p] at hCXX
            have hCpXXpp : C ∪ {p} = (X₁ ∪ X₂) \ {p} ∪ {p} := congr_fun (congr_arg Union.union hCXX) {p}
            -- todo : use Set.diff_union_of_subset
            rw [Set.diff_union_self] at hCpXXpp
            have hpXX : {p} ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right hpX₂ X₁
            rw [Set.union_eq_left.← hpXX] at hCpXXpp
            have hCpEXXE₂ : (C ∪ {p}) ∩ M₂.E = (X₁ ∪ X₂) ∩ M₂.E := congr_fun (congr_arg Inter.inter hCpXXpp) M₂.E
            have hXXEXEXE₂ : (X₁ ∪ X₂) ∩ M₂.E = X₁ ∩ M₂.E ∪ X₂ ∩ M₂.E := Set.union_inter_distrib_right X₁ X₂ M₂.E
            have eq_X₂ : X₂ ∩ M₂.E = X₂ := (Set.left_eq_inter.← hX₂.subset_ground).symm
            have inter_sub_inter₁ : X₁ ∩ M₂.E ⊆ M₁.E ∩ M₂.E := Set.inter_subset_inter_left M₂.E hX₁.subset_ground
            have inter_sub_X₂ : M₁.E ∩ M₂.E ⊆ X₂ := hp ▸ hpX₂
            have sub_X₂ : X₁ ∩ M₂.E ⊆ X₂ := inter_sub_inter₁.trans inter_sub_X₂
            have union_inter_eq_X₂ : X₁ ∩ M₂.E ∪ X₂ = X₂ := Set.union_eq_self_of_subset_left sub_X₂
            have hCpE₂ : (C ∪ {p}) ∩ M₂.E = C ∩ M₂.E ∪ {p} ∩ M₂.E := Set.union_inter_distrib_right C {p} M₂.E
            have p_sub_E₂ : {p} ⊆ M₂.E := singleton_inter_subset_right hp
            have p_inter : {p} ∩ M₂.E = {p} := (Set.left_eq_inter.← p_sub_E₂).symm
            rw [p_inter] at hCpE₂
            rw [←hCpE₂, hCpEXXE₂, hXXEXEXE₂, eq_X₂, union_inter_eq_X₂]
          -- todo: make lemma in Sum2
          have M₁_noncirc_p : ¬(M₁.toMatroid.Circuit {p})
          · intro M₁_circ_p
            exact assumptions.inter_singleton_not_loop_M₁ hp ((M₁.toMatroid.loop_iff_circuit ).← M₁_circ_p)
          -- todo: make lemma in Sum2
          have M₂_noncirc_p : ¬(M₂.toMatroid.Circuit {p})
          · intro M₂_circ_p
            exact assumptions.inter_singleton_not_loop_M₂ hp ((M₂.toMatroid.loop_iff_circuit ).← M₂_circ_p)
          have not_X₁_sub_p : ¬(X₁ ⊆ {p})
          · intro X₁_sub_p
            have M₁_circ_p : M₁.toMatroid.Circuit {p} := ⟨
              X₁_dep.superset X₁_sub_p (singleton_inter_subset_left hp),
              fun Q hQ hQp => by
                simp only [Set.le_eq_subset] at hQp
                rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                exact le_of_eq_of_le hQp.symm (by rfl)⟩
            exact M₁_noncirc_p M₁_circ_p
          have not_X₂_sub_p : ¬(X₂ ⊆ {p})
          · intro X₂_sub_p
            have M₂_circ_p : M₂.toMatroid.Circuit {p} := ⟨
              X₂_dep.superset X₂_sub_p (singleton_inter_subset_right hp),
              fun Q hQ hQp => by
                simp only [Set.le_eq_subset] at hQp
                rw [Set.Nonempty.subset_singleton_iff hQ.nonempty] at hQp
                exact le_of_eq_of_le hQp.symm (by rfl)⟩
            exact M₂_noncirc_p M₂_circ_p
          have disjoint_X₁_wo_p_X₂_wo_p : X₁ \ {p} ⫗ X₂ \ {p} := disjoint_of_singleton_inter_both_wo inter_eq_p
          have C_inter_E₁_nonempty : (C ∩ M₁.E).Nonempty
          · rw [hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_inter_distrib_right]
            rw [←Set.diff_nonempty] at not_X₁_sub_p
            have X₁_sub_E₁ : X₁ ⊆ M₁.E := X₁_dep.subset_ground
            have sub_E₁ : X₁ \ {p} ⊆ M₁.E := diff_subset_parent X₁_sub_E₁
            exact (Set.left_eq_inter.← sub_E₁ ▸ not_X₁_sub_p).inl
          have C_inter_E₂_nonempty : (C ∩ M₂.E).Nonempty
          · rw [hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_inter_distrib_right]
            rw [←Set.diff_nonempty] at not_X₂_sub_p
            have X₂_sub_E₂ : X₂ ⊆ M₂.E := X₂_dep.subset_ground
            have sub_E₂ : X₂ \ {p} ⊆ M₂.E := diff_subset_parent X₂_sub_E₂
            exact (Set.left_eq_inter.← sub_E₂ ▸ not_X₂_sub_p).inr
          have M₁_circ_X₁ : M₁.toMatroid.Circuit X₁
          · constructor
            · exact X₁_dep
            · intro Y₁ hY₁ Y₁_sub_X₁
              obtain ⟨-, Z₁, hZ₁, Z₁_sub_Y₁⟩ := M₁.toMatroid.dep_iff_has_circuit.→ hY₁
              have Z₁_sub_X₁ : Z₁ ⊆ X₁ := Z₁_sub_Y₁.trans Y₁_sub_X₁
              if p_sub_Z₁ : {p} ⊆ Z₁ then
                have hpZ₁X₂ : Z₁ ∩ X₂ = {p}
                · apply ((Set.inter_subset_inter_left X₂ Z₁_sub_X₁).trans inter_eq_p.subset).antisymm
                  exact Set.subset_inter p_sub_Z₁ hpX₂
                have hZ₁dp : (Z₁ \ {p}).Nonempty
                · by_contra! hZ₁dp
                  have hZ₁eqp : Z₁ = {p} := (Set.diff_eq_empty.→ hZ₁dp).antisymm p_sub_Z₁
                  exact M₁_noncirc_p (hZ₁eqp ▸ hZ₁)
                have sub_C : ((Z₁ ∪ X₂) \ (Z₁ ∩ X₂)) ⊆ C
                · rw [hpZ₁X₂, hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_diff_distrib]
                  exact Set.union_subset_union (Set.diff_subset_diff_left Z₁_sub_X₁) (by rfl)
                have circuitform_Z₁ : DeltaSumCircuitForm M₁ M₂ ((Z₁ ∪ X₂) \ (Z₁ ∩ X₂))
                · constructor
                  · rw [hpZ₁X₂, Set.union_diff_distrib]
                    exact Set.Nonempty.inl hZ₁dp
                  exact ⟨sub_C.trans hCE, Z₁, X₂, rfl, hZ₁.isUnionDisjointCircuits, hX₂⟩
                specialize C_min circuitform_Z₁ sub_C
                have X₁_sub_Z₁ : X₁ ⊆ Z₁
                · rw [hpZ₁X₂, hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_diff_distrib] at C_min
                  simp only [Set.le_eq_subset] at C_min
                  have hX₁union := (Set.union_subset_iff.→ C_min).left
                  have hX₁Z₁dp : X₁ \ {p} ⊆ Z₁ \ {p} :=
                    Disjoint.subset_left_of_subset_union hX₁union disjoint_X₁_wo_p_X₂_wo_p
                  rw [Set.diff_subset_iff, Set.union_comm, Set.diff_union_of_subset p_sub_Z₁] at hX₁Z₁dp
                  exact hX₁Z₁dp
                exact X₁_sub_Z₁.trans Z₁_sub_Y₁
              else
                rw [Set.singleton_subset_iff] at p_sub_Z₁
                have Z₁_disjoint_p : Z₁ ⫗ {p} := Set.disjoint_singleton_right.← p_sub_Z₁
                have hMMZ₁ : DeltaSumCircuitForm1 M₁ M₂ Z₁ := ⟨hZ₁, hp ▸ Z₁_disjoint_p⟩
                have Z₁_sub_C : Z₁ ⊆ C
                · have hZ₁X₁X₂ : Z₁ ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_left Z₁_sub_X₁ X₂
                  have hZ₁X₁X₂p : Z₁ ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hZ₁X₁X₂ p_sub_Z₁
                  exact hCXX ▸ inter_eq_p ▸ hZ₁X₁X₂p
                specialize C_min hMMZ₁.circuit_form Z₁_sub_C
                have C_eq_Z₁ := C_min.antisymm Z₁_sub_C
                exact (Set.not_nonempty_empty (hMMZ₁.disjoint_M₂.inter_eq ▸ C_eq_Z₁ ▸ C_inter_E₂_nonempty)).elim
          have M₂_circ_X₂ : M₂.toMatroid.Circuit X₂
          · constructor
            · exact X₂_dep
            · intro Y₂ hY₂ Y₂_sub_X₂
              obtain ⟨-, Z₂, hZ₂, Z₂_sub_Y₂⟩ := M₂.toMatroid.dep_iff_has_circuit.→ hY₂
              have Z₂_sub_X₂ : Z₂ ⊆ X₂ := Z₂_sub_Y₂.trans Y₂_sub_X₂
              if p_sub_Z₂ : {p} ⊆ Z₂ then
                have hpX₁Z₂ : X₁ ∩ Z₂ = {p}
                · apply ((Set.inter_subset_inter_right X₁ Z₂_sub_X₂).trans inter_eq_p.subset).antisymm
                  exact Set.subset_inter hpX₁ p_sub_Z₂
                have hZ₂dp : (Z₂ \ {p}).Nonempty
                · by_contra! hZ₂dp
                  have Z₂_eq_p : Z₂ = {p} := (Set.diff_eq_empty.→ hZ₂dp).antisymm p_sub_Z₂
                  exact M₂_noncirc_p (Z₂_eq_p ▸ hZ₂)
                have sub_C : ((X₁ ∪ Z₂) \ (X₁ ∩ Z₂)) ⊆ C
                · rw [hpX₁Z₂, hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_diff_distrib]
                  exact Set.union_subset_union (by rfl) (Set.diff_subset_diff_left Z₂_sub_X₂)
                have circuitform_Z₂ : DeltaSumCircuitForm M₁ M₂ ((X₁ ∪ Z₂) \ (X₁ ∩ Z₂))
                · constructor
                  · rw [hpX₁Z₂, Set.union_diff_distrib]
                    exact Set.Nonempty.inr hZ₂dp
                  exact ⟨sub_C.trans hCE, X₁, Z₂, rfl, hX₁, hZ₂.isUnionDisjointCircuits⟩
                specialize C_min circuitform_Z₂ sub_C
                have X₂_sub_Z₂ : X₂ ⊆ Z₂
                · rw [hpX₁Z₂, hCXX, inter_eq_p, Set.union_diff_distrib, Set.union_diff_distrib] at C_min
                  simp only [Set.le_eq_subset] at C_min
                  have hX₂union := (Set.union_subset_iff.→ C_min).right
                  have hX₂Z₂dp : X₂ \ {p} ⊆ Z₂ \ {p} :=
                    Disjoint.subset_right_of_subset_union hX₂union disjoint_X₁_wo_p_X₂_wo_p.symm
                  rw [Set.diff_subset_iff, Set.union_comm, Set.diff_union_of_subset p_sub_Z₂] at hX₂Z₂dp
                  exact hX₂Z₂dp
                exact X₂_sub_Z₂.trans Z₂_sub_Y₂
              else
                rw [Set.singleton_subset_iff] at p_sub_Z₂
                have Z₂_disjoint_p : Z₂ ⫗ {p} := Set.disjoint_singleton_right.← p_sub_Z₂
                have hMMZ₂ : DeltaSumCircuitForm2 M₁ M₂ Z₂ := ⟨hZ₂, hp ▸ Z₂_disjoint_p⟩
                have Z₂_sub_C : Z₂ ⊆ C
                · have hZ₂X₁X₂ : Z₂ ⊆ X₁ ∪ X₂ := Set.subset_union_of_subset_right Z₂_sub_X₂ X₁
                  have hZ₂X₁X₂p : Z₂ ⊆ (X₁ ∪ X₂) \ {p} := Set.subset_diff_singleton hZ₂X₁X₂ p_sub_Z₂
                  exact hCXX ▸ inter_eq_p ▸ hZ₂X₁X₂p
                specialize C_min hMMZ₂.circuit_form Z₂_sub_C
                have C_eq_Z₂ := Set.Subset.antisymm C_min Z₂_sub_C
                exact (Set.not_nonempty_empty (hMMZ₂.disjoint_M₁.inter_eq ▸ C_eq_Z₂ ▸ C_inter_E₁_nonempty)).elim
          exact ⟨hp ▸ hCEpX₁ ▸ M₁_circ_X₁, hp ▸ hCEpX₂ ▸ M₂_circ_X₂, hCE⟩

end SpecialCase2sum
