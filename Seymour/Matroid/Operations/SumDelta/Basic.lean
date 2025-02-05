import Seymour.Matroid.Classes.Binary
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Notions.DisjointCircuitFamily


variable {α : Type}


section BasicDefinitions

/-- Circuits in `M₁ Δ M₂` are nonempty subsets of the ground set of form `X₁ Δ X₂`
    where `X₁` and `X₂` are disjoint unions of circuits in `M₁` and `M₂` respectively. -/
def DeltaSumCircuitsAux (M₁ M₂ : BinaryMatroid α) (C X₁ X₂ : Set α) : Prop :=
  C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) ∧ M₁.toMatroid.IsUnionDisjointCircuits X₁ ∧ M₂.toMatroid.IsUnionDisjointCircuits X₂

/-- A set satisfies circuit form if for some `X₁` and `X₂` it has the form above. -/
def DeltaSumCircuitForm (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  C.Nonempty ∧ C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) ∧ ∃ X₁ X₂ : Set α, DeltaSumCircuitsAux M₁ M₂ C X₁ X₂

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where `X₁` and `X₂` is a disjoint union of circuits of `M₁` and `M₂` respectively. -/
def DeltaSumCircuitPred (M₁ M₂ : BinaryMatroid α) : CircuitPredicate α :=
  Minimal (DeltaSumCircuitForm M₁ M₂)

end BasicDefinitions


section BasicProperties

/-- A set of circuit form is nonempty. -/
lemma deltaSumCircuitForm.nonempty {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm M₁ M₂ C) :
    C.Nonempty :=
  hC.left

/-- A set of circuit form is a subset of the ground set. -/
lemma DeltaSumCircuitForm.subset_ground {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm M₁ M₂ C) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  hC.right.left

/-- A set of circuit form is the symmetric difference of `X₁` and `X₂` -/
lemma DeltaSumCircuitsAux.eq_symmDiff {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) :=
  hC.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₁` -/
lemma DeltaSumCircuitsAux.udc_left {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    M₁.toMatroid.IsUnionDisjointCircuits X₁ :=
  hC.right.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₂` -/
lemma DeltaSumCircuitsAux.udc_right {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    M₂.toMatroid.IsUnionDisjointCircuits X₂ :=
  hC.right.right

end BasicProperties


section CircuitAxioms

/-- In circuit construction of Δ-sum, empty set is not circuit -/
lemma deltaSumCircuitPred_not_circuit_empty (M₁ M₂ : BinaryMatroid α) :
    ¬DeltaSumCircuitPred M₁ M₂ ∅ := by
  simp only [DeltaSumCircuitPred, Minimal, DeltaSumCircuitForm, DeltaSumCircuitsAux,
    Set.not_nonempty_empty, Set.empty_subset, Set.le_eq_subset, Set.subset_empty_iff,
    true_and, false_and, exists_const, exists_and_left, implies_true, and_true, not_false_eq_true]

/-- In circuit construction of Δ-sum, no circuit is strict subset of another circuit -/
lemma deltaSumCircuitPred_circuitNotSsubset (M₁ M₂ : BinaryMatroid α) :
    (DeltaSumCircuitPred M₁ M₂).CircuitNotSsubset := by
  intro C C' hC hC'
  sorry

/-- In circuit construction of Δ-sum, circuit predicate satisfies axiom (C3) -/
lemma deltaSumCircuitPred_bruhnC3 (M₁ M₂ : BinaryMatroid α) :
    (DeltaSumCircuitPred M₁ M₂).BruhnC3 := by
  intro X C F z hz
  sorry

/-- In circuit construction of Δ-sum, set of all circuit-independent sets has the maximal subset prop -/
lemma deltaSumCircuitPred_circuitMaximal (M₁ M₂ : BinaryMatroid α) :
    (DeltaSumCircuitPred M₁ M₂).CircuitMaximal ((M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)) := by
  intro X hXE
  sorry

/-- In circuit construction of Δ-sum, every circuit is subset of ground set -/
lemma DeltaSumCircuitPred.subset_ground {M₁ M₂ : BinaryMatroid α} (C : Set α)
    (hC : DeltaSumCircuitPred M₁ M₂ C) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  hC.left.right.left

end CircuitAxioms


section API

/-- Construction of Δ-sum via circuits -/
def deltaSumCircuitMatroid (M₁ M₂ : BinaryMatroid α) : CircuitMatroid α where
  E := (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)
  CircuitPred := Minimal (DeltaSumCircuitForm M₁ M₂)
  not_circuit_empty := deltaSumCircuitPred_not_circuit_empty M₁ M₂
  circuit_not_ssubset := deltaSumCircuitPred_circuitNotSsubset M₁ M₂
  circuit_c3 := deltaSumCircuitPred_bruhnC3 M₁ M₂
  circuit_maximal := deltaSumCircuitPred_circuitMaximal M₁ M₂
  subset_ground := DeltaSumCircuitPred.subset_ground

/-- Matroid corresponding to Δ-sum -/
def deltaSumMatroid (M₁ M₂ : BinaryMatroid α) : Matroid α :=
  (deltaSumCircuitMatroid M₁ M₂).toMatroid

@[simp]
lemma deltaSumMatroid_E (M₁ M₂ : BinaryMatroid α) :
    (deltaSumMatroid M₁ M₂).E = (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  rfl

@[simp]
lemma deltaSumCircuitMatroid_circuitPred (M₁ M₂ : BinaryMatroid α) :
    (deltaSumCircuitMatroid M₁ M₂).CircuitPred = DeltaSumCircuitPred M₁ M₂ :=
  rfl

@[simp]
lemma deltaSumCircuitMatroid_circuit_iff (M₁ M₂ : BinaryMatroid α) {C : Set α} :
    (deltaSumMatroid M₁ M₂).Circuit C ↔ DeltaSumCircuitPred M₁ M₂ C :=
  (deltaSumCircuitMatroid M₁ M₂).toMatroid_circuit_iff.trans ⟨And.right, fun hC => ⟨hC.subset_ground, hC⟩⟩

end API
