import Seymour.Matroid.Classes.Regular
import Seymour.Matroid.Operations.SumDelta.SpecialCase1Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase2Sum
import Seymour.Matroid.Operations.SumDelta.SpecialCase3Sum
import Seymour.Matroid.Operations.Sum1regularity
import Seymour.Matroid.Operations.Sum2.Regularity

/-!
This file states the "easy" (composition) direction of the Seymour decomposition theorem.
-/

variable {α : Type}

theorem easySeymour.Sum1 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular) (hMM : M₁.E ⫗ M₂.E)
    [∀ a : α, Decidable (a ∈ M₁.E)] [∀ a : α, Decidable (a ∈ M₂.E)] :
    (Matroid.disjointSum M₁ M₂ hMM).IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, hM₁⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, hM₂⟩ := hM₂ F hF
  have hE₁ : M₁.E = E₁ := by rw [←hM₁, VectorMatroid.toMatroid_E]
  have hE₂ : M₂.E = E₂ := by rw [←hM₂, VectorMatroid.toMatroid_E]
  have hMA₁ : M₁.IsRepresentedBy (hE₁ ▸ A₁) := hE₁ ▸ hM₁.symm
  have hMA₂ : M₂.IsRepresentedBy (hE₂ ▸ A₂) := hE₂ ▸ hM₂.symm
  exact ⟨_, (Matroid.disjointSum.ofRepresented_repr hMM hMA₁ hMA₂).symm⟩

theorem easySeymour.Sum2 {M₁ M₂ : Matroid α} (hM₁ : M₁.IsRegular) (hM₂ : M₂.IsRegular)
    (assumptions : TwoSumAssumptions M₁ M₂) :
    assumptions.build2sum.IsRegular := by
  apply Matroid2sum_isRegular_isRegular
  convert hM₁
  convert hM₂

theorem easySeymour.Sum3 [DecidableEq α] {M₁ M₂ : BinaryMatroid α}
    (hM₁ : M₁.toMatroid.IsRegular) (hM₂ : M₂.toMatroid.IsRegular)
    (assumptions : ThreeSumAssumptions M₁ M₂) :
    (BinaryMatroid.DeltaSum.toMatroid M₁ M₂).IsRegular := by
  intro F hF
  obtain ⟨⟨X₁, E₁, A₁⟩, hA₁⟩ := hM₁ F hF
  obtain ⟨⟨X₂, E₂, A₂⟩, hA₂⟩ := hM₂ F hF
  sorry
