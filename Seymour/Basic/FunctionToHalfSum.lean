import Seymour.Basic.Basic

/-!
# Functions to "half" Sum

Here we study functions of type `α → β₁ ⊕ β₂` that happen to contain image in only one of the half of its codomain.
-/

variable {β₁ β₂ : Type*}

lemma sum_ne_inl {x : β₁ ⊕ β₂} (hx₁ : ∀ b₁ : β₁, x ≠ ◩b₁) : ∃ b₂ : β₂, x = ◪b₂ := by
  aesop

lemma sum_ne_inr {x : β₁ ⊕ β₂} (hx₂ : ∀ b₂ : β₂, x ≠ ◪b₂) : ∃ b₁ : β₁, x = ◩b₁ := by
  aesop

variable {α : Type*}

lemma fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) : ∀ a : α, ∃ b₂ : β₂, f a = ◪b₂ :=
  (sum_ne_inl <| hf ·)

lemma fn_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ ◪b₂) : ∀ a : α, ∃ b₁ : β₁, f a = ◩b₁ :=
  (sum_ne_inr <| hf ·)

/-- Assume `f : α → β₁ ⊕ β₂` never reaches `β₁` values. We convert `f` to `α → β₂` function. -/
noncomputable def fn_of_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) : α → β₂ :=
  (fn_sum_ne_inl hf · |>.choose)

/-- Assume `f : α → β₁ ⊕ β₂` never reaches `β₂` values. We convert `f` to `α → β₁` function. -/
noncomputable def fn_of_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ ◪b₂) : α → β₁ :=
  (fn_sum_ne_inr hf · |>.choose)

lemma eq_of_fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) (i : α) :
    f i = ◪(fn_of_sum_ne_inl hf i) :=
  (fn_sum_ne_inl hf i).choose_spec

lemma eq_of_fn_sum_ne_inr {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₂ : β₂, f a ≠ ◪b₂) (i : α) :
    f i = ◩(fn_of_sum_ne_inr hf i) :=
  (fn_sum_ne_inr hf i).choose_spec
