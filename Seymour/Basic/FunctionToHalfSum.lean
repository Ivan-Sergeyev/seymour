import Seymour.Basic.Basic


variable {β₁ β₂ : Type}

lemma sum_ne_inl {x : β₁ ⊕ β₂} (hx₁ : ∀ b₁ : β₁, x ≠ ◩b₁) : ∃ b₂ : β₂, x = ◪b₂ := by
  cases hx : x with
  | inl =>
    exfalso
    apply hx₁
    exact hx
  | inr a =>
    use a

variable {α : Type}

lemma fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) : ∀ a : α, ∃ b₂ : β₂, f a = ◪b₂ :=
  (sum_ne_inl <| hf ·)

/-- Assume `f : α → β₁ ⊕ β₂` never reaches `β₁` values. We convert `f` to `α → β₂` function. -/
noncomputable def fn_of_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) : α → β₂ :=
  (fn_sum_ne_inl hf · |>.choose)

lemma eq_of_fn_sum_ne_inl {f : α → β₁ ⊕ β₂} (hf : ∀ a : α, ∀ b₁ : β₁, f a ≠ ◩b₁) (i : α) :
    f i = ◪(fn_of_sum_ne_inl hf i) :=
  (fn_sum_ne_inl hf i).choose_spec
