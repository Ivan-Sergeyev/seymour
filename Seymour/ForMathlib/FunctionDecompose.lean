import Mathlib.Tactic

/-!
# Function to Sum decomposition

Here we decompose a function `f : α → β₁ ⊕ β₂` into a function and two bijections: `α → α₁ ⊕ α₂ ≃ β₁ ⊕ β₂`
-/

variable {α β₁ β₂ : Type*}

/-- Given `f : α → β₁ ⊕ β₂` decompose `α` into two preïmages. -/
@[simp]
def Function.decomposeSum (f : α → β₁ ⊕ β₂) :
    α ≃ { x₁ : α × β₁ // f x₁.fst = Sum.inl x₁.snd } ⊕ { x₂ : α × β₂ // f x₂.fst = Sum.inr x₂.snd } where
  toFun a :=
    (match hfa : f a with
      | .inl b₁ => Sum.inl ⟨(a, b₁), hfa⟩
      | .inr b₂ => Sum.inr ⟨(a, b₂), hfa⟩
    )
  invFun x :=
    x.casesOn (·.val.fst) (·.val.fst)
  left_inv a := by
    cases f a with
    | inl => aesop
    | inr => aesop
  right_inv x := by
    cases x with
    | inl => aesop
    | inr => aesop

lemma Function.eq_comp_decomposeSum (f : α → β₁ ⊕ β₂) :
    f = Sum.elim (Sum.inl ∘ (·.val.snd)) (Sum.inr ∘ (·.val.snd)) ∘ f.decomposeSum := by
  aesop