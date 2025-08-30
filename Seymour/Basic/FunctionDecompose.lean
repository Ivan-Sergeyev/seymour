import Seymour.Basic.Basic

/-!
# Function to Sum decomposition

Here we decompose a function of type `α → β₁ ⊕ β₂` into a function and two bijections: `α → α₁ ⊕ α₂ ≃ β₁ ⊕ β₂`
-/

variable {α β₁ β₂ : Type*}

/-- Given `f : α → β₁ ⊕ β₂` decompose `α` into two preïmages. -/
@[simp low]
def Function.decomposeSum (f : α → β₁ ⊕ β₂) :
    α ≃ { x₁ : α × β₁ // f x₁.fst = ◩x₁.snd } ⊕ { x₂ : α × β₂ // f x₂.fst = ◪x₂.snd } where
  toFun a :=
    match hfa : f a with
    | .inl b₁ => ◩⟨⟨a, b₁⟩, hfa⟩
    | .inr b₂ => ◪⟨⟨a, b₂⟩, hfa⟩
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

@[app_unexpander Function.decomposeSum]
def Function.decomposeSum_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f) => `($(f).$(Lean.mkIdent `decomposeSum))
  | _ => throw ()

@[simp ←]
lemma Function.eq_comp_decomposeSum (f : α → β₁ ⊕ β₂) :
    f = Sum.elim (Sum.inl ∘ (·.val.snd)) (Sum.inr ∘ (·.val.snd)) ∘ f.decomposeSum := by
  aesop

-- The rest of the file deals with the cardinality of the preïmages (assuming finitess).

noncomputable instance [Fintype α] {f : α → β₁ ⊕ β₂} : Fintype { x₁ : α × β₁ // f x₁.fst = ◩x₁.snd } := by
  apply Fintype.ofInjective (·.val.fst)
  intro ⟨⟨u, u₁⟩, hu⟩ ⟨⟨v, v₁⟩, hv⟩ huv
  dsimp only at hu hv huv
  rw [Subtype.mk_eq_mk, Prod.mk_inj]
  refine ⟨huv, ?_⟩
  rw [←Sum.inl.injEq, ←hu, ←hv, huv]

noncomputable instance [Fintype α] {f : α → β₁ ⊕ β₂} : Fintype { x₂ : α × β₂ // f x₂.fst = ◪x₂.snd } := by
  apply Fintype.ofInjective (·.val.fst)
  intro ⟨⟨u, u₁⟩, hu⟩ ⟨⟨v, v₁⟩, hv⟩ huv
  dsimp only at hu hv huv
  rw [Subtype.mk_eq_mk, Prod.mk_inj]
  refine ⟨huv, ?_⟩
  rw [←Sum.inr.injEq, ←hu, ←hv, huv]

lemma Function.decomposeSum_card_eq [Fintype α] (f : α → β₁ ⊕ β₂) :
    #{ x₁ : α × β₁ // f x₁.fst = ◩x₁.snd } + #{ x₂ : α × β₂ // f x₂.fst = ◪x₂.snd } = #α := by
  rw [←Fintype.card_sum]
  exact Fintype.card_congr f.decomposeSum.symm
