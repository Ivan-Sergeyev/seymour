# Contributing to Seymour

Thank you for your interest in contributing to Seymour!
We welcome all contributions from the community and appreciate your efforts to improve the project.

## Code style

If you contribute to the project, do not worry about code style too much;
none of the style rules is enforced by a linter;
we will accept your PR regardless of style;
Martin will eventually adjust it.
The guideline below is written primarily to assist you in reading the code.

### Global variables

- Implicit and typeclass arguments may be put after `variable` but explicit arguments may not be. Example and a non-example:

  `variable {R : Type} [R : Ring] (a : R)`

  While `{R : Type} [R : Ring]` in encouraged, the explicit argument `(a : R)` is not allowed to be a global variable.
  As a result, when you call a function or a lemma, you can be sure that all required arguments are visible at the lines of given function or lemma,
  which is very important.
- We use global variables sparingly — usually for arguments that are used by the entire file or section.

### Lines

- Lines should not be longer than 128 characters (see the vertical ruler in VS Code) unless the line contains a long URL.
- Starting a proof on a new line is recommended even in cases where the entire proof fits into the same line with the statement.
- When the header of a declaration does not fit into one line, it is recommended to start the part after `:` on a new line.
- Make 2 empty lines between imports and the content of the file (unless it has `/-! a top-level comment section -/` in which case 1 empty line goes above and 1 empty line goes below).
- Make 1 empty line between the start of a section and a declaration.
- Make 1 empty line between declarations of any kind.
- Make 1 empty line between a declaration and the end of a section.
- Make 2 empty lines between the end of a section and what follows.
- Each file ends with a linebreak.

### Indentation

- We use the same indentation as Mathlib.
  - Subitem: 2 spaces
  - Continuation of the same item after a linebreak: 4 spaces
- Deviations from the style are welcome if they hint some metaïnformation.

### Spaces

- There is always a space before a bracket (of any kind) opens and after it closes. Example:

  `foo {R : Type} [R : Ring] (a b : R) : ⟨a, b⟩ ∈ S`
- Space after a brace opens and before a brace closes is written only in the `Set` builder and in `Subtype` declarations. Examples:

  `{ x : X | ∃ y : Y, Bar x y }`

  `{ x₁ : α × β₁ // f x₁.fst = ◩x₁.snd }`

- With a comma, a space is written only after it, not before.
- With a colon, a space is written from both sides.

### Naming

#### Constants

- Use `camelCase` and `PascalCase` and `snake_case` the same way Mathlib uses them.
  - Constants that live in `Sort` (i.e., new `Type` and `Prop` declarations) are written in `PascalCase`
  - All other constants that live in `Type` (e.g. functions that return real numbers) are written in `camelCase`
  - Constants that live in `Prop` (i.e., theorems and lemmas) are written in `snake_case` whose constituents are other constants converted to `camelCase` and other standard tokens like `ext` or `cancel`
- We like to write `.` in the name of a constant if it facilitates the use of dot notation when calling it. Usually it means that the part of the name that comes before the last `.` is identical to the type of the first explicit argument.
  - In such a case, the parts before the last `.` are not converted to `camelCase`

#### Variables

- Data variables (both in arguments and local variables) are always denoted by a single letter, possibly with other stuff after it like lower index or apostrophe.
- Prop variables (both in arguments and local variables) are always denoted by multiple letters, possibly with other stuff after them like lower index or apostrophe.
  - Prefix `h` means "the statement is anything about the following variables"
  - Not starting with `h` means that the actual statement (or its substantial part) is spelled out, not only the variables that appear in it
  - We sometimes use the digit `9` to refer to the number `-1` in the names of Prop variables (only there; write `neg_one` in names of constants)
- Examples:

  `intro a b a_lt_b hab`
  - `a` carries data (e.g. an integer)
  - `b` carries data (e.g. an integer)
  - `a_lt_b` carries a proof of `a < b`
  - `hab` carries any information about `a` and `b`

  `intro x y x_eq_y h1 h1'`
  - `x` carries data (e.g. an integer)
  - `y` carries data (e.g. an integer)
  - `x_eq_y` carries a proof of `x = y`
  - `h1` carries any information involving the number `1`
  - `h1'` carries another information involving the number `1`

  `intro M hM hM'`
  - `M` carries data (e.g. a matroid)
  - `hM` carries any information about `M`
  - `hM'` carries another information about `M`

  `intro M M' hM hM'`
  - `M` carries data (e.g. a matroid)
  - `M'` carries data (e.g. a matroid)
  - `hM` carries any information about `M`
  - `hM'` carries any information about `M'`

  `intro M₁ M₂ hM₁ hM₂ hMM`
  - `M₁` carries data (e.g. a matroid)
  - `M₂` carries data (e.g. a matroid)
  - `hM₁` carries any information about `M₁`
  - `hM₂` carries any information about `M₂`
  - `hMM` carries any information about both `M₁` and `M₂` (indices after `hMM` are not needed)
- Never name anything `this` or standalone `h` (these names are acceptable neither for data nor for propositions), but leaving automatically named stuff with `this` or `h` is encouraged if the term is not explicitly referred to later.
  - Writing names like `h₁` or `h'` or `this'` or `this_` is strongly discouraged regardless of the purpose
- Real-life example (focus on the third line of each version – explicit arguments of the lemma):
  - Unacceptable argument names:
    ```lean
    lemma Multiset.sum_lt_sum {ι α : Type} [OrderedCancelAddCommMonoid α]
        {s : Multiset ι} {f g : ι → α}
        (h : ∀ i ∈ s, f i ≤ g i) (h' : ∃ i ∈ s, f i < g i) :
        (s.map f).sum < (s.map g).sum := by
      obtain ⟨l⟩ := s
      simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
      exact l.sum_lt_sum f g h h'
    ```
  - Bad argument names:
    ```lean
    lemma Multiset.sum_lt_sum {ι α : Type} [OrderedCancelAddCommMonoid α]
        {s : Multiset ι} {f g : ι → α}
        (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
        (s.map f).sum < (s.map g).sum := by
      obtain ⟨l⟩ := s
      simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
      exact l.sum_lt_sum f g hle hlt
    ```
  - Acceptable argument names:
    ```lean
    lemma Multiset.sum_lt_sum {ι α : Type} [OrderedCancelAddCommMonoid α]
        {s : Multiset ι} {f g : ι → α}
        (hfg : ∀ i ∈ s, f i ≤ g i) (hfg' : ∃ i ∈ s, f i < g i) :
        (s.map f).sum < (s.map g).sum := by
      obtain ⟨l⟩ := s
      simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
      exact l.sum_lt_sum f g hfg hfg'
    ```
  - Better argument names:
    ```lean
    lemma Multiset.sum_lt_sum {ι α : Type} [OrderedCancelAddCommMonoid α]
        {s : Multiset ι} {f g : ι → α}
        (all_f_le_g : ∀ i ∈ s, f i ≤ g i) (exists_f_lt_g : ∃ i ∈ s, f i < g i) :
        (s.map f).sum < (s.map g).sum := by
      obtain ⟨l⟩ := s
      simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
      exact l.sum_lt_sum f g all_f_le_g exists_f_lt_g
    ```
  - Best argument names:
    ```lean
    lemma Multiset.sum_lt_sum {ι α : Type} [OrderedCancelAddCommMonoid α]
        {s : Multiset ι} {f g : ι → α}
        (all_le : ∀ i ∈ s, f i ≤ g i) (exists_lt : ∃ i ∈ s, f i < g i) :
        (s.map f).sum < (s.map g).sum := by
      obtain ⟨l⟩ := s
      simp only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.prod_coe]
      exact l.sum_lt_sum f g all_le exists_lt
    ```

##### Default single-capital-letter names

- `A` ... matrix
- `B` ... standard representation matrix
- `C` ... circuit
- `D` ... dependent set
- `E` ... ground set
- `F` ... field
- `G` ... base
- `I` ... independent set
- `J` ... independent set
- `M` ... matroid
- `O` ... module
- `P` ... proposition
- `Q` ... proposition
- `R` ... (semi)ring
- `S` ... standard representation of a matroid
- `X` ... set of row indices
- `Y` ... set of col indices
- `Z` ... subset of indices

### Stability and readability

- Do not open namespaces (but `open scoped` is fine).
- Do not utilize automatic opening of a namespace for the declaration's name prefix.

  For example, do not write:
  ```lean
  def List.uppcaseLetters (l : List Char) := map Char.toUpper l
  ```
  Either write down the full name of the function:
  ```lean
  def List.uppcaseLetters (l : List Char) := List.map Char.toUpper l
  ```
  Or, even better, utilize the dot notation:
  ```lean
  def List.uppcaseLetters (l : List Char) := l.map Char.toUpper
  ```
  This way:
  - Reading the code is immediately clear without reading ahead and performing unification inside the reader's mind.
  - The effect of the function will not change when you rename it (and the same applies to proofs).

  Since deviation from the recommended style can be hard to spot here, we use the `implicitNamespace` linter by Damiano Testa to check that the automatically opened namespace hasn't been exploited.
- Annotate types even in situations where they can be inferred automatically, for example:
  ```lean
  def List.uppcaseLetters (l : List Char) : List Char := l.map Char.toUpper
  ```
  The only exception is decidability assumptions such as `[∀ a, Decidable (a ∈ Z)]` where `Z : Set _` because it appears all the time (we do not annotate the type of `a`),

### Other

- We currently prefer `Type` over universe-polymorphic types. Generalization to `Type*` will probably be done at the end of the project.
- We prefer `Unit` over `Fin 1` and we prefer `⟨⟩` over `()` for its only value.
- We prefer not to write parentheses after quantifiers.
- We do not write a space after `¬` but we write redundant parentheses around the negated expression when it contains any infix operator.
- Orphaning parentheses is allowed.
- We like to use our custom notation declared at the beginning of the [Basic](https://github.com/Ivan-Sergeyev/seymour/blob/main/Seymour/Basic/Basic.lean) file.
- We do not write `.1` and `.2` to access fields; write their names instead (with the exception for `Iff.mp` and `Iff.mpr` where we prefer our notation `.→` and `.←` respectively).
- We prefer Mathlib's `have` over Std's `have` inside tactic-block proofs.
- We prefer Mathlib's `congr_arg` and `congr_fun` over Std's `congrArg` and `congrFun` respectively.
- We prefer `exfalso` over `absurd` to discharge "impossible" proof branches.
- When a variable name refers to exactly 2 out of 3 objects, we often refer to the missing object (instead of the two present objects) (analogical to naming parts of a triangle).
- We do not write a space after `←` in the `rw` syntax.
- We do not write `↦` as this syntax does not work everywhere. Write `=>` instead.
- When passing arguments to `simp` and other tactics that don't care about in which order they come, pass variables first, constants later.
- Ordering of cases when eliminating `SignType` is: first `zero` (0), then `pos` (1), then `neg` (-1).
