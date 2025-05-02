import Lean.Elab.Command
import Mathlib.Tactic

/-!
# The "implicitNamespace" linter

Original code written by Damiano Testa.

The "implicitNamespace" linter emits a warning when a declaration uses the "implicit namespace" feature.

It attempts to address this issue: https://github.com/leanprover/lean4/issues/6855
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The "implicitNamespace" linter emits a warning when a declaration uses the "implicit namespace" feature.
-/
register_option linter.implicitNamespace : Bool := {
  defValue := true
  descr := "enable the implicitNamespace linter"
}

/-- Add string `a` at the start of the first component of the name `n`. -/
partial def prependBefore (n : Name) (a : String := "_") : Name :=
  n.modifyBase fun
    | .anonymous => .str .anonymous a
    | .str .anonymous s => .str .anonymous (a ++ s)
    | .str p s => .str (prependBefore p a) s
    | .num p n => .num (.str p a) n

def isMonolytic (n : Name) : Bool :=
  match n with
    | .anonymous => false
    | .str .anonymous _ => true
    | .str _ _ => false
    | .num _ _ => false

namespace ImplicitNamespace

@[inherit_doc Mathlib.Linter.linter.implicitNamespace]
def implicitNamespaceLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.implicitNamespace (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let some id := stx.find? (·.isOfKind ``Parser.Command.declId) | return
  let stx1 : Syntax := stx.replaceM (m := Id) fun s =>
    if s.getKind == ``Parser.Command.declId then
      let newId := s.modifyArg 0 fun i => mkIdentFrom i (prependBefore i.getId)
      some newId
    else
      none
  let oldState ← get
  let s ← getScope
  let newId := ((stx1.find? (·.isOfKind ``Parser.Command.declId)).getD default)[0]
  -- do not test declarations with "atomic" names
  if isMonolytic newId.getId then
    return
  -- do not test declarations of inductive types
  if ((stx1.getArg 1).getArg 0).getAtomVal == "inductive" then
    return
  let report : Bool ←
    withScope (fun _ =>
      {(default : Scope) with
        header := s.header
        -- Omitting `opts` seems to be fixing some issues.  It may cause other issues, though.
        currNamespace := s.currNamespace
        openDecls := s.openDecls
        levelNames := s.levelNames
        varDecls := s.varDecls
        varUIds := s.varUIds
        includedVars := s.includedVars
        omittedVars := s.omittedVars
        isNoncomputable := s.isNoncomputable
        }) do
      elabCommand stx1
      return (← get).messages.hasErrors
      -- debug command, to see what errors the linter is finding.  Should be unknown identifier
      --dbg_trace (← (← get).messages.reported.toArray.mapM (·.toString))
  set oldState
  if report then
    Linter.logLint linter.implicitNamespace id
      m!"'{id[0]}' uses the implicit namespace '{id[0].getId.getRoot}'"

initialize addLinter implicitNamespaceLinter

end ImplicitNamespace

end Mathlib.Linter
