/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import VersoManual

/-!
# Executable Blueprint examples

Verso Blueprint uses the `lean` code-block name for snippets attached to
formal statement nodes. This module exposes Verso's ordinary elaborated Lean
block under a separate name for calculator sessions and standalone theorem
examples.

The blocks elaborate in a scope that Verso keeps in an environment extension,
not in the scope of the chapter module, so a `set_option` around the chapter's
`#doc` command does not reach them. Mathlib's `linter.hashCommand` would then
warn on every `#cas` example, and the warning would be rendered with the
example. The block below turns that linter off in Verso's scope for the
duration of the block and restores the previous setting afterwards, so that
declarations and `open` statements made inside a block still carry over to the
next one.
-/

open Verso Doc Elab
open Verso.Genre.Manual.InlineLean.Scopes (getScopes setScopes)

namespace Blueprint

/-- The Mathlib linter that rejects `#`-commands in library code. -/
private def hashCommandLinter : Lean.Name := `linter.hashCommand

/--
Elaborate and render a Lean block without attaching it to a formal Blueprint
statement node. `#cas` and other `#`-commands are examples here, so the
`hashCommand` linter is off inside the block.
-/
@[code_block leanExample]
meta def leanExample :
    CodeBlockExpanderOf Verso.Genre.Manual.InlineLean.LeanBlockConfig
  | config, contents => do
    let scopes ← getScopes
    let previous := scopes.head?.bind (·.opts.find? hashCommandLinter)
    setScopes <| scopes.modifyHead fun scope ↦
      { scope with opts := scope.opts.setBool hashCommandLinter false }
    try
      Verso.Genre.Manual.InlineLean.lean config contents
    finally
      let scopes ← getScopes
      setScopes <| scopes.modifyHead fun scope ↦
        { scope with
          opts :=
            match previous with
            | some value => scope.opts.insert hashCommandLinter value
            | none => scope.opts.erase hashCommandLinter }

end Blueprint
