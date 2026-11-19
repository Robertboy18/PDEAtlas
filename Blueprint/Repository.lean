/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Verso.Output.Html

/-!
# Repository links

This module is the single source of repository references used by generated
Blueprint views. A source reference is rendered as its path and line, as visible
text. When the environment variable named by `publicUrlVariable` holds the URL
of a public repository, the same reference becomes a link to that line. Development builds
follow `main`; releases set `LEANPDE_SOURCE_REVISION` to the immutable revision
of the published artifact.

`Blueprint/Tools/optimize-site.mjs` reads the same variable for the footer of the
site shell.
-/

namespace LeanPDE.Repository

/-- Revision used by source links in a development render. -/
def sourceRevision : String := "main"

/-- The environment variable that names the public repository. When it is unset or empty,
source references are not links. -/
def publicUrlVariable : String := "LEANPDE_PUBLIC_REPOSITORY_URL"

/-- Where source references may point. -/
structure Target where
  /-- The public repository URL without a trailing slash or `.git`, if any. -/
  publicRoot : Option String := none
  /-- A lowercase hexadecimal commit revision, or `main` for development. -/
  revision : String := sourceRevision
deriving Inhabited

private def normalizeUrl (url : String) : String :=
  let url := url.trimAscii.toString
  let url := if url.endsWith "/" then (url.dropEnd 1).toString else url
  if url.endsWith ".git" then (url.dropEnd 4).toString else url

/-- Read the render target from the environment. -/
def readTarget : IO Target := do
  let supplied := (← IO.getEnv "LEANPDE_SOURCE_REVISION").getD ""
  let supplied := supplied.trimAscii.toString
  let valid := 7 ≤ supplied.length && supplied.length ≤ 40 &&
    supplied.toList.all (fun c ↦ c.isDigit || ('a'.val ≤ c.val && c.val ≤ 'f'.val))
  let revision := if valid then supplied else sourceRevision
  let url := normalizeUrl ((← IO.getEnv publicUrlVariable).getD "")
  pure { publicRoot := if url.isEmpty then none else some url, revision }

/-- Public URL of a source line, for a path relative to the repository root. -/
def sourceUrl (target : Target) (publicRoot : String) (path : String) (line : Nat) : String :=
  s!"{publicRoot}/blob/{target.revision}/{path}#L{line}"

/-- Visible text of a source reference: the path and the line. -/
def sourceText (path : String) (line : Nat) : String :=
  s!"{path}:{line}"

open Verso.Output in
/-- A reference to a source line. With a public repository it is a link carrying
`label` (or the path and line when there is no label). Otherwise it is `label`,
if any, followed by the path and line as plain text in a `leanpde-source-ref`
span, and nothing carries an `href`. `class?` names the CSS class of the link or
of the span. -/
def sourceRef (target : Target) (path : String) (line : Nat) (title : String)
    (label : Option Html := none) (class? : Option String := none) : Html :=
  let text := sourceText path line
  let classAttr := (class?.map fun c ↦ #[("class", c)]).getD #[]
  match target.publicRoot with
  | some publicRoot =>
    .tag "a" (classAttr ++ #[("href", sourceUrl target publicRoot path line), ("title", title)])
      (label.getD (.text true text))
  | none =>
    let cls := (class?.map (· ++ " leanpde-source-ref")).getD "leanpde-source-ref"
    let ref := Html.tag "span" #[("class", cls), ("title", title)] (.text true text)
    match label with
    | some label => .seq #[label, .text true " ", ref]
    | none => ref

open Verso.Output in
/-- `label` as a link to a source line when the repository is public, and as the
same content in a `span` carrying `title` otherwise. For tables whose rows already
show the path and the line. -/
def linkOrText (target : Target) (path : String) (line : Nat) (title : String) (label : Html)
    (class? : Option String := none) : Html :=
  let classAttr := (class?.map fun c ↦ #[("class", c)]).getD #[]
  match target.publicRoot with
  | some publicRoot =>
    .tag "a" (classAttr ++ #[("href", sourceUrl target publicRoot path line), ("title", title)]) label
  | none => .tag "span" (classAttr ++ #[("title", title)]) label

end LeanPDE.Repository
