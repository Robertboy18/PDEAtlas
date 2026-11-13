/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import VersoBlueprint.Commands.Bibliography

/-!
# LeanPDE bibliography command

Verso Blueprint's stock bibliography is unnumbered and titled "Blueprint
Bibliography". LeanPDE presents it as the final numbered chapter, so this
command changes the part metadata and wraps the stock block in one that
differs from it in two ways.

The stock renderer lists, under each entry, the places that cite it. A
citation on a chapter page gets a link such as `Introduction/#--bp-cite-...`,
which is relative to the site root. A citation on the landing page gets the
fragment alone, `#--bp-cite-...`, because the landing page is the site root.
On the Bibliography page that fragment names nothing, and it only reaches the
landing page through the `<base href="./../">` element that every chapter page
carries. The wrapper rewrites those fragments to `index.html#...`, the same
form the site shell uses for its own link to the landing page.

The wrapper also carries the PDF metadata. Verso's TeX preamble loads
`hyperref` and inserts the preamble items contributed by the blocks a document
contains, and the bibliography is the one LeanPDE block that every render of
the book contains exactly once. The title and authors repeat the `#docs`
header of `Blueprint.lean` and must be kept in step with it.
-/

namespace Informal.Commands

open Lean

/-- The `hyperref` metadata of the PDF rendering: title, authors, and a numbered
outline that opens at the chapter level. -/
def leanPDEPdfMetadataPreamble : String :=
  "\\hypersetup{pdftitle={LeanPDE}," ++
    "pdfauthor={Robert Joseph George and Anima Anandkumar}," ++
    "pdfsubject={Partial differential equations and verified computation in Lean}," ++
    "bookmarksnumbered=true,bookmarksopen=true,bookmarksopenlevel=1}"

/-- Prefix of the anchors that `Inline.bpCite` gives to citation use sites. -/
private def citationAnchorPrefix : String := "#--bp-cite-"

/-- Point every fragment-only citation back-link at the landing page, where the
anchor lives. Links that already name a chapter route are left alone. -/
partial def linkCitationFragmentsToRoot : Verso.Output.Html → Verso.Output.Html
  | .tag name attrs contents =>
    let attrs := attrs.map fun (key, value) ↦
      if key == "href" && value.startsWith citationAnchorPrefix then
        (key, "index.html" ++ value)
      else
        (key, value)
    .tag name attrs (linkCitationFragmentsToRoot contents)
  | .seq items => .seq (items.map linkCitationFragmentsToRoot)
  | html => html

open Verso Doc Genre Manual in
/-- The stock bibliography block under a LeanPDE name, so that it can be
rendered by the descriptor below. -/
def Block.leanPDEBibliography (biblio : BibliographyData) : Block where
  data := toJson biblio

open Verso Doc Genre Manual in
/-- The stock bibliography renderer, with root-page citation back-links repaired
and the PDF metadata added to the TeX preamble. -/
@[block_extension Block.leanPDEBibliography]
public def Block.leanPDEBibliography.descr : BlockDescr :=
  { Block.bibliography.descr with
    preamble := Block.bibliography.descr.preamble ++ [leanPDEPdfMetadataPreamble]
    toHtml := Block.bibliography.descr.toHtml.map fun render goI goB id data blocks ↦ do
      linkCitationFragmentsToRoot <$> render goI goB id data blocks }

open Verso Doc Elab Syntax in
private def mkLeanPDEBibliographyPart
    (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titlePreview := "Bibliography"
  let titleInlines ← `(inline | "Bibliography")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let entries := Informal.Cite.allBibEntries (← getEnv)
  let refs : Array (TSyntax `term) ← entries.toArray.mapM fun (label, decl) ↦
    `(BibliographyEntry.mk $(quote label) $(mkIdent decl))
  let block ← ``(Verso.Doc.Block.other
    (Informal.Commands.Block.leanPDEBibliography
      (BibliographyData.mk (entries := ([$refs,*] : List BibliographyEntry)))) #[])
  pure <| FinishedPart.mk stx stx expandedTitle titlePreview none #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
/-- Finish the current chapter and insert the bibliography with repaired citation back-links. -/
@[part_command Lean.Doc.Syntax.command]
public meta def leanPDEBibliographyCmd : PartCommand
  | stx@`(block|command{leanpde_bibliography}) => do
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkLeanPDEBibliographyPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end Informal.Commands
