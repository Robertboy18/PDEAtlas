import Lake

open Lake DSL

/-!
# LeanPDE Blueprint package

The mathematical Blueprint is a documentation package layered over LeanPDE.
Keeping its Verso dependency here prevents documentation tooling from entering
the dependency graph of the exact `PDE` library.

The source directory is the repository root so that `Blueprint.lean` remains
the `Blueprint` module and continues to own the `Blueprint.Chapters.*` tree.
-/

def certificatesMode : String :=
  match (get_config? certificates).getD "kernel" with
  | "kernel" => "kernel"
  | "fast" | "native" => "fast"
  | value => panic! s!"Unknown certificates profile '{value}'; use kernel or fast"

package LeanPDEBlueprint where
  version := v!"1.0.0"
  buildDir := if certificatesMode == "fast" then ".lake/build-fast" else ".lake/build"
  description := "Mathematical blueprint and dependency maps for LeanPDE"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`warningAsError, true⟩,
    ⟨`weak.verso.blueprint.foldCodeBlocks, true⟩
  ] ++ #[⟨`weak.cega.nativeCertificates, certificatesMode == "fast"⟩]

require LeanPDE from ".."
  with NameMap.empty.insert `certificates certificatesMode

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @
    "ed7f665fb8e27607fdeac127e114c521fbfd902e"

-- Use the Lean 4.35 release stack with VersoBlueprint's 4.35 release-line revision.
require verso from git
  "https://github.com/leanprover/verso" @ "304b8561790c50222551c937ce02928df0d5b445"

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides" @ "b43d452d8023773b0731899b51bc6d373c17b111"

-- Match the highlighting API used by Verso and VersoBlueprint.
require subverso from git
  "https://github.com/leanprover/subverso" @ "892d6dc520270b5fb8c1291dd1b131e8c16255ed"

-- Keep Mathlib last so its dependency pins govern the remaining documentation graph.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "56a005855ea17e0b0958f73ec801ae140b0a1679"

-- Preserve the section-anchor fix from our previous Verso pin.
-- The helper accepts only the exact pinned source or its already-patched form.
post_update pkg do
  let some versoPkg ← findPackageByName? `verso
    | error "Verso dependency missing"
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[(pkg.dir / "Tools" / "patch_verso_anchors.py").toString, versoPkg.dir.toString]
  }
  if result.exitCode != 0 then
    error s!"Cannot preserve Verso section anchors:\n{result.stderr}"

@[default_target]
lean_lib Blueprint where
  srcDir := ".."
