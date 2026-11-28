import Lake

open Lake DSL

/-!
# LeanPDE Blueprint package

The mathematical Blueprint is a documentation package layered over LeanPDE.
Keeping its Verso dependency here prevents documentation tooling from entering
the dependency graph of the exact `PDE` library.

The source directory is the repository root, which contains `Blueprint.lean`
and its `Blueprint.Chapters.*` modules.
-/

/-- The checking profile of the numerical certificates, set with `-Kcertificates`. The default
`kernel` checks every `cega [fast]` certificate in the kernel and builds into `.lake/build`;
`fast` (alias `native`) evaluates them with compiled code, which also trusts Lean's compiler,
and builds into `.lake/build-fast`. The profile is forwarded to LeanPDE. -/
def certificatesMode : String := run_io do
  match (get_config? certificates).getD "kernel" with
  | "kernel" => return "kernel"
  | "fast" | "native" => return "fast"
  | value =>
    throw <| .userError <|
      s!"unknown certificates profile '{value}': use kernel, fast or native, with lake -R"

package LeanPDEBlueprint where
  version := v!"1.0.0"
  buildDir := if certificatesMode == "fast" then ".lake/build-fast" else ".lake/build"
  description := "Mathematical blueprint and dependency maps for PDEAtlas"
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

-- The head of VersoBlueprint's open port to Lean 4.36 (leanprover/verso-blueprint#504). The pin
-- moves to the release branch when the port lands.
require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint.git" @
    "74b2c9e6784b88778e3482bbd9d5c67bd26a5c0e"

-- Verso v4.36.0, the revision that the port pins and that the auxiliary-name patch checks.
require verso from git
  "https://github.com/leanprover/verso" @ "6674cf83c82a2c260bf5827d44e58f26568f7cbe"

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides" @ "9b8020d8c764fc2e18af698cd5552c6ffb0a53c2"

-- Match the highlighting API used by Verso and VersoBlueprint.
require subverso from git
  "https://github.com/leanprover/subverso" @ "f9c40d40521bc71f0c33bff422d085dd86d359bd"

-- Keep Mathlib last so its dependency pins govern the remaining documentation graph. This is the
-- revision of the library's own manifest (Mathlib v4.36.0), so both packages share one Mathlib.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"

-- Give auxiliary declarations made by Lean blocks a module-specific name.
-- The helper accepts only the exact pinned source or the corresponding patched source.
post_update pkg do
  let some versoPkg ← findPackageByName? `verso
    | error "Verso dependency missing"
  let result ← IO.Process.output {
    cmd := "python3"
    args := #[(pkg.dir / "Tools" / "patch_verso.py").toString, versoPkg.dir.toString]
  }
  if result.exitCode != 0 then
    error s!"Cannot patch the pinned Verso source:\n{result.stderr}"

@[default_target]
lean_lib Blueprint where
  srcDir := ".."
