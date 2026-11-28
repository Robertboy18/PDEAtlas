import Lake

/-!
# PDEAtlas package

Configure the `PDE` library, its dependencies, and the kernel and fast certificate profiles.
-/

open Lake DSL

/-- The checking profile of the numerical certificates. The default `kernel` checks every
`cega [fast]` certificate in the kernel and builds into `.lake/build`. `fast` (alias `native`)
evaluates them with compiled code, which additionally trusts Lean's compiler, and builds into
`.lake/build-fast`; select it with `lake build -R -Kcertificates=fast`. The profile is forwarded
to SymLean. -/
def certificatesMode : String := run_io do
  match (get_config? certificates).getD "kernel" with
  | "kernel" => return "kernel"
  | "fast" | "native" => return "fast"
  | value =>
    throw <| .userError <|
      s!"unknown certificates profile '{value}': use kernel, fast or native, with lake -R"

/-- Shared Lean arguments for the `PDE` library. Use one thread per compiler process to limit
memory use during certificate checks, and enable Mathlib's standard linters and warnings as
errors. -/
def pdeLeanArgs : Array String := #[
  "-j1",
  "-Dpp.unicode.fun=true",
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false",
  "-Dweak.linter.mathlibStandardSet=true",
  "-DwarningAsError=true"
]

package LeanPDE where
  fixedToolchain := true
  version := v!"1.0.0"
  buildDir := if certificatesMode == "fast" then ".lake/build-fast" else ".lake/build"

-- SymLean supplies the computer algebra system (`cas`, `#cas`) and the certificate engines of
-- `cega`; LeanPDE adds the PDE routes of `PDE/Symbolic` and the PDE engines of `PDE/Numerics`.
-- FloatLib, with its executable floats and outward-rounded intervals, comes through SymLean at the
-- revision SymLean pins; two spline modules of LeanPDE import it directly.
require SymLean from git "https://github.com/lean-dojo/SymLean.git" @ "main"
  with NameMap.empty.insert `certificates certificatesMode

-- Mathlib stays last so its release pins govern the shared support packages.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib PDE where
  globs := #[.andSubmodules `PDE]
  moreLeanArgs := pdeLeanArgs ++
    #[if certificatesMode == "fast" then "-Dweak.cega.nativeCertificates=true"
      else "-Dweak.cega.nativeCertificates=false"]
