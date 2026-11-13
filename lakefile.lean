import Lake

open Lake DSL

/-- The checking profile of the numerical certificates. The default `kernel` checks every
`cega [fast]` certificate in the kernel and builds into `.lake/build`. `fast` (alias `native`)
evaluates them with compiled code, which additionally trusts Lean's compiler, and builds into
`.lake/build-fast`; select it with `lake build -R -Kcertificates=fast`. The profile is forwarded
to SymLean. -/
def certificatesMode : String :=
  match (get_config? certificates).getD "kernel" with
  | "kernel" => "kernel"
  | "fast" | "native" => "fast"
  | value => panic! s!"Unknown certificates profile '{value}'; use kernel or fast"

/-- Lean arguments used throughout the PDE library. Each compiler runs on one thread (`-j1`): Lake
already runs one compiler per hardware thread, and a compiler with several threads keeps the
memory of the kernel checks of several declarations at once, which roughly doubles the peak of a
certificate module. -/
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
require SymLean from git "https://github.com/Robertboy18/SymLean.git" @ "main"
  with NameMap.empty.insert `certificates certificatesMode

-- Mathlib stays last so its release pins govern the shared support packages.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib PDE where
  globs := #[.andSubmodules `PDE]
  moreLeanArgs := pdeLeanArgs ++
    #[if certificatesMode == "fast" then "-Dweak.cega.nativeCertificates=true"
      else "-Dweak.cega.nativeCertificates=false"]
