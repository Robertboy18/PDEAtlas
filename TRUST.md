# What a PDEAtlas theorem trusts

The default build (`lake build`) checks every theorem of PDEAtlas in Lean's kernel. After a build,

```bash
lake env lean --run scripts/Audit.lean
```

reads the compiled library, follows every declaration down to the axioms it rests on, and fails
if one of them is not `propext`, `Classical.choice` or `Quot.sound`. It also prints the counts of
this file: it reads 99,159 declarations of 6,783 modules, the examples included, and finds these
three axioms and no other. It reads the declarations that have a name. An `example` leaves none:
the build checks it in the kernel as it checks a theorem, and a `sorry` in it is an error of the
build.

## Always

- The kernel of Lean 4.36.0 and the three axioms above.
- Mathlib, SymLean, FloatLib and the eight packages that come with them (Batteries, Aesop, Qq,
  ProofWidgets, ImportGraph, LeanSearchClient, Plausible, Cli), at the revisions of
  `lake-manifest.json`. The statements use
  their definitions (`fderiv`, the Bochner and the interval integral, `MeasureTheory.eLpNorm`,
  `Real.rpow`, and so on), so they mean what those definitions mean. What a SymLean proof
  trusts is in SymLean's own [`TRUST.md`](https://github.com/lean-dojo/SymLean/blob/main/TRUST.md).
- The definitions of PDEAtlas that a statement names. A theorem on a weak solution, on
  `W^{k,p}(Ω)` or on `∂[i] u` says what these definitions say, and a reader has to read them.
  The module docs say where a statement differs from its source. In particular
  `fderiv` is zero where a function is not differentiable, so an equation written with
  derivatives is the classical equation only together with the regularity hypotheses of the
  statement.
- The tactics `cas` and `cega` and the command `#cas` build proof terms, and the kernel checks
  them. What they print (a formula, a report, a certificate summary) is output and proves
  nothing by itself: the theorem is what was checked. `python3 Blueprint/Tools/build-cas-ledger.py`
  lists the call sites in `Blueprint/Generated/CasLedgerData.lean`.

## Only in the fast profile

- `lake build -R -Kcertificates=fast` lets `cega [fast]` check finite certificates with compiled
  code: this trusts Lean's compiler and runtime, and the theorem then shows an additional axiom.
  The library has four such call sites, in
  `PDE/Elliptic/PotentialTheory/FundamentalSolution/PlanarKernelBounds.lean` and
  `PlanarAxisKernelBounds.lean`. The profile is off by default, builds into `.lake/build-fast`,
  and the default build checks the same certificates in the kernel.

## Compiled code that cannot reach a theorem

- Seven opaque constants from `partial def`s: six of the planner of `#cas [pdesolve]`
  (`PDE/Symbolic/Command/CAS/PDESolve.lean`) and one of the report on spherical Bessel zeros
  (`PDE/Symbolic/Command/CAS/SphericalBessel.lean`). The kernel never unfolds them, so no proof
  depends on their code. A wrong result makes a command fail or print another report.
- Nine constructor indices `T.ctorIdx`, each implemented by the unsafe definition
  `T.ctorIdx._impl` that Lean generates for an inductive type with several constructors. Only
  compiled code uses the implementation; the kernel uses the logical definition.
- No `@[csimp]` lemma, no `@[extern]`, no `native_decide`, and no `implemented_by` attribute
  written in the sources.
- The audit script counts the opaque constants, the unsafe constants, the `implemented_by`
  attributes and the `csimp` lemmas, and fails when one of the four counts changes. It does not
  look for `@[extern]`, and it does not see one constant replaced by another of the same kind.
- Elaborators, delaborators and notation (`∂[i]`, `∇·`, `W^{k,p}(Ω)`, the PDE routes of `cas`):
  they produce terms or print them, and the kernel checks the terms.

## What no build checks

- That a statement is the theorem of the source it cites. The module docs name the result of
  Evans or of a paper that a theorem formalizes and say where it differs. This is prose.
- The Blueprint: its exposition, its figures and its maps. The library build does not check that the
  published statement cards match the library declarations.
  See the [build notes](Blueprint/README.md#published-site).
- `NOTICE`, the account of where the 42 modules of general lemmas come from.
- `formalization.yaml`, the release metadata.

## Options that the library sets

Inside `PDE/` no file raises a resource limit (`maxHeartbeats`, `maxRecDepth`,
`synthInstance.maxHeartbeats`), and only these linters are turned off. The 42 modules of `NOTICE`
turn off `linter.style.header`, which asks for the license line of our header: they are not under
the license of the library, and their header names the authors instead. In `PDE/Examples`, files
of `#cas` reports turn off `linter.hashCommand`, files that hold only examples turn off
`linter.privateModule`, and a printed report wider than 100 characters turns off
`linter.style.longLine` for one command. `set_option quotPrecheck false in` stands before local
notations. Two declarations carry `@[nolint unusedArguments]`. `bash scripts/counts.sh` counts the
modules that turn the header linter off.

## The other checks

The same run of `scripts/Audit.lean` checks that no two theorems of the library have the same
statement as kernel terms, and that none has the statement of a theorem of a module of Lean,
Mathlib, SymLean or FloatLib that the library imports. It checks the 41,747 theorems that have a
name of their own: those written in the sources, private ones included, and those that Lean derives
under a name, for example from the fields of structures and from instances that are propositions.
The auxiliary theorems that Lean generates under an internal name (`_proof_1`, `congr_simp` and the
like) are left out. The script does not see two statements that agree only after a definition is
unfolded or hypotheses are reordered.

Every one of the 6,598 library modules starts with a doc that says what it proves and where its
statements differ from their source, and 1,986 of them have a References section that cites the
results they formalize. Every public theorem, definition, instance, type and field of a structure
that is written in a source file of the library has a docstring. `bash scripts/counts.sh` prints
the numbers of this file and of the README that are counted on the sources, and fails when a
module has no doc.
