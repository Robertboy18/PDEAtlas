# Contributing to PDEAtlas

Contributions can add mathematics, improve a proof, extend the PDE routes of the computer algebra
system, or clarify the exposition. For a substantial new development, open an issue describing
the mathematical statement and where it belongs. For a focused correction, open a pull request
with the change and the commands you used to check it.

## Getting started

Use the toolchain and dependency revisions committed in the repository, and avoid `lake update`
unless the contribution is a dependency update. The computer algebra system itself is
[SymLean](https://github.com/Robertboy18/SymLean); a change to its APIs needs a SymLean bump here
in the same pull request.

```bash
lake exe cache get
lake build
```

Search PDEAtlas and the pinned Mathlib before adding a declaration:

```bash
rg "name_or_concept" PDE -g '*.lean'
rg "name_or_concept" .lake/packages/mathlib/Mathlib -g '*.lean' --no-ignore
```

Reuse Mathlib's definitions, bundled maps, notation and lemmas when they fit, and keep new
assumptions as weak as the argument allows.

## Where changes belong

| Change | Location |
| --- | --- |
| General analysis or a PDE theorem | Its mathematical subject under `PDE/` |
| Expressions and tactics of the computer algebra system | [SymLean](https://github.com/Robertboy18/SymLean) |
| Routes of the computer algebra system for PDE operators | `PDE/Symbolic/` |
| Finite certificate checks for PDE quantities | `PDE/Numerics/Certificates/`; generic engines go to `CAS/Numerics/` of SymLean |
| A compiled example | `PDE/Examples/` |
| Exposition or a diagram | `Blueprint/`; see [its guide](Blueprint/README.md) |

The path follows the mathematics: a theorem that holds for many equations sits under its analytic
subject, and a theorem about one equation sits under that equation. In the evolution theory,
`PDE/Analysis/Evolution/Galerkin/` holds the statements that mention an approximation family, a
trial projection or a finite-dimensional scheme; statements about abstract trajectories, weak
time derivatives or distributions go in `Integrated/`, `Time/`, `Gelfand/` or `LionsMagenes/`.
General analysis must not depend on an equation-specific application. Import the narrow modules
that own the declarations you use, update callers and exports together when moving code, and
remove obsolete declarations rather than adding forwarding aliases. `PDE.lean` exports the
mathematical library; the Lake library also compiles `PDE/Examples/`, which no production module
imports.

Documentation lives in the module docs (`/-! ... -/`) and docstrings, as in Mathlib. State the
hypotheses and conclusion of the formal result there, with the source it follows. For a named
result, add a short `## How it works` section: the idea of the proof, which steps are classical
and which are ours, and the declarations that carry it.

## Lean style

Follow Mathlib's conventions and the layout of nearby files:

- `UpperCamelCase` for types, `lowerCamelCase` for functions and data, `snake_case` for
  propositions and theorems. Preserve the spelling of referenced declarations in theorem names.
- Put every declaration in a namespace. The calculus of `PDE/FDeriv` and other general lemmas go
  in `PDE`, lemmas meant for dot notation in the namespace of their type
  (`ContDiff.partialDeriv`). The modules of `PDE/Symbolic` and `PDE/Numerics` declare in the
  SymLean namespaces they extend.
- Write an acronym as one word, upper case inside a name (`hilbertPV`, `IsSquareIBPAdmissibleOn`).
  Keep the standard ones (`PV`, `IVP`, `ACL`, `IBP`, `LDL`, `LDU`, `CK` for `C^{k,γ}`) and spell
  out the rest (`reflectTestFunction`, not `reflectTF`).
- Use a structure for a mathematical object that later theorems keep using, such as an evolution
  equation, a Gelfand triple, a Sobolev element with its weak derivatives or a solution operator.
  Keep a coercivity bound, regularity assumption, energy estimate or trace condition of a single
  theorem as an explicit hypothesis or predicate.
- Give public declarations mathematical docstrings. Explain an argument or a design choice in a
  comment rather than narrating tactic calls.
- Keep lines within 100 characters, keep `classical`, local instances and options narrowly
  scoped, and add `@[simp]` only for a stable canonical simplification.
- Use the shared notation (`∂[i]`, `∇·`, the `Sobolev` scope) rather than local aliases.
- Complete every proof: no `sorry`, `admit`, custom axioms, disabled linters or resource-limit
  overrides. Inside `PDE/` the only disabled linters are in `PDE/Examples`: the files of `#cas`
  reports turn off `linter.hashCommand`, files that hold only examples and the private data they
  use turn off `linter.privateModule`, and a printed report wider than 100 characters turns off
  `linter.style.longLine` for that one command. Outside `PDE/`, the Verso document (`Blueprint.lean`
  and the chapters under `Blueprint/`) is prose and embedded markup, not library code. There the
  disabled linters are `linter.style.longLine` and `linter.style.emptyLine`, for the prose of a
  file, and `linter.hashCommand`, for each `#doc`, `#docs` and `#cas` command.

Copy the copyright header and module layout from the nearest file, and keep existing author
attribution when moving or adapting code. The library uses Lean's module system: mathematical
modules use `public import` and `@[expose] public section`, metaprogramming modules also use
`public meta import` and `public meta section`, and an import that only proofs need is a plain
`import`.

## Calculations and certificates

For supported concrete expressions, use `cas` for exact algebra, derivatives and integrals and
`cega` for numerical bounds, with domain hypotheses supplied through `cas using h` when needed.
Keep the surrounding analytic argument in ordinary Lean; a direct Mathlib proof is fine when the
computer algebra system does not support the expression. Import the smallest frontend that
works: `CAS.ExactTactic`, `CAS.IntegrationTactic` or `CAS.CEGA`.

External numerical data enter through the certificate interface `CAS.Numerics` of SymLean. Keep
the analytic soundness theorem explicit: imported data establish no claim by themselves. Use
`cega [fast]` for large finite certificate checks rather than `native_decide` or
`decide +native`; the default build checks it in the kernel.

## Checking a change

Build the changed module first, then the library:

```bash
lake build +PDE.Symbolic.Calculus.Operators
lake build
```

The `+` selects a module. The repository's options apply, including `autoImplicit=false`,
Mathlib's standard linters and warnings as errors. `lake build -R -Kcertificates=fast` builds the
fast profile into `.lake/build-fast`, and `lake build -R` returns to the kernel profile. Keep
every certificate module under 60 s and 8 GB in the kernel profile, since a plain `lake build`
runs many of them in parallel.

For Blueprint changes, run `bash Blueprint/Tools/build.sh`. It regenerates the computation
ledger and the textbook map; the other files in `Blueprint/Generated/` have their own
generators, listed in the [Blueprint guide](Blueprint/README.md). Edit their inputs, not the
output.

## Exposition and sources

Explain the mathematical question, the hypotheses and the argument, and keep worked examples
concrete. Cite the source near the result and in the Blueprint card, verify the edition before
recording page numbers, and state the hypotheses and conclusion of the formal statement. The
module doc ends with a `## References` section giving each source in full: authors, title,
journal or publisher, year, the section, theorem or equation used, and a DOI, arXiv or publisher
link. Cite only what you have read, in the edition you name. Write from the formal argument; do
not paraphrase a textbook paragraph sentence by sentence. A figure should say what it draws and
distinguish an illustration from a certified solution.

A pull request describes the mathematical change and the commands used to check it. For a new
or revised theorem, include its hypotheses, its conclusion and its source.
