/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/
import Lean

/-!
# Audit of the compiled library: axioms, duplicate statements, compiled code

Run from the repository root, after `lake build`:

```
lake env lean --run scripts/Audit.lean
```

The script imports every module under `PDE/` (the examples included) and makes three checks on
the declarations of these modules. It exits with code 1 if one of them fails.

1. Axioms. From every declaration it follows the constants that the statement and the proof
   mention, down to the axioms. It fails if one of them is not `propext`, `Classical.choice` or
   `Quot.sound`, and then names the first declarations that depend on each other axiom. A
   declaration that is itself an axiom is found the same way.
2. Duplicates. Two theorems have the same statement, and two definitions the same type and
   value, when these are equal as kernel terms up to the names of bound variables, the kinds of
   binders and the names of universe parameters. The check fails on a theorem of PDEAtlas that
   has the statement of another theorem of the environment: of PDEAtlas, or of a module of
   Lean, Mathlib, SymLean or FloatLib that PDEAtlas imports. It fails on a definition of
   PDEAtlas that equals another definition of the environment, unless the pair is in the list
   `accepted` below, which gives the reason for each pair. It also fails if a listed pair does
   not have equal types and values.
3. Compiled code. It counts the opaque constants, the unsafe constants, the `implemented_by`
   attributes and the `csimp` lemmas of PDEAtlas: four kinds of places where compiled code may
   differ from the definitions that the kernel sees (it does not look for `@[extern]`). It fails
   if the counts are not those of `expectedCompiled` below. `TRUST.md` says what these constants
   are and why none of them can reach a theorem; a change of the counts needs a change there.

What the second check does not see: a module of a dependency that PDEAtlas does not import; a
statement whose hypotheses stand in another order; a statement that agrees with another one
only after a definition is unfolded; a lemma that is a case of a more general one; a
definition of a proposition that states a theorem; an opaque constant. The names that Lean
generates (auxiliary recursors, matchers, `congr_simp` lemmas, `_proof_1`, `eq_1`) are left
out; they are recognized by the form of the name.

The script also prints the number of modules and of declarations. It reads the compiled library,
so it checks what `lake build` built: build first, with the default (kernel) certificate
profile. It sees the declarations that have a name. An `example` and the output of a `#cas`
command leave no declaration; the build checks them in the kernel, and a `sorry` in one of them
is an error of the build.

To see the script fail, add a module under `PDE/` with an axiom, a theorem that restates
`Nat.add_comm` and a definition `def n : ℕ := 96`, build it and run the script: it reports the
axiom with the declarations that use it, the theorem and the definition, and exits with code 1.
-/

open Lean

namespace Audit

/-- The axioms that a declaration of PDEAtlas may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The pairs of definitions with the same type and value that the library keeps, each with its
reason. A private definition is named without its private prefix. -/
def accepted : List (Name × Name × String) := [
  (`CAS.IntegrationPlanner.maxSearchFuel, `PDE.Analysis.polarIntervalBits,
    "the number 96: a search fuel of SymLean and a precision in bits"),
  (`LaplacianEquation.Symbolic.linearHarmonic2D, `VariationalEquation.Symbolic.coordinateTestX2,
    "the expression `x`: a harmonic function of one example and a test function of another"),
  (`LaplacianEquation.Symbolic.quadraticPoisson2D, `VariationalEquation.Symbolic.quadraticTrial2,
    "the expression `x ^ 2 + y ^ 2`: a solution of one example and a trial function of another"),
  (`PDE.Examples.Analysis.EndpointFlattening.derivativeWeight,
    `PDE.Examples.Analysis.SmoothOddApproximation.smoothDerivativeWeight,
    "the weight `1 / x ^ 2 + 1`, private in two example files"),
  (`IncompressibleFlow.massFlux, `IncompressibleFlow.pressureFlux,
    "a scalar field times the velocity: the mass flux `ρu` and the pressure flux `pu`"),
  (`NavierStokes.Symbolic.shearForce2, `NavierStokes.Symbolic.shearVelocity2,
    "the shear flow `(sin y, 0)` is its own force, since `-Δ(sin y) = sin y`"),
  (`NonlinearFirstOrder.hamiltonianTimeDerivative, `NonlinearFirstOrder.valueDerivative,
    "the derivative in the middle argument: `∂H/∂t` for `H p t x` and `F_z` for `F p z x`")]

/-- The numbers of opaque constants, unsafe constants, `implemented_by` attributes and `csimp`
lemmas of PDEAtlas that `TRUST.md` accounts for. -/
def expectedCompiled : Nat × Nat × Nat × Nat := (7, 9, 9, 0)

/-- The module names of the Lean files under `dir` (a path relative to the repository root). -/
partial def modulesUnder (dir : System.FilePath) : IO (Array Name) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      out := out ++ (← modulesUnder entry.path)
    else if entry.path.extension == some "lean" then
      let parts := (entry.path.withExtension "").components
      out := out.push (parts.foldl (fun n s => Name.mkStr n s) Name.anonymous)
  return out

/-- Everything that the type and the value of a constant mention. -/
def uses (ci : ConstantInfo) : Array Name := Id.run do
  let mut used := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
  match ci with
  | .inductInfo v => used := used ++ v.ctors.toArray
  | .ctorInfo v => used := used.push v.induct
  | .recInfo v => used := used ++ v.all.toArray
  | _ => pure ()
  return used

/-- The axioms among the constants reachable from `roots`, and the reachable names that the
environment does not hold (there should be none). -/
def axiomsOf (env : Environment) (roots : Array Name) : Array Name × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  let mut found : Array Name := #[]
  let mut missing : Array Name := #[]
  for r in roots do
    if !seen.contains r then
      seen := seen.insert r
      stack := stack.push r
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      if let .axiomInfo _ := ci then found := found.push n
      for c in uses ci do
        if !seen.contains c then
          seen := seen.insert c
          stack := stack.push c
  return (found, missing)

/-- The constants reachable from `roots` that depend on `target`. -/
def dependents (env : Environment) (roots : Array Name) (target : Name) : Std.HashSet Name :=
  Id.run do
  -- the edges, reversed, among the constants reachable from the roots
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  let mut users : Std.HashMap Name (Array Name) := {}
  for r in roots do
    if !seen.contains r then
      seen := seen.insert r
      stack := stack.push r
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if let some ci := env.find? n then
      for c in uses ci do
        users := users.alter c fun
          | none => some #[n]
          | some a => some (a.push n)
        if !seen.contains c then
          seen := seen.insert c
          stack := stack.push c
  -- backwards from the target
  let mut out : Std.HashSet Name := {}
  stack := #[target]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    for u in users.getD n #[] do
      if !out.contains u then
        out := out.insert u
        stack := stack.push u
  return out

/-- A name that Lean generates: an auxiliary recursor, a matcher or its splitter, a `congr_simp`
lemma, or an internal name such as `_proof_1` and `eq_1`. -/
def isGenerated (env : Environment) (n : Name) : Bool :=
  let user := privateToUserName n
  user.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    user.components.any fun c =>
      match c with
      | .str _ s => s.startsWith "match_" || s == "congr_simp"
      | _ => true

/-- A term with its universe parameters renamed by position. -/
def normLevels (params : List Name) (e : Expr) : Expr :=
  if params.isEmpty then e
  else e.instantiateLevelParams params
    ((List.range params.length).map fun i => Level.param (.num `u i))

/-- The term that stands for a theorem in the comparison: its statement. -/
def statement? : ConstantInfo → Option Expr
  | .thmInfo v => some (normLevels v.levelParams v.type)
  | _ => none

/-- The term that stands for a definition in the comparison: its type applied to its value. -/
def typeAndValue? : ConstantInfo → Option Expr
  | .defnInfo v => some (.app (normLevels v.levelParams v.type) (normLevels v.levelParams v.value))
  | _ => none

/-- The classes of at least two names with equal terms that hold a declaration of PDEAtlas
(`own`). The second component is the number of declarations of PDEAtlas that were compared. -/
def classes (env : Environment) (own : Name → Bool) (term? : ConstantInfo → Option Expr) :
    Array (Array Name) × Nat := Id.run do
  let mut keys : Std.HashSet UInt64 := {}
  let mut count := 0
  for (n, ci) in env.constants.map₁ do
    if own n && !isGenerated env n then
      if let some e := term? ci then
        keys := keys.insert e.hash
        count := count + 1
  let mut buckets : Std.HashMap UInt64 (Array (Name × Expr)) := {}
  for (n, ci) in env.constants.map₁ do
    if !isGenerated env n then
      if let some e := term? ci then
        if keys.contains e.hash then
          buckets := buckets.insert e.hash ((buckets.getD e.hash #[]).push (n, e))
  let mut out : Array (Array Name) := #[]
  for (_, bucket) in buckets do
    let mut rest := bucket
    while !rest.isEmpty do
      let e := rest[0]!.2
      let same := (rest.filter fun p => p.2 == e).map (·.1)
      rest := rest.filter fun p => !(p.2 == e)
      if same.size > 1 && same.any own then
        out := out.push (same.qsort fun a b => a.toString < b.toString)
  return (out.qsort fun a b => a[0]!.toString < b[0]!.toString, count)

/-- Whether the pair is in `accepted`, in one order or the other. -/
def isAccepted (a b : Name) : Bool :=
  let a := privateToUserName a
  let b := privateToUserName b
  accepted.any fun (x, y, _) => (x == a && y == b) || (x == b && y == a)

end Audit

open Audit in
/-- Imports every module under `PDE/` and the root module `PDE`, makes the three checks of the
module doc and prints the counts. Returns 1 if a check fails and 0 otherwise. -/
unsafe def main : IO UInt32 := do
  let mods := (← modulesUnder "PDE").push `PDE
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true) (mods.map fun m => { module := m }) {} 0
  -- the declarations of PDEAtlas: the constants of the modules whose name starts with `PDE`
  let own (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!.getRoot == `PDE
    | none => false
  let decls := env.constants.map₁.fold (fun acc n _ => if own n then acc.push n else acc) #[]
  let mut failed := false
  IO.println s!"modules of PDEAtlas: {mods.size}"
  IO.println s!"declarations of PDEAtlas (generated ones included): {decls.size}"
  -- 1. axioms
  let (found, missing) := axiomsOf env decls
  IO.println s!"axioms they depend on: {found.qsort fun a b => a.toString < b.toString}"
  unless missing.isEmpty do
    failed := true
    IO.eprintln s!"{missing.size} names that a declaration mentions are not in the environment, \
      the first are {missing.extract 0 10}"
  for a in found.filter fun a => !standardAxioms.contains a do
    failed := true
    let dep := dependents env decls a
    let users := (decls.filter dep.contains).qsort fun x y => x.toString < y.toString
    IO.eprintln s!"axiom {a}: declarations of PDEAtlas that depend on it: {users.size}; \
      the first are {users.extract 0 10}"
  -- compiled code beside the logic (`TRUST.md`)
  let mut nOpaque := 0
  let mut nUnsafe := 0
  let mut nImpl := 0
  let mut nCsimp := 0
  for d in decls do
    if let some ci := env.find? d then
      if ci.isUnsafe then nUnsafe := nUnsafe + 1
      else if let .opaqueInfo _ := ci then nOpaque := nOpaque + 1
      if (Compiler.getImplementedBy? env d).isSome then nImpl := nImpl + 1
      if Compiler.hasCSimpAttribute env d then nCsimp := nCsimp + 1
  IO.println s!"opaque constants: {nOpaque}; unsafe constants: {nUnsafe}; \
    `implemented_by` attributes: {nImpl}; `csimp` lemmas: {nCsimp}"
  unless (nOpaque, nUnsafe, nImpl, nCsimp) == expectedCompiled do
    failed := true
    IO.eprintln s!"compiled code beside the logic: these counts are not {expectedCompiled}, the \
      ones that TRUST.md accounts for. Describe the change in TRUST.md and set \
      `expectedCompiled` in this script"
  -- 2. duplicates
  let (thmClasses, nThm) := classes env own statement?
  IO.println s!"theorems of PDEAtlas: {nThm}; classes with one statement and several names: \
    {thmClasses.size}"
  for c in thmClasses do
    failed := true
    IO.eprintln s!"one statement: {c}"
  let (defClasses, nDef) := classes env own typeAndValue?
  let mut nAccepted := 0
  let mut seen : Array (Name × Name) := #[]
  for c in defClasses do
    for a in c do
      for b in c do
        -- a pair of two definitions of dependencies is not a finding about PDEAtlas
        if a.toString < b.toString && (own a || own b) then
          seen := seen.push (privateToUserName a, privateToUserName b)
          if isAccepted a b then nAccepted := nAccepted + 1
          else
            failed := true
            IO.eprintln s!"one type and value: {a} and {b}"
  IO.println s!"definitions of PDEAtlas: {nDef}; pairs with one type and value that hold one \
    of them: {seen.size}, of which {nAccepted} are in the list of accepted pairs"
  for (x, y, _) in accepted do
    unless seen.any fun (a, b) => (a == x && b == y) || (a == y && b == x) do
      failed := true
      IO.eprintln s!"the accepted pair {x}, {y} is no longer a pair: remove it from the list"
  if failed then
    return 1
  IO.println "audit passed"
  return 0
