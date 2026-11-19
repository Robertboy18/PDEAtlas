/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.ZeroCertificate
public import CAS.Command.SpecialFunctions
public meta import PDE.Analysis.SpecialFunctions.SphericalBessel.ZeroCertificate
public meta import CAS.Command.SpecialFunctions
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Spherical Bessel functions in the calculator

`#cas [N d] (SphericalBesselJ l x)` prints the first `d` significant digits of the spherical
Bessel function `j_l x` at a rational point, as `#cas [N d]` does for elementary expressions. The
value comes from `sphericalBesselGridInterval`, the series of `j_l` on a binary grid, with the
grid and the number of terms doubled until the digits are determined; the kernel checks the
comparison with the decimal bounds through `of_decimalLowerCheck`. The handler declines every
other argument (`throwUnsupportedSyntax`), so `#cas [N d]` falls through to the calls of the
function table in `CAS.Command.Calls` and to the elementary handler.

`#cas [zeros x in [a, b]] (SphericalBesselJ l x)` lists every zero of `j_l` in `(a, b]` with
20 certified decimals, and `#cas (digits := d) [zeros x in [a, b]] (SphericalBesselJ l x)` with
`d` of them, up to 40. The command searches a cover of `[a, b]` by sign cells and root cells and
the kernel checks it with `zeroCoverCheck`; the theorem states that each printed interval contains
exactly one zero and that there are no other zeros in `(a, b]`.
-/

public meta section

namespace CAS.Command.SpecialFunctions

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Continuum
open PDE.Analysis.SpecialFunctions
open CAS.Command.Digits

/-- Recognize `SphericalBesselJ l x`, returning the order and the argument syntax. -/
def sphericalBesselCall? (stx : Syntax) : Option (Nat × Syntax) :=
  match unparen stx with
  | `($f:ident $l:num $x:term) =>
      if f.getId == `SphericalBesselJ || f.getId == `sphericalBesselJ then
        some (l.getNat, x)
      else none
  | _ => none

/-- The working grid and number of series terms of round `round`. -/
def besselPrecision (digits l round : Nat) (x : ℚ) : Nat × Nat :=
  let size := ⌈|x|⌉.toNat
  ((digits * 3322 / 1000 + 3 * size + 64) * 2 ^ round,
    (l / 2 + 2 * size + digits + 30) * 2 ^ round)

/-- The certified theorem for the digits of `j_l x`. -/
def certifyBessel (bits terms l : Nat) (x : ℚ) (outcome : Outcome) : MetaM Lean.Expr := do
  let xTerm ← quoteRat x
  let sound ← mkAppM ``sphericalBesselGridInterval_sound
    #[toExpr bits, toExpr l, toExpr terms, xTerm]
  let (theoremName, args) := match outcome with
    | .positiveDecimal m k =>
        (``RationalInterval.of_decimalLowerCheck, #[toExpr m, toExpr k])
    | .negativeDecimal m k =>
        (``RationalInterval.of_decimalUpperCheck, #[toExpr m, toExpr k])
    | .positiveScaled m k =>
        (``RationalInterval.of_scaledLowerCheck, #[toExpr m, toExpr k])
    | .negativeScaled m k =>
        (``RationalInterval.of_scaledUpperCheck, #[toExpr m, toExpr k])
    | .enclosure lo hi k =>
        (``RationalInterval.of_decimalEnclosureCheck, #[toExpr lo, toExpr hi, toExpr k])
  let partialProof ← mkAppOptM theoremName (#[none, none, some sound] ++ args.map some)
  let .forallE _ checkType _ _ ← whnfR (← inferType partialProof)
    | throwError "N: unexpected certificate theorem shape"
  let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
  cleanProof (mkApp partialProof check) ratCastLemmas

/-- Run `#cas [N d] (SphericalBesselJ l x)`. -/
def logBessel (ref : Syntax) (digits l : Nat) (argument input : Syntax) :
    CommandElabM Unit := do
  checkDigitCount ref "N" digits
  let x ← parseRational "N" argument
  let mut found : Option (Nat × Nat × Outcome) := none
  let mut first : Option (Nat × Nat × RationalInterval) := none
  for round in [0:5] do
    if found.isSome then break
    let (bits, terms) := besselPrecision digits l round x
    let I := sphericalBesselGridInterval bits l terms x
    if first.isNone then first := some (bits, terms, I)
    if let some outcome := resolve? digits I then
      found := some (bits, terms, outcome)
  let (bits, terms, outcome) ← match found, first with
    | some result, _ => pure result
    | none, some (bits, terms, I) => pure (bits, terms, enclosureOutcome digits I)
    | none, none => throwErrorAt input "N could not enclose this value"
  let report ← liftTermElabM do
    let proof ← certifyBessel bits terms l x outcome
    evidenceReportMessage #[← proofStep "Certified decimal digits"
      ``sphericalBesselGridInterval_sound proof]
  let outputType := match outcome with
    | .enclosure _ _ _ => "certified decimal enclosure"
    | _ => s!"first {digits} significant digits, truncated"
  logReport ref {
    domain := "spherical Bessel function at a rational point"
    input := CAS.Command.surfaceText input
    inputType := "scalar ℝ"
    output := renderOutcome outcome
    outputType
  } #[
    computationNode "Certified series evaluation" #[
      m!"Series of j_{l} with {terms} terms on the grid 2^-{bits}",
      m!"Guarantee: every printed digit is a digit of the real value, truncated toward zero"
    ],
    report
  ]

/-! ## Zeros -/

/-- The sign of `j_l x` certified by `sphericalBesselInterval`, if it is determined. -/
def besselSign (l : Nat) (x : ℚ) : Option Bool :=
  let I := sphericalBesselInterval l x
  if 0 < I.lo then some true else if I.hi < 0 then some false else none

/-- A refinement `[m / 10 ^ d, (m + 1) / 10 ^ d]` of the root in `[u, v]`, or the bisection
interval when the decimal neighbours cannot be separated. -/
def refineRoot (l digits : Nat) (u v : ℚ) : ℚ × ℚ := Id.run do
  let some su := besselSign l u | return (u, v)
  let mut lo := u
  let mut hi := v
  for _ in [0:digits * 3322 / 1000 + 16] do
    let m := (lo + hi) / 2
    match besselSign l m with
    | some sm => if sm == su then lo := m else hi := m
    | none => break
  let scale : ℚ := 10 ^ digits
  let m := ⌊lo * scale⌋
  let candidate := ((m : ℚ) / scale, ((m : ℚ) + 1) / scale)
  if u ≤ candidate.1 && candidate.2 ≤ v &&
      sphericalBesselSignChange l candidate.1 candidate.2 then
    return candidate
  return (lo, hi)

/-- Cover `[u, v]` by sign cells and root cells, bisecting at most `depth` times. -/
partial def coverCells (l digits : Nat) (u v : ℚ) (depth : Nat) :
    Except String (List (ℚ × ZeroCell)) := do
  if signCellCheck l u v then return [(v, .sign)]
  if rootCellCheck l u v then
    let (lo, hi) := refineRoot l digits u v
    return [(v, .root lo hi)]
  if depth = 0 then
    throw s!"could not separate the zeros near [{u}, {v}]; the cover needs more subdivision"
  let m := (u + v) / 2
  return (← coverCells l digits u m (depth - 1)) ++ (← coverCells l digits m v (depth - 1))

/-- The largest multiple of `1 / 100` whose square is at most `l (l + 1)`. -/
def originEnd (l : Nat) : ℚ :=
  ((Nat.sqrt (l * (l + 1) * 10000) : ℕ) : ℚ) / 100

/-- A complete cover of `[a, b]`, starting with an origin cell when `a = 0` and `l > 0`. -/
def zeroCover (l digits : Nat) (a b : ℚ) : Except String (List (ℚ × ZeroCell)) := do
  if a = 0 && 0 < l then
    let s := originEnd l
    if b ≤ s then return [(b, .origin)]
    return (s, .origin) :: (← coverCells l digits s b 40)
  coverCells l digits a b 40

/-- The cells as a Lean list. -/
def quoteCells (digits : Nat) (cells : List (ℚ × ZeroCell)) : MetaM Lean.Expr := do
  let cellType := mkConst ``ZeroCell
  let pairType ← mkAppM ``Prod #[mkConst ``Rat, cellType]
  let entries ← cells.mapM fun (t, cell) ↦ do
    let cellTerm ← match cell with
      | .sign => pure (mkConst ``ZeroCell.sign)
      | .origin => pure (mkConst ``ZeroCell.origin)
      | .root lo hi =>
          mkAppM ``ZeroCell.root #[← quoteDecimal digits lo, ← quoteDecimal digits hi]
    mkAppM ``Prod.mk #[← quoteRat t, cellTerm]
  mkListLit pairType entries

/-- The root intervals as a Lean list. -/
def quoteRoots (digits : Nat) (roots : List (ℚ × ℚ)) : MetaM Lean.Expr := do
  let pairType ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``Rat]
  mkListLit pairType (← roots.mapM fun (lo, hi) ↦ do
    mkAppM ``Prod.mk #[← quoteDecimal digits lo, ← quoteDecimal digits hi])

/-- Run `#cas [zeros x in [a, b]] (SphericalBesselJ l x)`. -/
def logZeros (ref : Syntax) (digits l : Nat) (aStx bStx input : Syntax) :
    CommandElabM Unit := do
  if digits = 0 || digits > 40 then
    throwErrorAt ref "zeros accepts between 1 and 40 digits"
  let a ← parseRational "zeros" aStx
  let b ← parseRational "zeros" bStx
  unless 0 ≤ a && a < b do
    throwErrorAt ref "zeros needs rational endpoints 0 ≤ a < b"
  let cells ← match zeroCover l digits a b with
    | .ok cells => pure cells
    | .error message => throwErrorAt input "zeros: {message}"
  let roots := zeroCoverRoots cells
  let report ← liftTermElabM do
    let cellsTerm ← quoteCells digits cells
    let rootsTerm ← quoteRoots digits roots
    let statement ← mkAppM ``of_zeroCoverCheck_list
      #[toExpr l, ← quoteRat a, ← quoteRat b, cellsTerm, rootsTerm]
    let .forallE _ checkType _ _ ← whnfR (← inferType statement)
      | throwError "zeros: unexpected certificate theorem shape"
    let check ← CAS.CEGA.Elaboration.decideClosedCertificate checkType false
    let proof ← cleanProof (mkApp statement check)
      (ratCastLemmas ++ [``List.forall_mem_cons, ``List.not_mem_nil, ``List.mem_cons,
        ``List.mem_nil_iff, ``exists_eq_or_imp, ``exists_eq_left, ``or_false,
        ``forall_eq_or_imp, ``forall_eq, ``IsEmpty.forall_iff, ``forall_const, ``and_true,
        ``false_and, ``exists_false, ``Rat.cast_pow])
    evidenceReportMessage #[← proofStep "Complete list of zeros"
      ``of_zeroCoverCheck proof]
  let rendered := roots.map (renderRoot digits)
  let output := if rendered.isEmpty then "no zeros" else ", ".intercalate rendered
  logReport ref {
    domain := s!"x ∈ ({a}, {b}]"
    input := CAS.Command.surfaceText input
    inputType := "scalar ℝ"
    output
    outputType := s!"all {roots.length} zeros, {digits} decimals each, truncated"
  } #[
    computationNode "Certified cover" #[
      m!"Cells: {cells.length}, of which {roots.length} contain a zero",
      m!"Guarantee: each printed value is the truncation of exactly one zero, and there are no \
        other zeros in the interval"
    ],
    report
  ]

end CAS.Command.SpecialFunctions

namespace CAS.Command

open Lean Elab Command

/-- List the zeros of a spherical Bessel function in `(a, b]` with certified digits. -/
syntax (name := casZerosCommand) "#cas" optConfig "[" &"zeros" ident " in " "[" term ", " term "]"
  "]" term : command

elab_rules : command
  | `(#cas [N $digits:num] $expr:term) => do
      match SpecialFunctions.sphericalBesselCall? expr with
      | some (l, argument) =>
          SpecialFunctions.logBessel digits digits.getNat l argument expr
      | none => throwUnsupportedSyntax
  | `(#cas $cfg:optConfig [zeros $x:ident in [$a:term, $b:term]] $expr:term) => do
      let digits ← parseDigitsOption "zeros" cfg 20
      match SpecialFunctions.unparen expr with
      | `($f:ident $l:num $arg:ident) =>
          unless f.getId == `SphericalBesselJ || f.getId == `sphericalBesselJ do
            throwErrorAt f "zeros supports SphericalBesselJ l {x.getId}"
          unless arg.getId == x.getId do
            throwErrorAt arg "the argument must be the variable {x.getId}"
          SpecialFunctions.logZeros expr digits l.getNat a b expr
      | _ => throwErrorAt expr "zeros supports SphericalBesselJ l {x.getId}"

end CAS.Command
