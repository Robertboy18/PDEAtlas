/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Command.DSolveOrder
public import PDE.Symbolic.Calculus.EnergyUniqueness
public meta import PDE.Symbolic.Calculus.ClassicalPDE
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Classical linear equations in one space dimension: `#cas [pdesolve u t x]`

`#cas [pdesolve u t x, conditions] equation` treats four problems with rational constant
coefficients, the derivatives written `u_t`, `u_x`, `u_tt`, `u_xx`:

* transport `u_t + c u_x + d u = 0` with `u 0 x = g`: every differentiable solution is
  `e ^ (-d t) g (x - c t)`, and conversely (`ClassicalPDE.transport_iff`);
* heat `u_t = κ u_xx` with `u 0 x = f`, `u t 0 = 0`, `u t L = 0`, for `f` a finite sum of terms
  `b sin (ω x)` with `ω L` a multiple of `π`: the sum `∑ b e ^ (-κ ω ^ 2 t) sin (ω x)` solves the
  problem (`ClassicalPDE.heatSum_solves`), and every `C²` solution equals it on
  `[0, ∞) × [0, L]` by the energy method (`ClassicalPDE.heatSum_unique`);
* wave `u_tt = c ^ 2 u_xx` with `u 0 x = f`, `u_t 0 x = g` and the same boundary values: the sum
  `∑ (a cos (c ω t) + b / (c ω) sin (c ω t)) sin (ω x)` (`ClassicalPDE.waveSum_solves`), again the
  only `C²` solution (`ClassicalPDE.waveSum_unique`);
* wave on the line, without boundary values: d'Alembert's formula with a primitive `G` of `g`
  from the checked integrator (`ClassicalPDE.dalembert_solves`).

Mathematica's `DSolve` gives these formulas for the same problems; here each comes with the
theorem that it solves the problem, and except for the wave equation on the line that it is the
only solution in the stated class.
-/

public meta section

namespace CAS.Command.PDESolve

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.ExpPolynomials CAS.Command.RootSplit
open CAS.Verified.Expr

/-- A constant `q π ^ k` with `k ∈ {0, 1}`. -/
partial def piConst : Verified.Expr (Fin 1) → Option (ℚ × Nat)
  | .nat n => some (n, 0)
  | .int n => some (n, 0)
  | .rat p q => if q = 0 then none else some ((p : ℚ) / q, 0)
  | .pi => some (1, 1)
  | .neg a => do let (q, k) ← piConst a; some (-q, k)
  | .mul a b => do
      let (q₁, k₁) ← piConst a
      let (q₂, k₂) ← piConst b
      if k₁ + k₂ > 1 then none else some (q₁ * q₂, k₁ + k₂)
  | .div a b => do
      let (q₁, k₁) ← piConst a
      let (q₂, k₂) ← piConst b
      if q₂ = 0 || k₂ > k₁ then none else some (q₁ / q₂, k₁ - k₂)
  | _ => none

/-- `ω x` with `ω = q π ^ k`. -/
partial def linearCoefficient : Verified.Expr (Fin 1) → Option (ℚ × Nat)
  | .var _ => some (1, 0)
  | .neg a => do let (q, k) ← linearCoefficient a; some (-q, k)
  | .mul a b =>
      match piConst a, linearCoefficient b with
      | some (q₁, k₁), some (q₂, k₂) => if k₁ + k₂ > 1 then none else some (q₁ * q₂, k₁ + k₂)
      | _, _ => match linearCoefficient a, piConst b with
        | some (q₁, k₁), some (q₂, k₂) =>
            if k₁ + k₂ > 1 then none else some (q₁ * q₂, k₁ + k₂)
        | _, _ => none
  | .div a b => do
      let (q₁, k₁) ← linearCoefficient a
      let (q₂, k₂) ← piConst b
      if q₂ = 0 || k₂ > k₁ then none else some (q₁ / q₂, k₁ - k₂)
  | _ => none

/-- The terms `b sin (ω x)` of a finite sine sum, `ω = q π ^ k`. -/
partial def sineTerms : Verified.Expr (Fin 1) → Option (List (ℚ × ℚ × Nat))
  | .add a b => return (← sineTerms a) ++ (← sineTerms b)
  | .sub a b => return (← sineTerms a) ++ ((← sineTerms b).map fun (c, ω) ↦ (-c, ω))
  | .neg a => return (← sineTerms a).map fun (c, ω) ↦ (-c, ω)
  | .sin arg => do let ω ← linearCoefficient arg; some [(1, ω)]
  | .mul a b =>
      match piConst a, sineTerms b with
      | some (q, 0), some ts => some (ts.map fun (c, ω) ↦ (q * c, ω))
      | _, _ => match sineTerms a, piConst b with
        | some ts, some (q, 0) => some (ts.map fun (c, ω) ↦ (q * c, ω))
        | _, _ => none
  | .div a b => do
      let ts ← sineTerms a
      let (q, k) ← piConst b
      if q = 0 || k ≠ 0 then none else some (ts.map fun (c, ω) ↦ (c / q, ω))
  | .nat 0 => some []
  | _ => none

/-- `q π ^ k` as real term syntax. -/
def piSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) (k : Nat) :
    m (TSyntax `term) := do
  if k = 0 then real q else if q = 1 then `(Real.pi) else `($(← real q) * Real.pi)

/-- Elaborate a statement and its proof. -/
def elabPDE (statement proof : TSyntax `term) : TermElabM Lean.Expr := do
  let type ← elabType statement
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← withoutErrToSorry <| elabTermEnsuringType proof type
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasSorry then throwError "pdesolve: a proof step failed"
  mkExpectedTypeHint value type

/-- The right side of the formula `u t x = …` in a statement: the hypothesis
`∀ t x, u t x = formula`, or the right side of the equivalence. -/
partial def formulaRhs (e : Lean.Expr) : MetaM (Option Format) := do
  match e.getAppFnArgs with
  | (``Eq, #[_, _, rhs]) => return some (← ppExpr rhs)
  | (``Iff, #[_, b]) => formulaRhs b
  | (``And, #[a, _]) => formulaRhs a
  | _ =>
    if e.isForall then
      forallTelescope e fun xs body ↦ do
        for x in xs do
          let type ← inferType x
          if type.isForall then
            let r ← forallTelescope type fun _ b ↦ do
              match b.getAppFnArgs with
              | (``Eq, #[_, _, rhs]) => return some (← ppExpr rhs)
              | _ => return none
            if r.isSome then return r
        formulaRhs body
    else return none

/-- The binder names of `original` on the quantifiers of `changed`, following only the
quantifiers and the applications with the same head. -/
partial def restoreBinders : Lean.Expr → Lean.Expr → Lean.Expr
  | .forallE n t₁ b₁ _, .forallE _ t₂ b₂ bi =>
      .forallE n (restoreBinders t₁ t₂) (restoreBinders b₁ b₂) bi
  | e₁, e₂ =>
      if e₁.isApp && e₂.isApp && e₁.getAppFn.isConst && e₁.getAppFn == e₂.getAppFn &&
          e₁.getAppNumArgs == e₂.getAppNumArgs then
        mkAppN e₂.getAppFn (Array.zipWith restoreBinders e₁.getAppArgs e₂.getAppArgs)
      else e₂

/-- Rename binders that shadow an enclosing binder of the same name, for display. -/
partial def freshBinders (scope : List Name) : Lean.Expr → Lean.Expr
  | .lam n t b bi =>
      let n' := if scope.contains n then
        ([`r, `z, `w, `v, `q].find? (fun m ↦ !scope.contains m)).getD n else n
      .lam n' (freshBinders scope t) (freshBinders (n' :: scope) b) bi
  | .forallE n t b bi =>
      .forallE n (freshBinders scope t) (freshBinders (n :: scope) b) bi
  | .app f a => .app (freshBinders scope f) (freshBinders scope a)
  | .mdata m body => .mdata m (freshBinders scope body)
  | other => other

/-- Merge sine terms with equal frequencies. -/
def mergeTerms (ts : List (ℚ × ℚ × Nat)) : List (ℚ × ℚ × Nat) :=
  let merged := ts.foldl (fun total (c, ω) ↦
    match total.find? (·.2 == ω) with
    | some (c', _) => total.filter (·.2 != ω) ++ [(c + c', ω)]
    | none => total ++ [(c, ω)]) []
  merged.filter (·.1 != 0)

/-- `∀ e ∈ [a₁, …], P e` from proofs of `P aᵢ`. -/
def forallMemSyntax (proofs : List (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let mut acc : TSyntax `term ← `(fun _ h ↦ absurd h List.not_mem_nil)
  for p in proofs.reverse do
    acc ← `(List.forall_mem_cons.mpr ⟨$p, $acc⟩)
  return acc

/-- A function of `x` from condition syntax. -/
def functionOf (x : TSyntax `ident) (stx : Syntax) : CommandElabM (Verified.Expr (Fin 1)) := do
  let reified ← parseExact stx [x.getId]
  return reified.expr.mapVars fun _ ↦ (.var 0 : Verified.Expr (Fin 1))

/-- A constant `q π ^ k` from syntax. -/
def constantOf (x : TSyntax `ident) (stx : Syntax) : CommandElabM (ℚ × Nat) := do
  let some c := piConst (← functionOf x stx)
    | throwErrorAt stx "pdesolve: expected a constant such as 1 or pi"
  return c

/-- `![t, x, u t x, u_t, u_x, u_tt, u_xx]`. -/
def envSyntax (u t x : TSyntax `term) : TermElabM (TSyntax `term) := do
  let s := mkIdent `s
  let r := mkIdent `r
  let y := mkIdent `y
  let z := mkIdent `z
  `(![$t, $x, $u $t $x, deriv (fun $s:ident ↦ $u $s $x) $t, deriv (fun $y:ident ↦ $u $t $y) $x,
    deriv (fun $s:ident ↦ deriv (fun $r:ident ↦ $u $r $x) $s) $t,
    deriv (fun $y:ident ↦ deriv (fun $z:ident ↦ $u $t $z) $y) $x])

/-- The lemmas that restate the answer in ordinary notation. -/
def pdeCleanLemmas : List Name :=
  ExpPolynomials.cleanLemmas ++ [``List.map_cons, ``List.map_nil, ``List.sum_cons, ``List.sum_nil,
    ``add_zero, ``one_mul, ``mul_one, ``zero_mul, ``mul_zero, ``zero_add, ``sub_zero, ``neg_mul,
    ``Real.exp_zero, ``neg_zero, ``zero_div]

/-- Run `#cas [pdesolve u t x, conditions] equation`. -/
def logPDE (ref : Syntax) (u t x : TSyntax `ident) (conditions : Array (TSyntax `term))
    (input : Syntax) : CommandElabM Unit := do
  let (lhs, rhs) ← match unparen input with
    | `($l:term = $r:term) => pure (l, r)
    | _ => throwErrorAt input "pdesolve expects an equation `lhs = rhs`"
  let uName := u.getId
  let named (suffix : String) : Name :=
    Name.mkSimple (uName.toString (escape := false) ++ suffix)
  let names := [t.getId, x.getId, uName, named "_t", named "_x", named "_tt", named "_xx"]
  let reified ← parseExact (← `($lhs - $rhs)) names
  let N := reified.names.length
  let E := reified.expr
  let coefficient (k : Nat) : CommandElabM ℚ := do
    if h : k < N then
      let c := Verified.Expr.simplify (E.diff ⟨k, h⟩)
      if (List.finRange N).any (fun i ↦ c.containsVar i) then
        throwErrorAt input "pdesolve: the coefficients must be rational constants"
      let some q := exactValue? (fun _ ↦ (0 : ℚ)) c
        | throwErrorAt input "pdesolve: the coefficients must be rational constants"
      pure q
    else pure 0
  let aU ← coefficient 2
  let aT ← coefficient 3
  let aX ← coefficient 4
  let aTT ← coefficient 5
  let aXX ← coefficient 6
  -- Homogeneous: the equation vanishes with `u` and its derivatives set to zero.
  let rest : Verified.Expr (Fin N) := E.mapVars fun i ↦
    if i.val < 2 then (.var i : Verified.Expr (Fin N)) else .nat 0
  for point in [((1 : ℚ) / 3, (2 : ℚ) / 7), ((5 : ℚ) / 4, (-3 : ℚ) / 2)] do
    let value := exactValue? (fun i : Fin N ↦ if i.val = 0 then point.1 else point.2) rest
    unless value == some 0 do
      throwErrorAt input "pdesolve: only homogeneous equations are treated"
  -- Conditions.
  let mut initial : Option (Verified.Expr (Fin 1)) := none
  let mut velocity : Option (Verified.Expr (Fin 1)) := none
  let mut boundary : List (ℚ × Nat) := []
  for condition in conditions do
    match condition with
    | `($f:ident $a:term $b:term = $v:term) =>
        let isX := b.raw.isIdent && b.raw.getId == x.getId
        let isT := a.raw.isIdent && a.raw.getId == t.getId
        if f.getId == uName && isX then
          unless (← parseRational "pdesolve" a) = 0 do
            throwErrorAt condition "pdesolve: initial values are given at t = 0"
          initial := some (← functionOf x v)
        else if f.getId == named "_t" && isX then
          unless (← parseRational "pdesolve" a) = 0 do
            throwErrorAt condition "pdesolve: initial values are given at t = 0"
          velocity := some (← functionOf x v)
        else if f.getId == uName && isT then
          unless (← parseRational "pdesolve" v) = 0 do
            throwErrorAt condition "pdesolve: only zero boundary values are treated"
          boundary := boundary ++ [← constantOf x b]
        else throwErrorAt condition "pdesolve: expected {uName} 0 {x.getId} = f, \
          {named "_t"} 0 {x.getId} = g or {uName} {t.getId} L = 0"
    | _ =>
        throwErrorAt condition "pdesolve: expected a condition such as {uName} 0 {x.getId} = f"
  let some f := initial
    | throwErrorAt ref "pdesolve: give the initial value {uName} 0 {x.getId} = f"
  unless conditionFree f do
    throwErrorAt ref "pdesolve: the initial value must be built from polynomials, exp, sin \
      and cos"
  -- The interval `[0, L]`.
  let interval : Option (ℚ × Nat) ← match boundary with
    | [] => pure none
    | [b₁, b₂] =>
        if b₁ = (0, 0) && b₂.1 > 0 then pure (some b₂)
        else if b₂ = (0, 0) && b₁.1 > 0 then pure (some b₁)
        else throwErrorAt ref "pdesolve: the boundary values must be given at 0 and at L > 0"
    | _ => throwErrorAt ref "pdesolve: give the boundary values at 0 and at L"
  let uT : TSyntax `term := ⟨u.raw⟩
  let tT : TSyntax `term := ⟨t.raw⟩
  let xT : TSyntax `term := ⟨x.raw⟩
  let kind : String :=
    if aTT = 0 && aXX = 0 && aT ≠ 0 then "transport"
    else if aTT = 0 && aT ≠ 0 && aX = 0 && aU = 0 && aXX ≠ 0 && -aXX / aT > 0 then "heat"
    else if aT = 0 && aX = 0 && aU = 0 && aTT ≠ 0 && -aXX / aTT > 0 then "wave"
    else "other"
  if kind = "other" then
    throwErrorAt input "pdesolve: the equation is not of transport, heat or wave type with the \
      right signs"
  let proof ← liftTermElabM do
    let certified (prop : TSyntax `term) : TermElabM (TSyntax `term) := do
      let type ← elabType prop
      synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      exprToSyntax (← CAS.CEGA.Elaboration.decideClosedCertificate type false)
    let quote (source : Verified.Expr (Fin 1)) : TermElabM (TSyntax `term) := do
      exprToSyntax (← quoteVerifiedExpr source)
    let ET ← exprToSyntax (← quoteVerifiedExpr E)
    let env ← envSyntax uT tT xT
    let equation ← `(∀ $t:ident $x:ident, Verified.Expr.eval $env $ET = 0)
    let evalSimp ← `(tactic| simp only [Verified.Expr.eval, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Int.cast_ofNat, Int.cast_neg, Nat.cast_ofNat,
      Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_zero])
    let s := mkIdent `s
    let r := mkIdent `r
    let y := mkIdent `y
    let z := mkIdent `z
    let bridgeOf (target : TSyntax `term) (lead : ℚ) : TermElabM (TSyntax `term) := do
      let leadT ← real lead
      let statement ← `(∀ $u:ident : ℝ → ℝ → ℝ, ($equation) ↔ $target)
      let proofT ← `(by
        intro $u:ident
        apply forall_congr'
        intro $t:ident
        apply forall_congr'
        intro $x:ident
        $evalSimp:tactic
        push_cast
        constructor
        · intro h
          linear_combination (1 / $leadT) * h
        · intro h
          linear_combination ($leadT) * h)
      exprToSyntax (← elabPDE statement proofT)
    let sumClose ← `(tactic| (
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Verified.Expr.univariateEval, Verified.Expr.euclideanSingle_eq_const]
      $evalSimp:tactic
      push_cast
      ring_nf))
    let equationAt ← `(Verified.Expr.eval $env $ET = 0)
    let pointBridgeOf (target : TSyntax `term) (lead : ℚ) : TermElabM (TSyntax `term) := do
      let leadT ← real lead
      let statement ← `(∀ $u:ident : ℝ → ℝ → ℝ, ∀ $t:ident $x:ident, ($equationAt) ↔ $target)
      let proofT ← `(by
        intro $u:ident $t:ident $x:ident
        $evalSimp:tactic
        push_cast
        constructor
        · intro h
          linear_combination (1 / $leadT) * h
        · intro h
          linear_combination ($leadT) * h)
      exprToSyntax (← elabPDE statement proofT)
    -- `∑ b sin (ω x) = f x`, the initial data matched with the sine terms.
    let sumEq (terms : TSyntax `term) (pick : TSyntax `term) (fT : TSyntax `term) :
        TermElabM (TSyntax `term) := do
      let statement ← `(∀ $x:ident,
        (List.map $pick $terms).sum = Verified.Expr.univariateEval $fT $xT)
      let proofT ← `(by
        intro $x:ident
        $sumClose:tactic)
      exprToSyntax (← elabPDE statement proofT)
    let fT ← quote f
    let hcfF ← certified (← `(Verified.Expr.conditionFree $fT = true))
    let sinProof (ωT LT : TSyntax `term) (q : ℚ) (k : Nat) (Lq : ℚ) (Lk : Nat) :
        TermElabM (TSyntax `term) := do
      let m := q * Lq
      unless k + Lk = 1 && m.den = 1 do
        throwError "pdesolve: sin (ω L) = 0 fails for the frequency \
          {q}{if k = 1 then "π" else ""}"
      let mT : TSyntax `term ← `(($(← ratSyntax m) : ℤ))
      `(by
        change Real.sin ($ωT * $LT) = 0
        rw [show $ωT * $LT = (($mT : ℤ) : ℝ) * Real.pi by push_cast; ring]
        exact Real.sin_int_mul_pi _)
    if kind = "transport" then
      let c := aX / aT
      let d := aU / aT
      let cT ← real c
      let dT ← real d
      let target ← `(∀ $t:ident $x:ident, deriv (fun $s:ident ↦ $uT $s $xT) $tT +
        $cT * deriv (fun $y:ident ↦ $uT $tT $y) $xT + $dT * $uT $tT $xT = 0)
      let bridge ← bridgeOf target aT
      let statement ← `(∀ $u:ident : ℝ → ℝ → ℝ, Differentiable ℝ (Function.uncurry $uT) →
        ((($equation) ∧ ∀ $x:ident, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) ↔
          ∀ $t:ident $x:ident, $uT $tT $xT =
            Real.exp (-($dT * $tT)) * Verified.Expr.univariateEval $fT ($xT - $cT * $tT)))
      let body ← `(fun $u:ident hu ↦ (and_congr_left' ($bridge $uT)).trans
        (ClassicalPDE.transport_iff $cT $dT
          ((Verified.Expr.contDiff_of_conditionFree $hcfF 1).differentiable (by norm_num)) hu))
      elabPDE statement body
    else if kind = "heat" then
      let some (Lq, Lk) := interval
        | throwError "pdesolve: the heat equation is solved on an interval [0, L] with \
            u t 0 = 0 and u t L = 0"
      let some ts := sineTerms f
        | throwError "pdesolve: the initial value must be a finite sum of terms b sin (ω x)"
      let ts := mergeTerms ts
      let κ := -aXX / aT
      let κT ← real κ
      let LT ← piSyntax Lq Lk
      let mut entries : Array (TSyntax `term) := #[]
      let mut sinProofs : List (TSyntax `term) := []
      for (b, (q, k)) in ts do
        let ωT ← piSyntax q k
        entries := entries.push (← `(($(← real b), $ωT)))
        sinProofs := sinProofs ++ [← sinProof ωT LT q k Lq Lk]
      let TERMS ← `([$entries,*])
      let hsin ← forallMemSyntax sinProofs
      let targetAt ← `(deriv (fun $s:ident ↦ $uT $s $xT) $tT =
        $κT * deriv (fun $y:ident ↦ deriv (fun $z:ident ↦ $uT $tT $z) $y) $xT)
      let target ← `(∀ $t:ident $x:ident, $targetAt)
      let bridge ← bridgeOf target aT
      let pbridge ← pointBridgeOf targetAt aT
      let hfeq ← sumEq TERMS (← `(fun e ↦ e.1 * Real.sin (e.2 * $xT))) fT
      let statement ← `((∀ $u:ident : ℝ → ℝ → ℝ,
        (∀ $t:ident $x:ident, $uT $tT $xT = ClassicalPDE.heatSum $κT $TERMS $tT $xT) →
          ($equation) ∧ (∀ $t:ident, $uT $tT 0 = 0) ∧ (∀ $t:ident, $uT $tT $LT = 0) ∧
            ∀ $x:ident, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) ∧
        ∀ $u:ident : ℝ → ℝ → ℝ, ContDiff ℝ 2 (Function.uncurry $uT) →
          (∀ $t:ident > 0, ∀ $x:ident ∈ Set.Ioo 0 $LT, $equationAt) →
          (∀ $t:ident ≥ 0, $uT $tT 0 = 0) → (∀ $t:ident ≥ 0, $uT $tT $LT = 0) →
          (∀ $x:ident ∈ Set.Icc 0 $LT, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) →
          ∀ $t:ident ≥ 0, ∀ $x:ident ∈ Set.Icc 0 $LT,
            $uT $tT $xT = ClassicalPDE.heatSum $κT $TERMS $tT $xT)
      let body ← `(⟨fun $u:ident hu ↦ by
          have hu' : $uT = fun $t:ident $x:ident ↦ ClassicalPDE.heatSum $κT $TERMS $tT $xT :=
            funext fun $t:ident ↦ funext (hu $tT)
          subst hu'
          obtain ⟨hpde, h0, hL, hinit⟩ := ClassicalPDE.heatSum_solves $κT $LT $TERMS $hsin
          exact ⟨($bridge _).mpr hpde, h0, hL, fun $x:ident ↦ (hinit $xT).trans ($hfeq $xT)⟩,
        fun $u:ident hu hpde h0 hL hinit ↦ ClassicalPDE.heatSum_unique (by norm_num)
          (by positivity) $TERMS $hsin hu
          (fun $t:ident ht $x:ident hx ↦ ($pbridge $uT $tT $xT).mp (hpde $tT ht $xT hx)) h0 hL
          (fun $x:ident hx ↦ (hinit $xT hx).trans ($hfeq $xT).symm)⟩)
      elabPDE statement body
    else
      -- The wave equation.
      let c2 := -aXX / aTT
      let (cn, cm) := (squareFactor c2.num.toNat, squareFactor c2.den)
      unless cn.2 = 1 && cm.2 = 1 do
        throwError "pdesolve: the wave speed √{c2} must be rational"
      let c : ℚ := (cn.1 : ℚ) / cm.1
      let cT ← real c
      let some g := velocity
        | throwError "pdesolve: give the initial velocity {named "_t"} 0 {x.getId} = g"
      unless conditionFree g do
        throwError "pdesolve: the initial velocity must be built from polynomials, exp, sin \
          and cos"
      let gT ← quote g
      let hcfG ← certified (← `(Verified.Expr.conditionFree $gT = true))
      let targetAt ← `(deriv (fun $s:ident ↦ deriv (fun $r:ident ↦ $uT $r $xT) $s) $tT =
          $cT ^ 2 * deriv (fun $y:ident ↦ deriv (fun $z:ident ↦ $uT $tT $z) $y) $xT)
      let target ← `(∀ $t:ident $x:ident, $targetAt)
      let bridge ← bridgeOf target aTT
      let pbridge ← pointBridgeOf targetAt aTT
      match interval with
      | some (Lq, Lk) =>
          let some fs := sineTerms f
            | throwError "pdesolve: the initial value must be a finite sum of terms b sin (ω x)"
          let some gs := sineTerms g
            | throwError "pdesolve: the initial velocity must be a finite sum of terms \
                b sin (ω x)"
          let fs := mergeTerms fs
          let gs := mergeTerms gs
          let freqs := (fs.map (·.2) ++ gs.map (·.2)).eraseDups
          let LT ← piSyntax Lq Lk
          let mut entries : Array (TSyntax `term) := #[]
          let mut sinProofs : List (TSyntax `term) := []
          let mut nonzero : List (TSyntax `term) := []
          for (q, k) in freqs do
            let a := ((fs.find? (·.2 == (q, k))).map (·.1)).getD 0
            let b := ((gs.find? (·.2 == (q, k))).map (·.1)).getD 0
            let ωT ← piSyntax q k
            entries := entries.push (← `(($(← real a), $(← real b), $ωT)))
            sinProofs := sinProofs ++ [← sinProof ωT LT q k Lq Lk]
            nonzero := nonzero ++ [← `(by
              change $cT * $ωT ≠ 0
              first | positivity | norm_num [Real.pi_ne_zero])]
          let TERMS ← `([$entries,*])
          let hsin ← forallMemSyntax sinProofs
          let hω ← forallMemSyntax nonzero
          let hfeq ← sumEq TERMS (← `(fun e ↦ e.1 * Real.sin (e.2.2 * $xT))) fT
          let hgeq ← sumEq TERMS (← `(fun e ↦ e.2.1 * Real.sin (e.2.2 * $xT))) gT
          let statement ← `((∀ $u:ident : ℝ → ℝ → ℝ,
            (∀ $t:ident $x:ident, $uT $tT $xT = ClassicalPDE.waveSum $cT $TERMS $tT $xT) →
              ($equation) ∧ (∀ $t:ident, $uT $tT 0 = 0) ∧ (∀ $t:ident, $uT $tT $LT = 0) ∧
                (∀ $x:ident, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) ∧
                ∀ $x:ident, deriv (fun $s:ident ↦ $uT $s $xT) 0 =
                  Verified.Expr.univariateEval $gT $xT) ∧
            ∀ $u:ident : ℝ → ℝ → ℝ, ContDiff ℝ 2 (Function.uncurry $uT) →
              (∀ $t:ident > 0, ∀ $x:ident ∈ Set.Ioo 0 $LT, $equationAt) →
              (∀ $t:ident ≥ 0, $uT $tT 0 = 0) → (∀ $t:ident ≥ 0, $uT $tT $LT = 0) →
              (∀ $x:ident ∈ Set.Icc 0 $LT, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) →
              (∀ $x:ident ∈ Set.Icc 0 $LT, deriv (fun $s:ident ↦ $uT $s $xT) 0 =
                Verified.Expr.univariateEval $gT $xT) →
              ∀ $t:ident ≥ 0, ∀ $x:ident ∈ Set.Icc 0 $LT,
                $uT $tT $xT = ClassicalPDE.waveSum $cT $TERMS $tT $xT)
          let body ← `(⟨fun $u:ident hu ↦ by
              have hu' : $uT = fun $t:ident $x:ident ↦
                  ClassicalPDE.waveSum $cT $TERMS $tT $xT :=
                funext fun $t:ident ↦ funext (hu $tT)
              subst hu'
              obtain ⟨hpde, h0, hL, hinit, hvel⟩ :=
                ClassicalPDE.waveSum_solves $cT $LT $TERMS $hω $hsin
              exact ⟨($bridge _).mpr hpde, h0, hL, fun $x:ident ↦ (hinit $xT).trans ($hfeq $xT),
                fun $x:ident ↦ (hvel $xT).trans ($hgeq $xT)⟩,
            fun $u:ident hu hpde h0 hL hinit hvel ↦ ClassicalPDE.waveSum_unique (by positivity)
              $TERMS $hω $hsin hu
              (fun $t:ident ht $x:ident hx ↦ ($pbridge $uT $tT $xT).mp (hpde $tT ht $xT hx)) h0 hL
              (fun $x:ident hx ↦ (hinit $xT hx).trans ($hfeq $xT).symm)
              (fun $x:ident hx ↦ (hvel $xT hx).trans ($hgeq $xT).symm)⟩)
          elabPDE statement body
      | none =>
          -- d'Alembert.
          let G ← DSolveOrder.primitiveIn "pdesolve" g "the initial velocity"
          let GT ← quote G
          let routeG ← certified (← `((IntegrationCheck.route (0 : Fin 1) $gT $GT).rhs = 0))
          let certG ← `((IntegrationCheck.AntiderivativeCert.mk $GT $routeG :
            IntegrationCheck.AntiderivativeCert (0 : Fin 1) $gT))
          let reqG ← certified (← `(($certG).requirements.nonzero.isEmpty &&
            ($certG).requirements.positive.isEmpty = true))
          let df ← quote (f.diff 0)
          let hcfDF ← certified (← `(Verified.Expr.conditionFree $df = true))
          let derivOf (ex hcf : TSyntax `term) : TermElabM (TSyntax `term) :=
            `(fun w ↦ Verified.Expr.hasDerivAt_univariateEval $ex w
              (Verified.Expr.validAt_of_conditionFree _ $ex $hcf))
          let hf ← derivOf fT hcfF
          let hf₁ ← derivOf df hcfDF
          let hg ← derivOf gT hcfG
          let hG ← `(fun w ↦ LinearODE.hasDerivAt_of_cert $certG $reqG w)
          let formula ← `((Verified.Expr.univariateEval $fT ($xT + $cT * $tT) +
              Verified.Expr.univariateEval $fT ($xT - $cT * $tT)) / 2 +
            (Verified.Expr.univariateEval $GT ($xT + $cT * $tT) -
              Verified.Expr.univariateEval $GT ($xT - $cT * $tT)) / (2 * $cT))
          let statement ← `(∀ $u:ident : ℝ → ℝ → ℝ,
            (∀ $t:ident $x:ident, $uT $tT $xT = $formula) →
              ($equation) ∧ (∀ $x:ident, $uT 0 $xT = Verified.Expr.univariateEval $fT $xT) ∧
                ∀ $x:ident, deriv (fun $s:ident ↦ $uT $s $xT) 0 =
                  Verified.Expr.univariateEval $gT $xT)
          let body ← `(fun $u:ident hu ↦ by
            obtain ⟨hpde, h0, h1⟩ := ClassicalPDE.dalembert_solves $cT (by norm_num)
              $hf $hf₁ $hG $hg $uT hu
            exact ⟨($bridge _).mpr hpde, h0, h1⟩)
          elabPDE statement body
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof pdeCleanLemmas
      [``Verified.Expr.univariateEval, ``ClassicalPDE.heatSum, ``ClassicalPDE.heatTerm,
        ``ClassicalPDE.waveSum, ``ClassicalPDE.waveTerm] (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let cleaned ← Digits.cleanProof cleaned [``one_mul, ``mul_one, ``zero_add, ``add_zero,
      ``sub_zero, ``zero_mul, ``mul_zero, ``neg_mul, ``Real.exp_zero, ``zero_sub, ``neg_zero,
      ``zero_div, ``sub_neg_eq_add] (simprocs := true) (reversed := [``sub_eq_add_neg])
    let named := freshBinders [] (restoreBinders (← inferType proof) (← inferType cleaned))
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "pdesolve" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        (if kind = "transport" then "The solution, and every differentiable solution has this form"
          else if interval.isSome then
            "The formula solves the problem, and every C² solution equals it on [0, ∞) × [0, L]"
          else "The formula solves the problem") proof]
  let answer ← liftTermElabM do
    let some rhs ← formulaRhs (← inferType proof) | pure "see the statement"
    pure s!"{uName}({t.getId}, {x.getId}) = {rhs}"
  logReport ref {
    domain := match interval with
      | none => s!"{t.getId}, {x.getId} ∈ ℝ"
      | some _ => s!"{x.getId} ∈ [0, L], Dirichlet boundary values"
    input := CAS.Command.surfaceText input
    inputType := s!"{kind} equation"
    output := answer
    outputType := if kind = "wave" && interval.isNone then "d'Alembert's formula"
      else if kind = "transport" then "characteristics" else "separation of variables"
  } #[report]

end CAS.Command.PDESolve

namespace CAS.Command

open Lean Elab Command

/-- Classical linear equations in one space dimension. -/
syntax (name := casPDESolveCommand)
  "#cas" "[" &"pdesolve" ident ident ident (", " term)* "]" term : command

elab_rules : command
  | `(#cas [pdesolve $u:ident $t:ident $x:ident $[, $conditions]*] $equation:term) =>
      PDESolve.logPDE equation u t x conditions equation

end CAS.Command
