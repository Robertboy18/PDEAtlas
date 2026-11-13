/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS

/-!
# Real powers in the checked symbolic calculator

`Verified.Expr.rpow a b` denotes Mathlib's `Real.rpow`, written `a ^ b` with a real
exponent. The reifier accepts both `a ^ (b : ℝ)` and `Real.rpow a b`; the checked derivative
rule is Mathlib's `HasFDerivAt.rpow`, so every derivative certificate carries the positivity of
the base as its analytic condition. Natural and literal integer exponents are lowered to
natural powers.

The calculator commands at the end of this file run in the build, each inside `#guard_msgs`,
which checks its report. The enclosure route rewrites `a ^ b` as `exp (log a * b)` when the base
interval is strictly positive (`Real.rpow_def_of_pos`) and fails closed otherwise.

The two derivatives display `3/2*sqrt(x)` and `y*x^(y - 1)`, both under `x > 0`. The
simplifications display `exp(x*y)` and `0` under `a > 0`. The first two enclosures are
`[1, 1.414214]` and `[1, 4.000001]`. The last command fails because the base interval contains
zero.

## Real-power identities

The side-conditioned normalizer contains the real-power pass
`CAS.ClosedForm.Pipeline.Passes.RealPower`: powers of one base in a product or
quotient are collected into a single power, nested powers flatten, powers of products
distribute, exponents are normalized, and literal exponents are read as natural powers,
reciprocals, or square roots. Every rewrite that Mathlib states for a positive base records
`0 < a` as its condition. Bare `cas` reaches this normal form through the checked identity
route (`CAS.Tactic.Identity`) after the Mathlib arithmetic script fails, and the
derivative finisher reaches it as its checked fallback, so the factored heat kernel derivative
below closes directly. The same pass recombines exponentials (`exp a * exp b = exp (a + b)`,
`exp u ^ 2 = exp (2 * u)`), which need no hypothesis.

The compiled examples cover derivatives with real and variable exponents, the heat kernel
time profile, an enclosure on a positive base interval, real-power identities,
and natural exponents with exponent arithmetic and numeral bases.
-/
@[expose] public section

namespace PDE.Examples.CASRealPowers

open CAS.Certificate

/-- The power rule with a real exponent; the base must be positive. -/
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ (3 / 2 : ℝ)) x = (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
  cas using hx

/-- A symbolic constant exponent, the shape of the Sobolev integrand `|x| ^ p` on `0 < x`. -/
example (p x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ p) x = p * x ^ (p - 1) := by
  cas using hx

/-- An exponent depending on the variable uses both terms of Mathlib's `HasDerivAt.rpow`. -/
example (x : ℝ) (hx : 0 < x) :
    deriv (fun t : ℝ ↦ t ^ t) x = x ^ x * Real.log x + x * x ^ (x - 1) := by
  cas using hx

/--
The factored form of the same derivative. Identifying it with the computed derivative needs
`(4πt) ^ (-n/2 - 1) = (4πt) ^ (-n/2) / (4πt)`, which the checked real-power normal form
proves (distributing the base, collecting the powers of `t`, and folding the integer part of
the exponent of the numeric base `4`), so the identity is not supplied by hand. Only the
positivity of `t` is needed; `4 > 0` and `π > 0` are recognized structurally.
-/
example (n : ℕ) (c t : ℝ) (ht : 0 < t) :
    deriv (fun s : ℝ ↦ (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-(c / (4 * s)))) t =
      (c / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(c / (4 * t)))) := by
  cas

/-- The box `[1, 2]` on the line, written as the theorem domain a `cega` statement uses. -/
def positiveDomain : Set (ℝ^1) :=
  {p | 1 ≤ p 0 ∧ p 0 ≤ 2}

/-- A real power is enclosed through `exp (log a * b)` on a positive base interval. -/
example :
    EnclosedOn (fun p : ℝ^1 ↦ p 0 ^ (1 / 2 : ℝ)) positiveDomain (1 : ℝ) (3 / 2 : ℝ) := by
  cega [enclose x in [1, 2]] (x ^ (1 / 2 : ℝ))

/-! ## Real-power identities with bare `cas`

Each identity below is proved by the checked identity route: both sides are reflected over
atoms, the real-power pass reduces their difference to zero, and the recorded positivity of
the base is discharged from the context or from the `using` evidence. -/

/-- Powers of one base collect: `Real.rpow_add` with the exponents normalized. -/
example (a s t : ℝ) (ha : 0 < a) : a ^ (s / 2) * a ^ ((t - s) / 2) = a ^ (t / 2) := by
  cas

/-- Exponents equal as polynomials are identified whatever the order of their atoms: the
collected exponent `t + s` against the stated `s + t`. -/
example (a s t : ℝ) (ha : 0 < a) : a ^ t * a ^ s = a ^ (s + t) := by
  cas

/-- Exponentials are the powers of `e` and are identified the same way. -/
example (u v : ℝ) : Real.exp u * Real.exp v = Real.exp (v + u) := by
  cas

/-- Nested powers flatten (`Real.rpow_mul`). -/
example (a p q : ℝ) (ha : 0 < a) : (a ^ p) ^ q = a ^ (p * q) := by
  cas

/-- A power of a product distributes (`Real.mul_rpow`); both factors must be positive. -/
example (a b p : ℝ) (ha : 0 < a) (hb : 0 < b) : (a * b) ^ p = a ^ p * b ^ p := by
  cas

/-- A natural power inside a real power flattens (`Real.rpow_natCast_mul`), and a natural
power with a symbolic exponent is read as the real power of the cast exponent
(`Real.rpow_natCast`). -/
example (b : ℝ) (k : ℕ) (hb : 0 < b) : (b ^ 2) ^ ((k : ℝ) / 2) = b ^ k := by
  cas

/-- A quotient by the base lowers the exponent by one (`Real.rpow_sub_one`). -/
example (t β : ℝ) (ht : 0 < t) : t ^ (β - 1) = t ^ β / t := by
  cas

/-- A negative exponent is a reciprocal (`Real.rpow_neg`). -/
example (t β : ℝ) (ht : 0 < t) : t ^ (-β) = 1 / t ^ β := by
  cas

/-- A natural literal exponent is a natural power (`Real.rpow_natCast`); no hypothesis is
needed. -/
example (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  cas

/-- The square root is the power `1/2` (`Real.sqrt_eq_rpow`); no hypothesis is needed. -/
example (x : ℝ) : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
  cas

/-- A power of a square root with a symbolic natural exponent, the shape of the heat-ball
normalization `√τ ^ n = τ ^ (n / 2)`. -/
example (τ : ℝ) (n : ℕ) (hτ : 0 < τ) : Real.sqrt τ ^ n = τ ^ ((n : ℝ) / 2) := by
  cas

/-- Powers of a backward scale `T - t` collect from a strict inequality on `t`. -/
example (T t α β : ℝ) (ht : t < T) :
    (T - t) ^ (-α) * ((T - t) ^ (-β)) ^ 2 = (T - t) ^ (-(α + 2 * β)) := by
  cas

/-! ## Natural exponents

A natural power with a symbolic exponent is read by the checked identity route as the real
power of the cast exponent, and the cast is reflected through the exponent's arithmetic: sums,
products, numerals, and a subtraction that `omega` proves non-truncating become real operations
over the atom `↑n`, so `x ^ (n + 2 - 1)` and `x * x ^ n` share one normal form. A numeral base
that is a perfect power of a smaller numeral is rewritten to that base, `4 ^ j = 2 ^ (2 * j)`,
a positive rational numeral base is split into two natural-base powers, and exponents equal as
polynomials are identified in any order of their atoms. -/

/-- The square of a power of two is a power of four (`Real.rpow_natCast_mul`). -/
example (j : ℕ) : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
  cas

/-- Powers of `2` and `4` collect into a power of `8`. -/
example (j : ℕ) : (2 : ℝ) ^ j * 4 ^ j = 8 ^ j := by
  cas

/-- A real power of a perfect-square base with a natural power of its root. -/
example (k : ℕ) : (9 : ℝ) ^ ((k : ℝ) / 2) = 3 ^ k := by
  cas

/-- A non-truncating natural subtraction in the exponent is reflected as a real subtraction
(`Nat.cast_sub`, discharged by `omega`). -/
example (x : ℝ) (n : ℕ) : x ^ (n + 2 - 1) = x * x ^ n := by
  cas

/-- The bound making the subtraction non-truncating may come from the context. -/
example (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (hx : 0 < x) : x ^ (n - 1) = x ^ n / x := by
  cas

/-- Exponents equal as polynomials in any order of their atoms, combined with `√9 = 3`, are
identified on the checked route. -/
example (a : ℝ) (p q : ℕ) : Real.sqrt 9 * a ^ (p + q) = 3 * a ^ (q + p) := by
  cas

/-- A rational numeral base is split into natural-base powers (`Real.div_rpow`), so that the
perfect-power rewrite reaches both parts. -/
example (p : ℕ) : ((1 : ℝ) / 4) ^ p = 1 / 2 ^ (2 * p) := by
  cas

example (p : ℕ) : (2 / 3 : ℝ) ^ p * 3 ^ p = 2 ^ p := by
  cas

/-! ## Exponential recombination

Exponentials are the powers of the base `e` in the same pass, so products, quotients, and
natural powers of exponentials recombine without any hypothesis. -/

/-- `Real.exp_add`, read as a collection of the powers of `e`. -/
example (a b : ℝ) : Real.exp a * Real.exp b = Real.exp (a + b) := by
  cas

/-- A natural power of an exponential (`Real.exp_nat_mul`). -/
example (u : ℝ) : Real.exp u ^ 2 = Real.exp (2 * u) := by
  cas

/-- Recombination and cancellation in one product. -/
example (u : ℝ) : Real.exp u ^ 2 * Real.exp (-2 * u) = 1 := by
  cas

/-- Exponentials separated by other factors are still collected. -/
example (a b x : ℝ) : Real.exp a * x * Real.exp b = x * Real.exp (a + b) := by
  cas

/-- A quotient by an exponential is a negative exponent (`Real.exp_neg`, `Real.exp_sub`). -/
example (a b x : ℝ) : x / Real.exp a = x * Real.exp (-a) ∧
    Real.exp a / Real.exp b = Real.exp (a - b) := by
  constructor
  · cas
  · cas

end PDE.Examples.CASRealPowers

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

/--
info: #cas [derive x]
Domain: x ∈ ℝ
Input (scalar ℝ): (x ^ (3/2 : ℝ))
Output (scalar ℝ): 3/2*sqrt(x)
Conditions: x > 0

[CAS.Command.details] More details
  Variables: x
  [CAS.Command.computation] Analytic domain conditions
    Raw checked nonzero requirements: 2
    Raw checked positivity requirements: x
  [CAS.Command.computation] Partial derivative in x
    [CAS.Command.computation] 1. Apply symbolic differentiation rules
      raw result: 1*3/2*x^(3/2 - 1) + (0*2 - 3*0)/2^2*x^(3/2)*log(x)
    [CAS.Command.computation] 2. Normalize the symbolic derivative unconditionally
      normalized result: 3/2*x^(1/2)
    [CAS.Command.computation] 3. Apply checked side-conditioned cleanup
      displayed result: 3/2*sqrt(x)
      additional nonzero requirements: (none)
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Derivative of the input
        Proposition: ∀ (x : ℝ), 0 < x → HasDerivAt (fun x ↦ x ^ (3 / 2 : ℝ)) (3 / 2 * √x) x
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.hasDerivAt_of_displayRoute
      [CAS.explanation.checkedStep] Partial derivative in x: indexed rules compute Expr.diff
        Proposition: (CAS.Verified.Expr.DiffDerivation.build 0
              (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2)))).rawDerivative =
          CAS.Verified.Expr.diff 0 (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat
2)))
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.rawDerivative_eq_diff
      [CAS.explanation.checkedStep] Partial derivative in x: normalization preserves evaluation
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat
2)))).simplifiedDerivative =
            CAS.Verified.Expr.eval ρ
              (CAS.Verified.Expr.DiffDerivation.build 0
                  (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat
2)))).rawDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.DiffDerivation.eval_simplifiedDerivative_eq_rawDerivative
      [CAS.explanation.checkedStep] Partial derivative in x: side-conditioned display normalization
        Proposition: ∀ (ρ : Fin 1 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (CAS.Command.displayDerivativeRoute
                  (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).nonzero
→
            CAS.Verified.Expr.eval ρ
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).rhs =
              CAS.Verified.Expr.eval ρ
                (CAS.Verified.Expr.DiffDerivation.build 0
                    (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat
2)))).simplifiedDerivative
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.displayDerivativeRoute_sound
      [CAS.explanation.checkedStep] Partial derivative in x: analytic semantics of the displayed
result
        Proposition: ∀ (x : ℝ^1),
          CAS.Verified.Expr.ValidAt x.ofLp (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div
(CAS.Verified.Expr.nat 2))) →
            CAS.Verified.Expr.Alg.SideHolds x.ofLp
                (CAS.Command.displayDerivativeRoute
                    (CAS.Verified.Expr.DiffDerivation.build 0
                      (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat
2))))).nonzero →
              (fderiv ℝ
                    (fun y ↦
                      CAS.Verified.Expr.eval y.ofLp
                        (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))
                    x)
                  (EuclideanSpace.single 0 1) =
                CAS.Verified.Expr.eval x.ofLp
                  (CAS.Command.displayDerivativeRoute
                      (CAS.Verified.Expr.DiffDerivation.build 0
                        (𝕏[0].rpow ((CAS.Verified.Expr.nat 3).div (CAS.Verified.Expr.nat 2))))).rhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.fderiv_apply_single_eq_eval_displayDerivative
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: pythagorean: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
-/
#guard_msgs in
#cas [derive x] (x ^ (3/2 : ℝ))

/--
info: #cas [derive x]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (x ^ y)
Output (scalar ℝ): y*x^(y - 1)
Conditions: x > 0

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [derive x] (x ^ y)

/--
info: #cas [simplify]
Domain: (x, y) ∈ ℝ^2
Input (scalar ℝ): (exp x ^ y)
Output (scalar ℝ): exp(x*y)

[CAS.Command.details] More details
-/
#guard_msgs (info, substring := true) in
#cas [simplify] (exp x ^ y)

/--
info: #cas [simplify]
Domain: (a, s, t) ∈ ℝ^3
Input (scalar ℝ): (a ^ (s / 2) * a ^ ((t - s) / 2) - a ^ (t / 2))
Output (scalar ℝ): 0
Conditions: a > 0

[CAS.Command.details] More details
  Variables: a, s, t
  [CAS.Command.computation] Checked symbolic computation
    Raw checked nonzero requirements: sqrt(a)
    Guarantee: these assumptions justify conditional rewrites and preserve real evaluation
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Identity with the simplified form
        Proposition: ∀ (a s t : ℝ), 0 < a → a ^ (s / 2) * a ^ ((t - s) / 2) - a ^ (t / 2) = 0
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Command.eq_of_simplifyFinDisplayRoute
      [CAS.explanation.checkedStep] Simplification under generated rewrite assumptions
        Proposition: ∀ (ρ : Fin 3 → ℝ),
          CAS.Verified.Expr.Alg.SideHolds ρ
              (((𝕏[0].rpow (𝕏[1].div (CAS.Verified.Expr.nat 2))).mul
                        (𝕏[0].rpow ((𝕏[2].sub 𝕏[1]).div (CAS.Verified.Expr.nat 2)))).sub
                    (𝕏[0].rpow (𝕏[2].div (CAS.Verified.Expr.nat
2)))).simplifyFinDisplayRoute.nonzero →
            CAS.Verified.Expr.eval ρ
                (((𝕏[0].rpow (𝕏[1].div (CAS.Verified.Expr.nat 2))).mul
                          (𝕏[0].rpow ((𝕏[2].sub 𝕏[1]).div (CAS.Verified.Expr.nat 2)))).sub
                      (𝕏[0].rpow (𝕏[2].div (CAS.Verified.Expr.nat 2)))).simplifyFinDisplayRoute.rhs
=
              CAS.Verified.Expr.eval ρ
                (((𝕏[0].rpow (𝕏[1].div (CAS.Verified.Expr.nat 2))).mul
                          (𝕏[0].rpow ((𝕏[2].sub 𝕏[1]).div (CAS.Verified.Expr.nat 2)))).sub
                      (𝕏[0].rpow (𝕏[2].div (CAS.Verified.Expr.nat 2)))).simplifyFinDisplayRoute.lhs
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Verified.Expr.SideClaimRoute.sound
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] pre-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] pre-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] base normalization: structural: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: trig: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: algebra: attempted
        checked
      [CAS.explanation.plannerStep] base normalization: factor-common: attempted
        checked
      [CAS.explanation.plannerStep] post-normalization: inverse-elementary: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: real-power: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: fraction-normal-form: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: rational-side: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-square: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-numeral: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: sqrt-product-collect: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: common-add-factor: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: deep-factor-cancel: attempted
        side-conditioned
      [CAS.explanation.plannerStep] post-normalization: unit-ratio: attempted
        side-conditioned
      [CAS.explanation.plannerStep] direct: rational-canonical: attempted
        side-conditioned
-/
#guard_msgs in
#cas [simplify] (a ^ (s / 2) * a ^ ((t - s) / 2) - a ^ (t / 2))

set_option linter.style.longLine false in
/--
info: #cas [enclose x in [1, 2]]
Domain: x ∈ [1, 2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x ^ (1/2 : ℝ))
Output (certified interval in ℝ): [1, 1.414214]
Upper bound: 1.414214
Absolute bound: 1.414214
Center and radius: ≈1.207106 ± 0.207108

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [1, 2] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
    Decimal preview: outward-rounded to 6 places where it is a bound
    Exact certified output: [1, 342118453460416830048032612000680186019384711691966160244062700441986037035742347997432405329285217844860692503420413189638556660884110989675623123749522415003436228676364686232370730733424805695557846506361041298855653295722631000074447757427542607975588202959428843523645152640125038810479025970110042841/241914278377435796879608382377573653422459037609088132761240530597347652868059881626684082708538312687678142079993575280259150254863723005397442568530762184196214814230916714711367934733585270045751645668695822113864257534480711034067060378125326831362582072872453826386753125888613679104000000000000000000]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, 1 ≤ x ^ (1 / 2 : ℝ) ∧ x ^ (1 / 2 : ℝ) ≤ 1.414214
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, x ^ (1 / 2 : ℝ) ≤ 1.414214
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, |x ^ (1 / 2 : ℝ)| ≤ 1.414214
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, |x ^ (1 / 2 : ℝ) - 1.207106| ≤ 0.207108
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn
          (CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑1 / ↑1)
          (↑342118453460416830048032612000680186019384711691966160244062700441986037035742347997432405329285217844860692503420413189638556660884110989675623123749522415003436228676364686232370730733424805695557846506361041298855653295722631000074447757427542607975588202959428843523645152640125038810479025970110042841 /
            ↑241914278377435796879608382377573653422459037609088132761240530597347652868059881626684082708538312687678142079993575280259150254863723005397442568530762184196214814230916714711367934733585270045751645668695822113864257534480711034067060378125326831362582072872453826386753125888613679104000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn
          (CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑342118453460416830048032612000680186019384711691966160244062700441986037035742347997432405329285217844860692503420413189638556660884110989675623123749522415003436228676364686232370730733424805695557846506361041298855653295722631000074447757427542607975588202959428843523645152640125038810479025970110042841 /
            ↑241914278377435796879608382377573653422459037609088132761240530597347652868059881626684082708538312687678142079993575280259150254863723005397442568530762184196214814230916714711367934733585270045751645668695822113864257534480711034067060378125326831362582072872453826386753125888613679104000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn
          (fun x ↦ |CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div
(CAS.Verified.Expr.nat 2))) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑342118453460416830048032612000680186019384711691966160244062700441986037035742347997432405329285217844860692503420413189638556660884110989675623123749522415003436228676364686232370730733424805695557846506361041298855653295722631000074447757427542607975588202959428843523645152640125038810479025970110042841 /
            ↑241914278377435796879608382377573653422459037609088132761240530597347652868059881626684082708538312687678142079993575280259150254863723005397442568530762184196214814230916714711367934733585270045751645668695822113864257534480711034067060378125326831362582072872453826386753125888613679104000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn
          (CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))))
          (fun x ↦
            ↑584032731837852626927640994378253839441843749301054293005303231039333689903802229624116488037823530532538834583413988469897706915747833995073065692280284599199651042907281400943738665467010075741309492175056863412719910830203342034141508135552869439338170275831882669910398278528738717914479025970110042841 /
              ↑483828556754871593759216764755147306844918075218176265522481061194695305736119763253368165417076625375356284159987150560518300509727446010794885137061524368392429628461833429422735869467170540091503291337391644227728515068961422068134120756250653662725164145744907652773506251777227358208000000000000000000)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑100204175082981033168424229623106532596925674082878027482822169844638384167682466370748322620746905157182550423426837909379406406020387984278180555218760230807221414445447971521002795999839535649806200837665219184991395761241919966007387379302215776613006130086975017136892026751511359706479025970110042841 /
            ↑483828556754871593759216764755147306844918075218176265522481061194695305736119763253368165417076625375356284159987150560518300509727446010794885137061524368392429628461833429422735869467170540091503291337391644227728515068961422068134120756250653662725164145744907652773506251777227358208000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] logarithm range: succeeded
      [CAS.explanation.plannerStep] exponential range: succeeded
-/
#guard_msgs in
#cas [enclose x in [1, 2]] (x ^ (1/2 : ℝ))

set_option linter.style.longLine false in
/--
info: #cas [enclose x in [1, 2]]
Domain: x ∈ [1, 2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (x ^ x)
Output (certified interval in ℝ): [1, 4.000001]
Upper bound: 4.000001
Absolute bound: 4.000001
Center and radius: ≈2.500000 ± 1.500001

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [1, 2] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
    Decimal preview: outward-rounded to 6 places where it is a bound
    Exact certified output: [1, 56325057387889877236502079853780746979906337603386304569895753367279302111798512300121564891044579480028619966022843847751879098065492607135879742648777002550403296477047784233148864336562799901241966275652871987187613581411658182363979848502864218319784289138748809223510797104015136175878411121/14081264285919943177118454034066156799815306300826378443816241959421176746723933705750624806884345172885697223245723596789126182840189605799820423622776415676123859257839894545693412349418810920658966390689358936731252908618230782103902915150702862963230702611178498854089593857562500000000000000]
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, 1 ≤ x ^ x ∧ x ^ x ≤ 4.000001
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, x ^ x ≤ 4.000001
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, |x ^ x| ≤ 4.000001
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 1 2, |x ^ x - 2.500000| ≤ 1.500001
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑1 / ↑1)
          (↑56325057387889877236502079853780746979906337603386304569895753367279302111798512300121564891044579480028619966022843847751879098065492607135879742648777002550403296477047784233148864336562799901241966275652871987187613581411658182363979848502864218319784289138748809223510797104015136175878411121 /
            ↑14081264285919943177118454034066156799815306300826378443816241959421176746723933705750624806884345172885697223245723596789126182840189605799820423622776415676123859257839894545693412349418810920658966390689358936731252908618230782103902915150702862963230702611178498854089593857562500000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑56325057387889877236502079853780746979906337603386304569895753367279302111798512300121564891044579480028619966022843847751879098065492607135879742648777002550403296477047784233148864336562799901241966275652871987187613581411658182363979848502864218319784289138748809223510797104015136175878411121 /
            ↑14081264285919943177118454034066156799815306300826378443816241959421176746723933705750624806884345172885697223245723596789126182840189605799820423622776415676123859257839894545693412349418810920658966390689358936731252908618230782103902915150702862963230702611178498854089593857562500000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑56325057387889877236502079853780746979906337603386304569895753367279302111798512300121564891044579480028619966022843847751879098065492607135879742648777002550403296477047784233148864336562799901241966275652871987187613581411658182363979848502864218319784289138748809223510797104015136175878411121 /
            ↑14081264285919943177118454034066156799815306300826378443816241959421176746723933705750624806884345172885697223245723596789126182840189605799820423622776415676123859257839894545693412349418810920658966390689358936731252908618230782103902915150702862963230702611178498854089593857562500000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]))
          (fun x ↦
            ↑70406321673809820413620533887846903779721643904212683013711995326700478858522446005872189697928924652914317189268567444541005280905682212935700166271553418226527155734887678778842276685981610821900932666342230923918866490029888964467882763653567081283014991749927308077600390961577636175878411121 /
              ↑28162528571839886354236908068132313599630612601652756887632483918842353493447867411501249613768690345771394446491447193578252365680379211599640847245552831352247718515679789091386824698837621841317932781378717873462505817236461564207805830301405725926461405222356997708179187715125000000000000000)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑42243793101969934059383625819714590180091031302559926126079511407858125365074578594370940084160234307142922742777120250962752915225303001336059319026000586874279437219207889687455451987143988980582999884963513050456360672793427400260076933352161355356553586527570310369421203246452636175878411121 /
            ↑28162528571839886354236908068132313599630612601652756887632483918842353493447867411501249613768690345771394446491447193578252365680379211599640847245552831352247718515679789091386824698837621841317932781378717873462505817236461564207805830301405725926461405222356997708179187715125000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] logarithm range: succeeded
      [CAS.explanation.plannerStep] exponential range: succeeded
-/
#guard_msgs in
#cas [enclose x in [1, 2]] (x ^ x)

/--
error: no checked interval route succeeded on this box. Possible domain obstruction: check whether
denominator intervals exclude zero; check whether nonconstant logarithm argument intervals exclude
zero. This is a search diagnostic, not a proof that the expression is singular. Restrict the domain
or rewrite the expression to make these facts interval-visible. `(depth := n)` subdivision still
needs a checked enclosure on every child box
-/
#guard_msgs in
#cas [enclose x in [-1, 2]] (x ^ (1/2 : ℝ))

