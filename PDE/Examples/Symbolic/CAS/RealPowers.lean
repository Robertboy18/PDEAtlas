/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import CAS

/-!
# Real powers in the checked symbolic calculator

`Verified.Expr.rpow a b` denotes Mathlib's `Real.rpow`, written `a ^ b` with a real
exponent. The reifier accepts both `a ^ (b : ℝ)` and `Real.rpow a b`; the checked derivative
rule is Mathlib's `HasFDerivAt.rpow`, so every derivative certificate carries the positivity of
the base as its analytic condition. Literal natural and integer exponents are lowered to
natural powers.

The calculator commands at the end of this file run in the build, each inside `#guard_msgs`,
which checks its report. The enclosure route rewrites `a ^ b` as `exp (log a * b)` when the base
interval is strictly positive (`Real.rpow_def_of_pos`) and fails closed otherwise.

The two derivatives display `3/2*sqrt(x)` and `y*x^(y - 1)`, both under `x > 0`. The
exponential-base simplification gives `exp(x*y)` without a condition; the cancellation of powers
of `a` gives `0` under `a > 0`. The first two enclosures are `[1, 1.414214]` and
`[1, 4.000001]`. The last command fails because the base interval contains zero.

## Real-power identities

The side-conditioned normalizer contains the real-power pass
`CAS.ClosedForm.Pipeline.Passes.RealPower`: powers of one base in a product or
quotient are collected into a single power, nested powers flatten, powers of products
distribute, exponents are normalized, and literal exponents are read as natural powers,
reciprocals, or square roots. Every rewrite that Mathlib states for a positive base records
`0 < a` as its condition. Bare `cas` reaches this normal form through the checked identity
route (`CAS.Tactic.Identity`) after the Mathlib arithmetic script fails, and the
derivative finisher reaches it as its checked fallback, so the factored heat kernel derivative
below closes directly. The same pass recombines exponentials without a positivity hypothesis:
`exp a * exp b = exp (a + b)` and `exp u ^ 2 = exp (2 * u)`.

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
    Exact certified output: [1, 2273249076769449584725905731023452155006904586678716168475187917264471287991307473559333290430488816477465239861070692042466482003235557065587086329917422796753378570252078425175982075669563274202953124135134276930898857533296762830524145251317113286598168565583841909231262292364145285222400810811919124118515137953851629603346879455429525507644636522265051987516207772232422795147831424325211975540379610688568287339734785677082459985284965942149486697189269680262049468196073779029672986674507059430503313631701626817776518085888885493767111953886706619857676590994034277699969565897989975741166490566315077948530351867858239070058238521513935599710281891567672769118944289073071753243419355664095287071080689317783159856849/1607429837287377692278241187195331994311002495024203624730988238851833235680816139261369723904500570462264395058805871545840511583759225553691217436894499960905875418086182058601563827565023500342242312168834702081207354005893762126059752063444585844324910839557352975837792943648166542990288975927957364456756203746773437370145207372061939199850677208212886523485234513688263469897026296357708609119042576805830429764572803499327108949126447299322499080669971960992323816094824283923163302949578566519519429703707350197941937799894517976878394708130163314786007288892696118069812012590137073252191827801694357297350044549094409300199122784908440644764560299950201525535925862400000000000000000000000000000000000000000000000000]
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
          (↑2273249076769449584725905731023452155006904586678716168475187917264471287991307473559333290430488816477465239861070692042466482003235557065587086329917422796753378570252078425175982075669563274202953124135134276930898857533296762830524145251317113286598168565583841909231262292364145285222400810811919124118515137953851629603346879455429525507644636522265051987516207772232422795147831424325211975540379610688568287339734785677082459985284965942149486697189269680262049468196073779029672986674507059430503313631701626817776518085888885493767111953886706619857676590994034277699969565897989975741166490566315077948530351867858239070058238521513935599710281891567672769118944289073071753243419355664095287071080689317783159856849 /
            ↑1607429837287377692278241187195331994311002495024203624730988238851833235680816139261369723904500570462264395058805871545840511583759225553691217436894499960905875418086182058601563827565023500342242312168834702081207354005893762126059752063444585844324910839557352975837792943648166542990288975927957364456756203746773437370145207372061939199850677208212886523485234513688263469897026296357708609119042576805830429764572803499327108949126447299322499080669971960992323816094824283923163302949578566519519429703707350197941937799894517976878394708130163314786007288892696118069812012590137073252191827801694357297350044549094409300199122784908440644764560299950201525535925862400000000000000000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn
          (CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑2273249076769449584725905731023452155006904586678716168475187917264471287991307473559333290430488816477465239861070692042466482003235557065587086329917422796753378570252078425175982075669563274202953124135134276930898857533296762830524145251317113286598168565583841909231262292364145285222400810811919124118515137953851629603346879455429525507644636522265051987516207772232422795147831424325211975540379610688568287339734785677082459985284965942149486697189269680262049468196073779029672986674507059430503313631701626817776518085888885493767111953886706619857676590994034277699969565897989975741166490566315077948530351867858239070058238521513935599710281891567672769118944289073071753243419355664095287071080689317783159856849 /
            ↑1607429837287377692278241187195331994311002495024203624730988238851833235680816139261369723904500570462264395058805871545840511583759225553691217436894499960905875418086182058601563827565023500342242312168834702081207354005893762126059752063444585844324910839557352975837792943648166542990288975927957364456756203746773437370145207372061939199850677208212886523485234513688263469897026296357708609119042576805830429764572803499327108949126447299322499080669971960992323816094824283923163302949578566519519429703707350197941937799894517976878394708130163314786007288892696118069812012590137073252191827801694357297350044549094409300199122784908440644764560299950201525535925862400000000000000000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn
          (fun x ↦ |CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑2273249076769449584725905731023452155006904586678716168475187917264471287991307473559333290430488816477465239861070692042466482003235557065587086329917422796753378570252078425175982075669563274202953124135134276930898857533296762830524145251317113286598168565583841909231262292364145285222400810811919124118515137953851629603346879455429525507644636522265051987516207772232422795147831424325211975540379610688568287339734785677082459985284965942149486697189269680262049468196073779029672986674507059430503313631701626817776518085888885493767111953886706619857676590994034277699969565897989975741166490566315077948530351867858239070058238521513935599710281891567672769118944289073071753243419355664095287071080689317783159856849 /
            ↑1607429837287377692278241187195331994311002495024203624730988238851833235680816139261369723904500570462264395058805871545840511583759225553691217436894499960905875418086182058601563827565023500342242312168834702081207354005893762126059752063444585844324910839557352975837792943648166542990288975927957364456756203746773437370145207372061939199850677208212886523485234513688263469897026296357708609119042576805830429764572803499327108949126447299322499080669971960992323816094824283923163302949578566519519429703707350197941937799894517976878394708130163314786007288892696118069812012590137073252191827801694357297350044549094409300199122784908440644764560299950201525535925862400000000000000000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn
          (CAS.Exact.exprFn (𝕏[0].rpow ((CAS.Verified.Expr.nat 1).div (CAS.Verified.Expr.nat 2))))
          (fun x ↦
            ↑3880678914056827277004146918218784149317907081702919793206176156116304523672123612820703014334989386939729634919876563588306993586994782619278303766811922757659253988338260483777545903234586774545195436303968979012106211539190524956583897314761699130923079405141194885069055236012311828212689786739876488575271341700625066973492086827491464707495313730477938511001442285920686265044857720682920584659422187494398717104307589176409568934411413241471985777859241641254373284290898062952836289624085625950022743335408977015718455885783403470645506662016869934643683879886730395769781578488127048993358318368009435245880396416952648370257361306422376244474842191517874294654870151473071753243419355664095287071080689317783159856849 /
              ↑3214859674574755384556482374390663988622004990048407249461976477703666471361632278522739447809001140924528790117611743091681023167518451107382434873788999921811750836172364117203127655130047000684484624337669404162414708011787524252119504126889171688649821679114705951675585887296333085980577951855914728913512407493546874740290414744123878399701354416425773046970469027376526939794052592715417218238085153611660859529145606998654217898252894598644998161339943921984647632189648567846326605899157133039038859407414700395883875599789035953756789416260326629572014577785392236139624025180274146504383655603388714594700089098188818600398245569816881289529120599900403051071851724800000000000000000000000000000000000000000000000000)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑665819239482071892447664543828120160695902091654512543744199678412638052310491334297963566525988246015200844802264820496625970419476331511895868893022922835847503152165896366574418248104539773860710811966299574849691503527403000704464393187872527442273257726026488933393469348715978742232111834883961759661758934207078192233201672083367586307793959314052165464030973258544159325250805127967503366421337033882737857575161982177755351036158518642826987616519297719269725652101249495106509683724928492910983883927994276619834580285994367516888717245756543305071669302101338159630157553307852902488974662764620720651180307318763829769859115736605494954945721591617471243583018426673071753243419355664095287071080689317783159856849 /
            ↑3214859674574755384556482374390663988622004990048407249461976477703666471361632278522739447809001140924528790117611743091681023167518451107382434873788999921811750836172364117203127655130047000684484624337669404162414708011787524252119504126889171688649821679114705951675585887296333085980577951855914728913512407493546874740290414744123878399701354416425773046970469027376526939794052592715417218238085153611660859529145606998654217898252894598644998161339943921984647632189648567846326605899157133039038859407414700395883875599789035953756789416260326629572014577785392236139624025180274146504383655603388714594700089098188818600398245569816881289529120599900403051071851724800000000000000000000000000000000000000000000000000)
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
    Exact certified output: [1, 1329634798179109809503592293717573846683790827944266476148738404100109967693071644444110231726075525053060688245429471114539151283774251216049355439303572449864712367479259687199755919726930789153134134781196367750897424980000155177175868541361690720390126805740767659424993273017183679036419483821410530696353150448398825117382575228495569148412954912036590709477045024013101753407925692296206868614767985736872211961555990884058939461970640927685430043937102507289830758342154786955042635337793275710463508786765089758398706435587758426261021785354816869413312977279619382612428463718184258496286730179469515000369011628603894218355560568018224791291751222026905391916565590319688273272282435761209881/332408699360846671201957126583197942106150811308655839654893586658432739180583227121992443134588218320955585269826965255972154677118046873001816671357501746285102053715192030062094835877128297463887454834469278330940743955907732446501306130387104104110261587684557948524376518846305807326728754479971983153877091993876319236048822758193472110455273804125798530591865745876367778880342826953882356526679507660764291843035361600465686412351103452025608603146221427761060081819990462588344559700009962286430610779545775182220130544403116794101208431155337590703276929581828355957083241260047069266698565386381962272774032553576943183854027812053228619724379449462890625000000000000000000000000000000000000]
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
          (↑1329634798179109809503592293717573846683790827944266476148738404100109967693071644444110231726075525053060688245429471114539151283774251216049355439303572449864712367479259687199755919726930789153134134781196367750897424980000155177175868541361690720390126805740767659424993273017183679036419483821410530696353150448398825117382575228495569148412954912036590709477045024013101753407925692296206868614767985736872211961555990884058939461970640927685430043937102507289830758342154786955042635337793275710463508786765089758398706435587758426261021785354816869413312977279619382612428463718184258496286730179469515000369011628603894218355560568018224791291751222026905391916565590319688273272282435761209881 /
            ↑332408699360846671201957126583197942106150811308655839654893586658432739180583227121992443134588218320955585269826965255972154677118046873001816671357501746285102053715192030062094835877128297463887454834469278330940743955907732446501306130387104104110261587684557948524376518846305807326728754479971983153877091993876319236048822758193472110455273804125798530591865745876367778880342826953882356526679507660764291843035361600465686412351103452025608603146221427761060081819990462588344559700009962286430610779545775182220130544403116794101208431155337590703276929581828355957083241260047069266698565386381962272774032553576943183854027812053228619724379449462890625000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑1329634798179109809503592293717573846683790827944266476148738404100109967693071644444110231726075525053060688245429471114539151283774251216049355439303572449864712367479259687199755919726930789153134134781196367750897424980000155177175868541361690720390126805740767659424993273017183679036419483821410530696353150448398825117382575228495569148412954912036590709477045024013101753407925692296206868614767985736872211961555990884058939461970640927685430043937102507289830758342154786955042635337793275710463508786765089758398706435587758426261021785354816869413312977279619382612428463718184258496286730179469515000369011628603894218355560568018224791291751222026905391916565590319688273272282435761209881 /
            ↑332408699360846671201957126583197942106150811308655839654893586658432739180583227121992443134588218320955585269826965255972154677118046873001816671357501746285102053715192030062094835877128297463887454834469278330940743955907732446501306130387104104110261587684557948524376518846305807326728754479971983153877091993876319236048822758193472110455273804125798530591865745876367778880342826953882356526679507660764291843035361600465686412351103452025608603146221427761060081819990462588344559700009962286430610779545775182220130544403116794101208431155337590703276929581828355957083241260047069266698565386381962272774032553576943183854027812053228619724379449462890625000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑1329634798179109809503592293717573846683790827944266476148738404100109967693071644444110231726075525053060688245429471114539151283774251216049355439303572449864712367479259687199755919726930789153134134781196367750897424980000155177175868541361690720390126805740767659424993273017183679036419483821410530696353150448398825117382575228495569148412954912036590709477045024013101753407925692296206868614767985736872211961555990884058939461970640927685430043937102507289830758342154786955042635337793275710463508786765089758398706435587758426261021785354816869413312977279619382612428463718184258496286730179469515000369011628603894218355560568018224791291751222026905391916565590319688273272282435761209881 /
            ↑332408699360846671201957126583197942106150811308655839654893586658432739180583227121992443134588218320955585269826965255972154677118046873001816671357501746285102053715192030062094835877128297463887454834469278330940743955907732446501306130387104104110261587684557948524376518846305807326728754479971983153877091993876319236048822758193472110455273804125798530591865745876367778880342826953882356526679507660764291843035361600465686412351103452025608603146221427761060081819990462588344559700009962286430610779545775182220130544403116794101208431155337590703276929581828355957083241260047069266698565386381962272774032553576943183854027812053228619724379449462890625000000000000000000000000000000000000)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (𝕏[0].rpow 𝕏[0]))
          (fun x ↦
            ↑1662043497539956480705549420300771788789941639252922315803631990758542706873654871566102674860663743374016273515256436370511305960892298089051172110661074196149814421194451717261850755604059086617021589615665646081838168935907887623677174671748794824500388393425325607949369791863489486363148238301382513850230242442275144353431397986689041258868228716162389240068910769889469532288268519250089225141447493397636503804591352484524625874321744379711038647083323935050890840162145249543387195037803237996894119566310864940618836979990875220362230216510154460116589906861447738569511704978231327762985295565851477273143044182180837402209588380071453411016130671489796016916565590319688273272282435761209881 /
              ↑664817398721693342403914253166395884212301622617311679309787173316865478361166454243984886269176436641911170539653930511944309354236093746003633342715003492570204107430384060124189671754256594927774909668938556661881487911815464893002612260774208208220523175369115897048753037692611614653457508959943966307754183987752638472097645516386944220910547608251597061183731491752735557760685653907764713053359015321528583686070723200931372824702206904051217206292442855522120163639980925176689119400019924572861221559091550364440261088806233588202416862310675181406553859163656711914166482520094138533397130772763924545548065107153886367708055624106457239448758898925781250000000000000000000000000000000000000)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 1 2 ⋯].get coordinate)
          (↑997226098818263138301635167134375904577640016635610636493844817441677228512488417322117788591487306732105102975602505858566996606656204343047538767946070703579610313764067657137661083849802491689246679946727089419956681024092422730674562410974586616279865218056209710900616754170877871709690729341438547542476058454522505881333752470302097037957681107910792178885179278136733974527582865342324512088088478076107920118520629283593253049619537475659821440790881079528770676522164324366698075637783313424032898007219314576178575891184641632159813354199479278710036047697791026655345222458137189229588164793087552727594979075026951034501532755964996171567371772564014766916565590319688273272282435761209881 /
            ↑664817398721693342403914253166395884212301622617311679309787173316865478361166454243984886269176436641911170539653930511944309354236093746003633342715003492570204107430384060124189671754256594927774909668938556661881487911815464893002612260774208208220523175369115897048753037692611614653457508959943966307754183987752638472097645516386944220910547608251597061183731491752735557760685653907764713053359015321528583686070723200931372824702206904051217206292442855522120163639980925176689119400019924572861221559091550364440261088806233588202416862310675181406553859163656711914166482520094138533397130772763924545548065107153886367708055624106457239448758898925781250000000000000000000000000000000000000)
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
