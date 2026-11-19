/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS
public import PDE.Symbolic.IntegrationByPartsTactic

/-!
# Integration by parts and improper integrals

CAS computes interval integrals and checks the proposed primitives by differentiation.
The endpoint-chord example integrates the affine interpolant of two function values.
The half-line examples use decay at infinity to evaluate exponential moments and an
inverse-square integral.

The weighted integration-by-parts examples keep the field's derivative, integrability,
and endpoint traces explicit. CAS supplies the derivative of the polynomial or logarithmic
weight, as in weighted PDE energy estimates.
-/

@[expose] public section

namespace PDE.Examples.SymbolicIntegration

open Filter
open MeasureTheory
open Set
open scoped Topology

/-! ## Ordinary integration by parts -/

/--
The controlled integration mode performs exactly one integration-by-parts
step. The statement uses ordinary Mathlib interval-integral syntax.
-/
example (a b : ℝ) :
    (∫ t in a..b, t * Real.exp t) =
      b * Real.exp b - a * Real.exp a -
        ∫ t in a..b, 1 * Real.exp t := by
  cas

/-- Domain evidence introduced by `have` is accepted when the integral is a proper subterm of the
relation. -/
example (a b : ℝ) (hab : a < b) :
    (∫ x in a..b, x) / (b - a) = (b ^ 2 - a ^ 2) / (2 * (b - a)) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  cas using hne

/-- Decimal literals are exact coefficients in the integral. -/
example : (∫ t in (0 : ℝ)..1, 0.5 * t) = 1 / 4 := by
  cas

/-- A real power independent of `t` is a coefficient. Integrating in `t` needs no
positivity hypothesis on its base, even when the exponent is written as a numeral. -/
example (a : ℝ) : (∫ t in (0 : ℝ)..1, a ^ (2 : ℝ) * t) = a ^ (2 : ℝ) / 2 := by
  cas

/-- The integral of the chord of `f` between `a` and `b`, an integrand with the symbolic constant
denominator `b - a` and the frozen values `f a`, `f b`, is its interval length times the average
endpoint value. The hypothesis `a < b` supplies the nonzero denominator. -/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b) =
      (b - a) * (f a + f b) / 2 := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  cas using hne

/-! ## Improper integrals over half-lines

The half-line route projects the same checked antiderivative through Mathlib's
`integral_Ioi_of_hasDerivAt_of_tendsto'`: the limit of the primitive at `+∞` is
computed for the exponential and real-power decay shapes, and integrability comes
from the sign of the integrand on the half-line. -/

/-- The exponential integral, with the primitive `-exp (-t)` tending to `0`. -/
example : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
  cas

/-- A product with a polynomial: the limit uses `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`. -/
example : (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-t)) = 1 := by
  cas

/-- A real power: the primitive `t ^ (-1) / (-1)` tends to `0` by `tendsto_rpow_neg_atTop`, and
the requirement `0 < t` on `[1, +∞)` is discharged from the membership. -/
example : (∫ t in Set.Ioi (1 : ℝ), t ^ (-(2 : ℝ))) = 1 := by
  cas

/-! ## Inverse trigonometric primitives

The rational kernels have arctangent primitives. For the square-root kernel,
the interval stays inside `(-1, 1)`, where the arcsine derivative is defined.
-/

/-- `∫₀¹ dt / (1 + t²) = π / 4`, through `Real.arctan_one` and `Real.arctan_zero`. -/
example : (∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2)) = Real.pi / 4 := by
  cas

/-- The rescaling `1 / (4 + t ^ 2)` has the primitive `arctan (t / 2) / 2`. -/
example : (∫ t in (0 : ℝ)..2, 1 / (4 + t ^ 2)) = Real.pi / 8 := by
  cas

/-- A symbolic scale: `1 / (a ^ 2 + t ^ 2)` has the primitive `arctan (t / a) / a`; the
elementary table proposes it and the checked residual records `a ≠ 0`. The upper endpoint is
`1` rather than `a` because the conversion back to ordinary syntax does not cancel `a / a`
inside `arctan`. -/
example (a : ℝ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..1, 1 / (a ^ 2 + t ^ 2)) = Real.arctan (1 / a) / a := by
  cas

/-- `∫₀^{1/2} dt / √(1 - t²) = arcsin (1/2)`, on an interval inside the domain. -/
example : (∫ t in (0 : ℝ)..(1 / 2), 1 / Real.sqrt (1 - t ^ 2)) = Real.arcsin (1 / 2) := by
  cas

/-! ## Parameterized rational kernels -/

/-- A pointwise domain hypothesis keeps the affine denominator away from zero. -/
example (a b u v : ℝ) (ha : a ≠ 0)
    (h : ∀ t ∈ uIcc u v, a * t + b ≠ 0) :
    (∫ t in u..v, 1 / (a * t + b)) =
      (Real.log (a * v + b) - Real.log (a * u + b)) / a := by
  cas

/-- Positive coefficients make the quadratic denominator positive on the whole real line. -/
example (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in u..v, 1 / (a * t ^ 2 + b)) =
      2 / Real.sqrt (4 * a * b) *
        (Real.arctan (2 * a * v / Real.sqrt (4 * a * b)) -
          Real.arctan (2 * a * u / Real.sqrt (4 * a * b))) := by
  cas

/-- The chain rule supplies the primitive `f(t²)` without reflecting the function `f`. -/
example (f f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hc : Continuous f') (a b : ℝ) :
    (∫ t in a..b, f' (t ^ 2) * (2 * t)) = f (b ^ 2) - f (a ^ 2) := by
  cas

/-! ## Weighted-square integration by parts -/

/--
The PDE-oriented `ibp` mode discharges the polynomial weight derivative while
keeping integrability and endpoint limits explicit.
-/
example (a b : ℝ) (field fieldDerivative : ℝ → ℝ)
    (hab : a < b)
    (hfield : ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ (2 * x) * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ x ^ 2 * field x * fieldDerivative x)
        (Ioo a b))
    (hlower :
      Tendsto (fun x ↦ x ^ 2 * field x ^ 2) (𝓝[>] a) (𝓝 0))
    (hupper :
      Tendsto (fun x ↦ x ^ 2 * field x ^ 2) (𝓝[<] b) (𝓝 0)) :
    SobolevSpace.Weighted.weightedSquareEnergy
        a b (fun x ↦ 2 * x) field =
      -2 * SobolevSpace.Weighted.weightedPrimitiveCross
        a b (fun x ↦ x ^ 2) field fieldDerivative := by
  cas [ibp]

/--
An analytic weight may provide the derivative condition through an explicit
domain hypothesis that the checked integrator uses.
-/
example (a b : ℝ) (field fieldDerivative : ℝ → ℝ)
    (hab : a < b)
    (hpositive : ∀ x ∈ Ioo a b, 0 < x)
    (hfield : ∀ x ∈ Ioo a b, HasDerivAt field (fieldDerivative x) x)
    (hweighted :
      IntegrableOn (fun x ↦ (1 / x) * field x ^ 2) (Ioo a b))
    (hcross :
      IntegrableOn
        (fun x ↦ Real.log x * field x * fieldDerivative x)
        (Ioo a b))
    (hlower :
      Tendsto (fun x ↦ Real.log x * field x ^ 2) (𝓝[>] a) (𝓝 0))
    (hupper :
      Tendsto (fun x ↦ Real.log x * field x ^ 2) (𝓝[<] b) (𝓝 0)) :
    SobolevSpace.Weighted.weightedSquareEnergy
        a b (fun x ↦ 1 / x) field =
      -2 * SobolevSpace.Weighted.weightedPrimitiveCross
        a b Real.log field fieldDerivative := by
  cas [ibp using hpositive]

end PDE.Examples.SymbolicIntegration
