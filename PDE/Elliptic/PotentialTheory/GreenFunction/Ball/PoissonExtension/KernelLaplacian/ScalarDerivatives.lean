/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Laplacian
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
import PDE.FDeriv.Calculus
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.SphereDerivatives.FirstDerivative
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.SphereDerivatives.SecondDerivative

/-!
# Scalar derivatives of the sphere-integral kernel

For `0 < r`, data `g : ℝ^n → ℝ` continuous on the radius-`r` sphere, and `x` inside the ball
`B(0, r)`, consider the sphere integral

`B(x) = ∫_{∂B(0,r)} g(y) / ‖x - y‖ⁿ dS(y)`.

`InteriorRegularity` establishes that `B` is Fréchet differentiable at interior points with
derivative given by differentiating under the integral sign. We convert that
continuous-linear-map statement into coordinate formulas: the first partial derivative `∂ᵢ B(x)`
is the sphere integral of `g(y) · Dₓ(‖x - y‖⁻ⁿ)(eᵢ)`, and the repeated partial derivative
`∂ᵢ∂ᵢ B(x)` is the sphere integral of

`g(y) · ( -n / dⁿ⁺² + n (n + 2) (x - y)ᵢ² / dⁿ⁺⁴ )`, with `d = ‖x - y‖`.

Since `x` stays in the open ball, every denominator `‖x - y‖` is bounded below on the sphere and
the integrands are continuous in `(x, ω)`, which is what justifies each differentiation under the
integral.

## Main results

* `partialDeriv_sphereIntegral_div_distance_pow`,
  `partialDeriv_sphereIntegral_div_distance_pow_scalar`: the first coordinate derivative of `B`, in
  continuous-linear-map and in scalar form.
* `secondPartial_sphereIntegral_div_distance_pow_scalar`: the scalar formula for `∂ᵢ∂ᵢ B(x)`.

## Implementation notes

The sphere `∂B(0, r)` is parametrised by the unit sphere via `ω ↦ r • ω`, which produces the
Jacobian factor `|r|ⁿ⁻¹` in front of every integral. Derivatives of `‖x - y‖⁻ᵏ` are taken from
`EuclideanDistance.invDistPowFDerivFormula`.
-/

@[expose] public section

open PDE (partialDeriv)

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

namespace KernelLaplacian

section PoissonKernelLaplacian

open scoped BigOperators

/-- The coordinate derivative of the singular sphere integral, in continuous-linear-map form. -/
theorem partialDeriv_sphereIntegral_div_distance_pow {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (i : Fin n) {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    (∂[i]
        (fun z : ℝ^n ↦
          PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r)) x =
      (|r| ^ (n - 1) : ℝ) *
        (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n))
          ∂((volume : Measure ℝ^n).toSphere)) (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  have hB :=
    hasFDerivAt_sphereIntegral_div_distance_pow (n := n) (r := r) hr hg (x₀ := x) hx
  have hderiv := hB.fderiv
  have := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ))) hderiv
  -- unfold `partialDeriv` and simplify evaluation of the integral CLM.
  simpa [partialDeriv, smul_eq_mul, mul_assoc] using this

/-- The coordinate derivative of the evaluated first derivative of the inverse-distance power. -/
theorem partialDeriv_sphereIntegral_invDistPowFDeriv_apply {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ Metric.ball (0 : ℝ^n) r) (v : ℝ^n) :
    (∂[i]
        (fun z : ℝ^n ↦
          (|r| ^ (n - 1) : ℝ) *
            ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
              g (r • (ω : ℝ^n)) * EuclideanDistance.invDistPowFDerivFormula n z (r • (ω : ℝ^n)) v
              ∂((volume : Measure ℝ^n).toSphere))) x =
      (|r| ^ (n - 1) : ℝ) *
        (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          (g (r • (ω : ℝ^n))) •
            (let y : ℝ^n := r • (ω : ℝ^n)
             let S : ℝ := (-(n : ℝ)) / dist x y ^ (n + 2)
             let T : ℝ := (innerSL ℝ v) (x - y)
             S • (innerSL ℝ v) +
               T • ((-(n : ℝ)) •
                 EuclideanDistance.invDistPowFDerivFormula (n + 2) x y))
          ∂((volume : Measure ℝ^n).toSphere)) (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  have h :=
    hasFDerivAt_sphereIntegral_invDistPowFDeriv_apply (n := n) (r := r) hr hg (x₀ := x) hx v
  have hderiv := h.fderiv
  have := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ))) hderiv
  simpa [partialDeriv, smul_eq_mul, mul_assoc] using this

/-- Scalar coordinate formula for the first derivative of the singular sphere integral. -/
theorem partialDeriv_sphereIntegral_div_distance_pow_scalar {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (i : Fin n) {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    (∂[i]
        (fun z : ℝ^n ↦
          PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist z y ^ n) 0 r)) x =
      (|r| ^ (n - 1) : ℝ) *
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          g (r • (ω : ℝ^n)) *
            EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n))
              (EuclideanSpace.single i (1 : ℝ))
          ∂((volume : Measure ℝ^n).toSphere) := by
  classical
  have hCLM :=
    partialDeriv_sphereIntegral_div_distance_pow (n := n) (r := r) hr hg i (x := x) hx
  -- Pull the evaluation on the basis vector into the integral.
  have hInt :
      Integrable
        (fun ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)) ↦
          (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)))
        ((volume : Measure ℝ^n).toSphere) := by
    simpa using (integrable_smul_invDistPowFDeriv (n := n) (r := r) hr hg (x := x) hx n)
  -- Rewrite `((∫ φ) v)` as `∫ (φ · v)`.
  have happly :
      (∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n))
          ∂((volume : Measure ℝ^n).toSphere)) (EuclideanSpace.single i (1 : ℝ))
        =
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          ((g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n)))
            (EuclideanSpace.single i (1 : ℝ))
          ∂((volume : Measure ℝ^n).toSphere) :=
    (ContinuousLinearMap.integral_apply (μ := (volume : Measure ℝ^n).toSphere) (φ := fun ω ↦
        (g (r • (ω : ℝ^n))) • EuclideanDistance.invDistPowFDerivFormula n x (r • (ω : ℝ^n))) hInt
      (EuclideanSpace.single i (1 : ℝ)))
  -- Finish by simplifying the scalar multiplication.
  simp [hCLM, happly, smul_eq_mul]

/-- Scalar formula for a repeated coordinate derivative of the singular sphere integral. -/
theorem secondPartial_sphereIntegral_div_distance_pow_scalar {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (i : Fin n) {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    (∂[i]
        (fun z : ℝ^n ↦
          (∂[i]
            (fun w : ℝ^n ↦
              PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist w y ^ n) 0 r)) z)) x =
      (|r| ^ (n - 1) : ℝ) *
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          g (r • (ω : ℝ^n)) *
            (let y : ℝ^n := r • (ω : ℝ^n)
             let d : ℝ := dist x y
             let t : ℝ := (x - y) i
             (-(n : ℝ)) / d ^ (n + 2) + (n : ℝ) * ((n + 2 : ℕ) : ℝ) * t ^ 2 / d ^ (n + 4))
          ∂((volume : Measure ℝ^n).toSphere) := by
  have hxy (ω : ↑(Metric.sphere (0 : ℝ^n) 1)) : x ≠ r • (ω : ℝ^n) := dist_ne_zero.mp
    (distance_ne_zero_of_mem_ball_mem_sphere hx (smul_unitSphere_mem_sphere hr.le ω))
  have hEq : (fun z ↦ (∂[i] (fun w : ℝ^n ↦
      PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist w y ^ n) 0 r)) z) =ᶠ[nhds x]
      fun z ↦ (|r| ^ (n - 1) : ℝ) * ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
        g (r • (ω : ℝ^n)) * EuclideanDistance.invDistPowFDerivFormula n z (r • (ω : ℝ^n))
          (EuclideanSpace.single i (1 : ℝ)) ∂((volume : Measure ℝ^n).toSphere) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact partialDeriv_sphereIntegral_div_distance_pow_scalar hr hg i hz
  have hint : Integrable (fun ω : ↑(Metric.sphere (0 : ℝ^n) 1) ↦ g (r • (ω : ℝ^n)) •
      EuclideanDistance.invDistPowSecondFDerivFormula n x (r • (ω : ℝ^n))
        (EuclideanSpace.single i 1)) ((volume : Measure ℝ^n).toSphere) := by
    have hd := EuclideanDistance.continuous_invDistPowFDerivFormula (n + 2) continuous_const
      (continuous_sphere_smul r) hxy
    refine integrableOn_univ.1 (Continuous.continuousOn ?_ |>.integrableOn_compact isCompact_univ)
    unfold EuclideanDistance.invDistPowSecondFDerivFormula
    exact (hg.comp_continuous (continuous_sphere_smul r) (smul_unitSphere_mem_sphere hr.le)).smul
      (by fun_prop (disch := exact fun ω ↦ pow_ne_zero _ (dist_ne_zero.mpr (hxy ω))))
  rw [PDE.partialDeriv_congr_nhds i hEq,
    partialDeriv_sphereIntegral_invDistPowFDeriv_apply hr hg i hx]
  congr 1
  refine (ContinuousLinearMap.integral_apply hint _).trans
    (integral_congr_ae (ae_of_all _ fun ω ↦ ?_))
  have hess := EuclideanLaplacian.fderiv_invDistPowFDeriv_apply_basis (k := n) i (hxy ω)
  rw [(EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply (hxy ω)).fderiv] at hess
  simp only [smul_apply, smul_eq_mul, hess]

end PoissonKernelLaplacian

end KernelLaplacian

end GreenFunction
