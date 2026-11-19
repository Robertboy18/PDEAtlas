/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Differentiating the quadratic mass of a semilinear wave

We prove the first- and second-derivative formulas

`I'(t) = ∫ u uₜ`,  `I''(t) = ∫ (uₜ² + u uₜₜ)`

for the quadratic mass `I(t) = ½ ∫ u(t, x)² dx` and the quadratic momentum `P = I'`, under
explicit local domination hypotheses. Compact support is used only for fixed-time spatial
integrability; differentiation under the integral requires a common integrable dominator on a
neighborhood of the base time. These are the two derivatives of the functional on which Levine's
concavity method for negative-energy blowup is built, and the second gives (4) in the proof of
Evans, §12.5.1, Theorem 1.

## Main results

* `hasDerivAt_waveSpatialQuadraticMass`: `I'(t) = P(t)`.
* `hasDerivAt_waveSpatialQuadraticMomentum`: `P'(t) = ∫ (uₜ² + u uₜₜ)`.
* `integrable_sq_time_deriv_of_quadratic_momentum_domination`: the dominator used to
  differentiate `∫ u uₜ` also makes `uₜ(t, ·)²` integrable on the slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, equation (4).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, proof of Theorem I,
  equation (II-2) and the formulas after it, pp. 5-6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A field continuous at every point of a time slice is continuous along the slice. -/
private theorem continuous_slice {f : ℝ^(n + 1) → ℝ} {r : ℝ}
    (hf : ∀ x : ℝ^n, ContinuousAt f (PDE.Common.timeSpaceCons r x)) :
    Continuous fun x : ℝ^n ↦ f (PDE.Common.timeSpaceCons r x) :=
  continuous_iff_continuousAt.mpr fun x ↦ (hf x).comp
    (PDE.Common.contDiff_timeSpaceCons_spatial n r (m := 1)).continuous.continuousAt

/-- The time derivative of the quadratic mass density `u² / 2` at a fixed point. -/
private theorem hasDerivAt_waveSpatialQuadraticMass_integrand {u : ℝ^(n + 1) → ℝ} (t : ℝ)
    (x : ℝ^n) (hu : ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    HasDerivAt (fun r ↦ (1 / 2 : ℝ) * u (PDE.Common.timeSpaceCons (n := n) r x) ^ 2)
      (u (PDE.Common.timeSpaceCons (n := n) t x) * (∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x))
      t := by
  have h := PDE.hasDerivAt_timeSpaceCons u t x (hu.differentiableAt one_ne_zero)
  simpa only [Pi.mul_apply, pow_two] using ((h.mul h).const_mul (1 / 2 : ℝ)).congr_deriv (by ring)

/-- Differentiate the spatial quadratic mass under the integral.

The compact-support hypothesis supplies integrability of the mass density at
the base time. Regularity and the integrable dominator for `u uₜ` are needed
only on the same common time neighborhood. -/
theorem hasDerivAt_waveSpatialQuadraticMass {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ}
    {bound : ℝ^n → ℝ}
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound) :
    HasDerivAt (waveSpatialQuadraticMass (n := n) u) (waveSpatialQuadraticMomentum (n := n) u t)
      t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hv (r : ℝ) (hr : r ∈ s) := continuous_slice fun x ↦ (hu r hr x).continuousAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x ↦ (1 / 2 : ℝ) * u (PDE.Common.timeSpaceCons r x) ^ 2)
    (F' := fun r x ↦ u (PDE.Common.timeSpaceCons r x) * (∂[0] u) (PDE.Common.timeSpaceCons r x))
    hs (by
      filter_upwards [hs] with r hr
      exact (continuous_const.mul ((hv r hr).pow 2)).aestronglyMeasurable)
    (by simpa [pow_two] using (((hv t ht).mul (hv t ht)).integrable_of_hasCompactSupport
      (μ := volume) hcompact.mul_right).const_mul (1 / 2 : ℝ))
    ((hv t ht).mul (continuous_slice fun x ↦
      (PDE.contDiffAt_partialDeriv 0 (hu t ht x) 0).continuousAt)).aestronglyMeasurable
    (by simpa only [waveSpatialQuadraticMomentumDensity] using hdominated) hboundIntegrable
    (.of_forall fun x r hr ↦ hasDerivAt_waveSpatialQuadraticMass_integrand r x (hu r hr x))).2

/-- The time derivative of the quadratic momentum density `u uₜ` at a fixed point. -/
private theorem hasDerivAt_waveSpatialQuadraticMomentum_integrand {u : ℝ^(n + 1) → ℝ} (t : ℝ)
    (x : ℝ^n) (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x)) :
    HasDerivAt
      (fun r ↦ u (PDE.Common.timeSpaceCons (n := n) r x) *
        (∂[0] u) (PDE.Common.timeSpaceCons (n := n) r x))
      (((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
        u (PDE.Common.timeSpaceCons (n := n) t x) *
          (∂[0] (fun p ↦ (∂[0] u) p)) (PDE.Common.timeSpaceCons (n := n) t x)) t := by
  have huAt := hu.differentiableAt (by norm_num)
  have hpAt := (PDE.contDiffAt_partialDeriv 1 hu 0).differentiableAt one_ne_zero
  have hcurve := PDE.hasDerivAt_timeSpaceCons (fun p ↦ u p * (∂[0] u) p) t x (huAt.mul hpAt)
  rw [PDE.partialDeriv_mul (i := 0) huAt hpAt] at hcurve
  simpa only [pow_two] using hcurve

/-- The quadratic momentum is differentiable, with integrable derivative density. -/
private theorem hasDerivAt_waveSpatialQuadraticMomentum_and_integrable_derivative
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ}
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound) :
    Integrable (fun x : ℝ^n ↦ ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      u (PDE.Common.timeSpaceCons (n := n) t x) *
        (∂[0] (fun p ↦ (∂[0] u) p)) (PDE.Common.timeSpaceCons (n := n) t x)) ∧
      HasDerivAt (waveSpatialQuadraticMomentum (n := n) u)
        (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
          u (PDE.Common.timeSpaceCons (n := n) t x) *
            (∂[0] (fun p ↦ (∂[0] u) p)) (PDE.Common.timeSpaceCons (n := n) t x)) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hv (r : ℝ) (hr : r ∈ s) := continuous_slice fun x ↦ (hu r hr x).continuousAt
  have hd (r : ℝ) (hr : r ∈ s) :=
    continuous_slice fun x ↦ (PDE.contDiffAt_partialDeriv 1 (hu r hr x) 0).continuousAt
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r x ↦ u (PDE.Common.timeSpaceCons r x) * (∂[0] u) (PDE.Common.timeSpaceCons r x))
    hs (by
      filter_upwards [hs] with r hr
      exact ((hv r hr).mul (hd r hr)).aestronglyMeasurable)
    (((hv t ht).mul (hd t ht)).integrable_of_hasCompactSupport (μ := volume) hcompact.mul_right)
    ((((hd t ht).pow 2).add ((hv t ht).mul (continuous_slice fun x ↦ (PDE.contDiffAt_partialDeriv
      0 (PDE.contDiffAt_partialDeriv 1 (hu t ht x) 0) 0).continuousAt))).aestronglyMeasurable)
    (by simpa only [waveSpatialQuadraticMomentumDerivativeDensity] using hdominated)
    hboundIntegrable
    (.of_forall fun x r hr ↦ hasDerivAt_waveSpatialQuadraticMomentum_integrand r x (hu r hr x))

/-- Differentiate the quadratic momentum under the spatial integral.

This is the analytic second-derivative formula for the quadratic mass:

`I''(t) = ∫ (uₜ² + u uₜₜ)`.

The term `u uₜ` is integrable because the compactly supported factor is `u`.
Integrability of the displayed second-derivative density follows from the
local integrable dominator. -/
theorem hasDerivAt_waveSpatialQuadraticMomentum {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ}
    {bound : ℝ^n → ℝ}
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound) :
    HasDerivAt (waveSpatialQuadraticMomentum (n := n) u)
      (∫ x : ℝ^n, waveSpatialQuadraticMomentumDerivativeDensity (n := n) u t x) t :=
  (hasDerivAt_waveSpatialQuadraticMomentum_and_integrable_derivative hu hs hcompact hdominated
    hboundIntegrable).2

/-- The local domination needed to differentiate `∫ u uₜ` also makes
`uₜ²` integrable on the base-time slice.

Indeed, the dominated derivative density is `uₜ² + u uₜₜ`, while the second
term is integrable because its first factor is compactly supported. -/
theorem integrable_sq_time_deriv_of_quadratic_momentum_domination
    {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ}
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound) :
    Integrable fun x : ℝ^n ↦ ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  refine ((hasDerivAt_waveSpatialQuadraticMomentum_and_integrable_derivative hu hs hcompact
    hdominated hboundIntegrable).1.sub (((continuous_slice fun x ↦ (hu t ht x).continuousAt).mul
      (continuous_slice fun x ↦ (PDE.contDiffAt_partialDeriv 0 (PDE.contDiffAt_partialDeriv 1
        (hu t ht x) 0) 0).continuousAt)).integrable_of_hasCompactSupport (μ := volume)
          hcompact.mul_right)).congr (.of_forall fun x ↦ ?_)
  simp only [Pi.sub_apply, Pi.mul_apply, add_sub_cancel_right]

end WaveEquation
