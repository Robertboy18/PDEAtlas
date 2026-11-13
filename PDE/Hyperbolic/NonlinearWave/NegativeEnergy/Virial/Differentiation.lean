/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Differentiation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Virial.IntegrationByParts

/-!
# The quadratic-momentum derivative for semilinear waves

For a classical semilinear wave, differentiation under the spatial integral
and spatial integration by parts give

`P'(t) = ∫ uₜ² - ∫ ‖Dₓu‖² - ∫ u V'(u)`.

All integrability and local domination assumptions needed for this identity
remain explicit.

This is the identity (4) in the proof of Evans, §12.5.1, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, equation (4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace WaveEquation

variable {n : ℕ}

/-- For a classical semilinear wave, the derivative of the quadratic
momentum is

`∫ uₜ² - ∫ ‖Dₓu‖² - ∫ u V'(u)`.

The local domination hypothesis justifies time differentiation and also
supplies integrability of `uₜ²`. Compact support of `u(t, ·)` handles the
spatial Laplacian and potential terms. -/
theorem hasDerivAt_waveSpatialQuadraticMomentum_of_solution
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ}
    (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hwave : ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0) :
    HasDerivAt (waveSpatialQuadraticMomentum (n := n) u)
      ((∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) -
        (∫ x : ℝ^n, ‖classicalWaveSpatialGradient (n := n) u
          (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2) -
        ∫ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) *
          deriv V (u (PDE.Common.timeSpaceCons (n := n) t x))) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hcont {f : ℝ^(n + 1) → ℝ} (hf : ∀ x : ℝ^n, ContinuousAt f (PDE.Common.timeSpaceCons t x)) :
      Continuous fun x : ℝ^n ↦ f (PDE.Common.timeSpaceCons t x) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hf x).comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have hvalue := hcont fun x ↦ (hu t ht x).continuousAt
  have hlap : Integrable fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x) *
      ∑ i : Fin n, (∂[i.succ] fun p ↦ (∂[i.succ] u) p) (PDE.Common.timeSpaceCons t x) :=
    (hvalue.mul (continuous_finsetSum _ fun i _ ↦ hcont fun x ↦ (PDE.contDiffAt_partialDeriv 0
      (PDE.contDiffAt_partialDeriv 1 (hu t ht x) i.succ) i.succ).continuousAt)
      ).integrable_of_hasCompactSupport (μ := volume) hcompact.mul_right
  have hpot : Integrable fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x) *
      deriv V (u (PDE.Common.timeSpaceCons t x)) :=
    (hvalue.mul (hV.continuous_deriv_one.comp hvalue)).integrable_of_hasCompactSupport
      (μ := volume) hcompact.mul_right
  have hk := integrable_sq_time_deriv_of_quadratic_momentum_domination hu hs hcompact hdominated
    hboundIntegrable
  refine (hasDerivAt_waveSpatialQuadraticMomentum hu hs hcompact hdominated
    hboundIntegrable).congr_deriv ?_
  rw [neg_eq_iff_eq_neg.mp (integral_mul_sum_spatial_secondDeriv_eq_neg_gradient_sq t
    (hu t ht) hcompact).symm, sub_neg_eq_add, ← integral_add hk hlap,
    ← integral_sub (by exact hk.add hlap) hpot]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have h := hwave x
  simp only [semilinearWaveOperator, waveOperator] at h
  simp only [waveSpatialQuadraticMomentumDerivativeDensity]
  linear_combination u (PDE.Common.timeSpaceCons t x) * h

end WaveEquation
