/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Differentiation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Estimates
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Virial.Differentiation

/-!
# Virial and concavity inequalities for negative-energy waves

The potential-growth condition `z V'(z) ≤ Λ V(z)` converts the exact
quadratic-momentum derivative into a lower virial bound. For `Λ ≥ 2`,
Cauchy-Schwarz then gives a pointwise concavity inequality. Negative energy
and the strict condition `Λ > 2` are used later to obtain finite-time
continuation obstructions.

For the semilinear wave `uₜₜ - Δu + V'(u) = 0` with `I(t) = ½ ∫ u²`, `P = I'` and energy
`E = ∫ ½ uₜ² + ½ |Dₓu|² + V(u)`, the identity `P' = ∫ uₜ² + u uₜₜ` together with integration by
parts and the growth condition gives

`P'(t) ≥ ((Λ + 2) / 2) ∫ uₜ² + ((Λ - 2) / 2) ∫ |Dₓu|² - Λ E(t)`,

and the Cauchy-Schwarz bound `P² ≤ 2 I ∫ uₜ²` then yields
`(1 + (Λ - 2) / 4) P² ≤ I (P' + Λ E)`. This is the differential inequality of Levine's concavity
method: when `E < 0` and `Λ > 2` it says `I^{-(Λ - 2) / 4}` is concave, which is what produces
the finite lifespan in `NegativeEnergy.Lifespan`. The growth condition `z V'(z) ≤ Λ V(z)` is
the condition (2) of Evans, §12.5.1, Theorem 1, and implies Levine's hypothesis (*) with
`Λ = 2(2α + 1)`; for `V(z) = c z^{2k+2} / (2k+2)` it holds with `Λ = 2k + 2`.

## Main results

* `le_deriv_waveSpatialQuadraticMomentum_of_solution`: the virial lower bound on `P'(t)` at a
  time where the equation holds on the slice.
* `waveSpatialQuadraticMomentum_concavity_inequality`: the pointwise concavity inequality for
  `Λ ≥ 2`, valid for energy `E` of either sign.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, Theorem 1 and its proof, equations (2)-(7).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Section II,
  hypothesis (F-II), and the proof of Theorem I, equations (II-2)-(II-6), pp. 3-6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
* L. E. Payne and D. H. Sattinger, *Saddle points and instability of nonlinear hyperbolic
  equations*, Israel J. Math. 22 (1975), 273-303.
  <https://doi.org/10.1007/BF02761595>
-/

@[expose] public section

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace WaveEquation

variable {n : ℕ}

/-- On a compactly supported `C¹` slice, the squared spatial gradient is integrable. -/
private theorem integrable_sq_norm_spatialGradient {u : ℝ^(n + 1) → ℝ} (t : ℝ)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons t x))
    (hcompact : HasCompactSupport fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x)) :
    Integrable fun x : ℝ^n ↦
      ‖classicalWaveSpatialGradient u (PDE.Common.timeSpaceCons t x)‖ ^ 2 := by
  have hcont (i : Fin n) : Continuous fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (PDE.contDiffAt_partialDeriv 0 (hu x) i.succ).continuousAt.comp
        (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have hsupp (i : Fin n) :
      HasCompactSupport fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) := by
    convert hcompact.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ)) using 1
    funext x
    exact (PDE.partialDeriv_timeSpaceCons_spatial i u t x
      ((hu x).differentiableAt one_ne_zero)).symm
  have hsq (i : Fin n) : Integrable fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) ^ 2 := by
    simpa only [pow_two] using Continuous.integrable_of_hasCompactSupport (μ := volume)
      (f := fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) *
        (∂[i.succ] u) (PDE.Common.timeSpaceCons t x)) ((hcont i).mul (hcont i)) (hsupp i).mul_right
  refine (integrable_finsetSum univ fun i _ ↦ hsq i).congr (.of_forall fun x ↦ ?_)
  simp only [EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply]

/-- The potential-growth condition `z V'(z) ≤ Λ V(z)` gives the virial
lower bound

`((Λ + 2) / 2) ∫ uₜ² + ((Λ - 2) / 2) ∫ ‖Dₓu‖² - Λ E ≤ P'(t)`.

The identity for `P'(t)` comes from the wave equation and spatial integration
by parts. The energy decomposition then converts the potential term into the
displayed kinetic, gradient, and total-energy contributions. -/
theorem le_deriv_waveSpatialQuadraticMomentum_of_solution
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ} {Λ : ℝ}
    (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hwave : ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z) :
    ((Λ + 2) / 2) * (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) +
        ((Λ - 2) / 2) *
          (∫ x : ℝ^n, ‖classicalWaveSpatialGradient (n := n) u
            (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2) -
        Λ * semilinearWaveSpatialEnergy (n := n) V u t ≤
      deriv (waveSpatialQuadraticMomentum (n := n) u) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hvalue : Continuous fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hu t ht x).continuousAt.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have hpot : Integrable fun x : ℝ^n ↦ V (u (PDE.Common.timeSpaceCons t x)) :=
    (hV.continuous.comp hvalue).integrable_of_hasCompactSupport (hcompact.comp_left hVzero)
  have hprod : ∫ x : ℝ^n, u (PDE.Common.timeSpaceCons t x) *
      deriv V (u (PDE.Common.timeSpaceCons t x)) ≤
        Λ * ∫ x : ℝ^n, V (u (PDE.Common.timeSpaceCons t x)) := by
    rw [← integral_const_mul]
    exact integral_mono ((hvalue.mul (hV.continuous_deriv_one.comp hvalue)
      ).integrable_of_hasCompactSupport hcompact.mul_right) (hpot.const_mul Λ) fun x ↦ hgrowth _
  have henergy := semilinearWaveSpatialEnergy_eq_integral_components V u t
    ((integrable_sq_time_deriv_of_quadratic_momentum_domination hu hs hcompact hdominated
      hboundIntegrable).const_mul (1 / 2 : ℝ))
    ((integrable_sq_norm_spatialGradient t (fun x ↦ (hu t ht x).of_le (by norm_num))
      hcompact).const_mul (1 / 2 : ℝ)) hpot
  simp only [semilinearWaveSpatialKineticEnergyDensity, semilinearWaveSpatialGradientEnergyDensity,
    semilinearWaveSpatialPotentialEnergyDensity, integral_const_mul] at henergy
  rw [(hasDerivAt_waveSpatialQuadraticMomentum_of_solution hV hu hs hcompact hdominated
    hboundIntegrable hwave).deriv, henergy]
  linarith

/-- For `Λ ≥ 2`, the quadratic mass and momentum satisfy
the pointwise concavity inequality

`(1 + (Λ - 2) / 4) P(t)² ≤ I(t) (P'(t) + Λ E(t))`.

The proof combines the virial lower bound with Cauchy-Schwarz and
nonnegativity of the quadratic mass. The energy may have either sign. -/
theorem waveSpatialQuadraticMomentum_concavity_inequality
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ} {s : Set ℝ} {bound : ℝ^n → ℝ} {Λ : ℝ}
    (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V)
    (hu : ∀ r ∈ s, ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hΛ : 2 ≤ Λ) (hs : s ∈ 𝓝 t)
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (hdominated : ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ bound x)
    (hboundIntegrable : Integrable bound)
    (hwave : ∀ x : ℝ^n,
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z) :
    (1 + (Λ - 2) / 4) * waveSpatialQuadraticMomentum (n := n) u t ^ 2 ≤
      waveSpatialQuadraticMass (n := n) u t *
        (deriv (waveSpatialQuadraticMomentum (n := n) u) t +
          Λ * semilinearWaveSpatialEnergy (n := n) V u t) := by
  have hsq := waveSpatialQuadraticMomentum_sq_le t
    (fun x ↦ (hu t (mem_of_mem_nhds hs) x).of_le (by norm_num)) hcompact
    (integrable_sq_time_deriv_of_quadratic_momentum_domination hu hs hcompact hdominated
      hboundIntegrable)
  have hlow := le_deriv_waveSpatialQuadraticMomentum_of_solution hVzero hV hu hs hcompact
    hdominated hboundIntegrable hwave hgrowth
  have hG : 0 ≤ ∫ x : ℝ^n, ‖classicalWaveSpatialGradient u (PDE.Common.timeSpaceCons t x)‖ ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hI : 0 ≤ waveSpatialQuadraticMass u t :=
    integral_nonneg fun x ↦ mul_nonneg (by norm_num) (sq_nonneg _)
  linarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ (Λ + 2) / 4),
    mul_nonneg hI (mul_nonneg (sub_nonneg.2 hΛ) hG), mul_le_mul_of_nonneg_left hlow hI]

end WaveEquation
