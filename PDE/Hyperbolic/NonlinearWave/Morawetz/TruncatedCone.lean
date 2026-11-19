/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.Integration.Cone.LocalDivergence
public import PDE.Hyperbolic.NonlinearWave.Morawetz.Power
import PDE.Analysis.Calculus.PowerPotential.Classical
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The quintic Morawetz balance on a truncated cone

Integrating the scaling current gives the two cap terms and the lateral flux,
with Euclidean Hausdorff normalization 1/√2. The off-shell identity retains the
wave residual; the on-shell consequence assumes the quintic wave equation
inside the truncated cone. Both require smoothness only on an open time band,
without an extension or limiting value at the apex. A vertex limit is separate.

This is the integration of (6) over the truncated cone in step 1 of the proof of Evans, §12.4,
Theorem 2, which leads to (9).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, step 1, equations (6)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

open Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace WaveEquation

/-- The integrated quintic scaling-current balance, retaining its wave residual.
The field is C² only on an open time band; neither cap is at the cone vertex. -/
theorem integral_morawetzCurrent_balance_quintic (c : ℝ^3)
    {s₀ s τ T : ℝ} (hs : s₀ < s) (hsτ : s ≤ τ) (hτ : τ < T)
    {u : ℝ^(3 + 1) → ℝ} (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) :
    (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      scalingMultiplier 1 (timeSpaceCons T c) u (timeSpaceCons t x) *
        semilinearWaveOperator (Real.signedPowerPotential 5) u (timeSpaceCons t x) -
          u (timeSpaceCons t x) ^ 6 / 3) =
      (∫ x in Metric.ball c (T - τ),
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons τ x)) -
      (∫ x in Metric.ball c (T - s),
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons s x)) +
        (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
          (scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u p -
            ⟪WithLp.toLp 2 (fun i ↦
              scalingCurrentFlux (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u i p),
              NormedSpace.normalize (spatialPart p - c)⟫)
            ∂Measure.euclideanHausdorffMeasure 3) := by
  let P := scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
  let Q (p : ℝ^(3 + 1)) : ℝ^3 := WithLp.toLp 2 (fun i ↦
    scalingCurrentFlux (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u i p)
  have hV := Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hopen : IsOpen {p : ℝ^(3 + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hP : ContDiffOn ℝ 1 P {p | s₀ < p 0 ∧ p 0 < T} := by
    intro p hp
    exact (contDiffAt_scalingCurrentDensity 1 (timeSpaceCons T c) hV.contDiffAt
      (hu.contDiffAt (hopen.mem_nhds hp))).contDiffWithinAt
  have hQ : ContDiffOn ℝ 1 Q {p | s₀ < p 0 ∧ p 0 < T} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_piLp 2).mpr
    intro i
    exact contDiffAt_scalingCurrentFlux 1 (timeSpaceCons T c) hV.contDiffAt
      (hu.contDiffAt (hopen.mem_nhds hp)) i
  have hres (t : ℝ) (ht : t ∈ Ioo s₀ T) (x : ℝ^3) :
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x =
        scalingMultiplier 1 (timeSpaceCons T c) u (timeSpaceCons t x) *
          semilinearWaveOperator (Real.signedPowerPotential 5) u (timeSpaceCons t x) -
            u (timeSpaceCons t x) ^ 6 / 3 := by
    have hup := hu.contDiffAt (hopen.mem_nhds
      (show s₀ < (timeSpaceCons t x) 0 ∧ (timeSpaceCons t x) 0 < T by
        simpa only [mem_Ioo, timeSpaceCons_zero] using ht))
    rw [← morawetzCurrent_balance_quintic (timeSpaceCons T c) hup]
    congr 1
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    exact partialDeriv_timeSpaceCons_spatial i _ t x
      ((contDiffAt_scalingCurrentFlux 1 (timeSpaceCons T c) hV.contDiffAt hup i).differentiableAt
        one_ne_zero)
  calc
    _ = ∫ t in s..τ, ∫ x in Metric.ball c (T - t),
        (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hsτ] at ht
      apply integral_congr_ae
      filter_upwards with x
      exact (hres t ⟨hs.trans_le ht.1, ht.2.trans_lt hτ⟩ x).symm
    _ = _ := integral_divergence_truncatedCone_of_contDiffOn_band hP hQ c hs hsτ hτ

/-- For a solution of `uₜₜ - Δu + u⁵ = 0`, the volume term is `-u⁶/3`.
The equation is needed only inside the spatial balls between the two cap times. -/
theorem integral_morawetzCurrent_balance_quintic_of_wave (c : ℝ^3) {s₀ s τ T : ℝ} (hs : s₀ < s)
    (hsτ : s ≤ τ) (hτ : τ < T) {u : ℝ^(3 + 1) → ℝ} (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      -(u (timeSpaceCons t x) ^ 6 / 3)) =
      (∫ x in Metric.ball c (T - τ),
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons τ x)) -
      (∫ x in Metric.ball c (T - s),
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons s x)) +
        (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
          (scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u p -
            ⟪WithLp.toLp 2 (fun i ↦
              scalingCurrentFlux (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u i p),
              NormedSpace.normalize (spatialPart p - c)⟫)
            ∂Measure.euclideanHausdorffMeasure 3) := by
  rw [← integral_morawetzCurrent_balance_quintic c hs hsτ hτ hu]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hsτ] at ht
  apply setIntegral_congr_fun measurableSet_ball
  intro x hx
  have hderiv : deriv (Real.signedPowerPotential 5) (u (timeSpaceCons t x)) =
      u (timeSpaceCons t x) ^ 5 := by
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast]
    rw [(show Even 4 by decide).pow_abs]
    cas
  have hres : semilinearWaveOperator (Real.signedPowerPotential 5) u
      (timeSpaceCons t x) = 0 := by
    rw [semilinearWaveOperator, hderiv]
    exact hwave t ht x hx
  dsimp only
  rw [hres, mul_zero, zero_sub]

end WaveEquation
