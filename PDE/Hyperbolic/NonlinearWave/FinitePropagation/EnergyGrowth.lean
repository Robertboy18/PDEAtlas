/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Basic
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Transport

/-!
# Growth of semilinear energy on shrinking cones

If the energy-balance residual is at most `C` times the energy density on a
backward cone, the cone energy grows at most like `exp (C (t - a))`. The potential
need only be nonnegative at the values the field takes on the closed cone. This
covers a potential plus a quadratic term that is nonnegative on a compact range of
values.

The proof combines the cone transport identity with Gronwall's inequality. The
residual bound is assumed on `[a, T)`, so the derivative estimate also holds at the
initial time.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation

variable {n : ℕ}

/-- A residual bound controls the derivative of cone energy when the potential is
nonnegative at the field values on the closed spatial slice. -/
theorem deriv_semilinearBackwardConeEnergy_le [Fact (0 < n)] {W : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hW : ContDiff ℝ 1 W) (hu : ContDiff ℝ 2 u) (c : ℝ^n) (T : ℝ) {t C : ℝ} (ht : t < T)
    (hWnonneg : ∀ x ∈ Metric.closedBall c (T - t), 0 ≤ W (u (timeSpaceCons t x)))
    (hbound : ∀ x ∈ Metric.ball c (T - t), semilinearWaveEnergyBalanceResidual W u
      (timeSpaceCons t x) ≤ C * semilinearWaveEnergyDensity W u (timeSpaceCons t x)) :
    deriv (semilinearBackwardConeEnergy W u c T) t ≤
      C * semilinearBackwardConeEnergy W u c T t := by
  have hspace : Continuous (timeSpaceCons (n := n) t) :=
    (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hresidual : Continuous (fun x : ℝ^n ↦
      semilinearWaveEnergyBalanceResidual W u (timeSpaceCons t x)) :=
    (contDiff_semilinearWaveEnergyBalanceResidual (m := 0) hW hu).continuous.comp hspace
  have hdensity : Continuous (fun x : ℝ^n ↦ semilinearWaveEnergyDensity W u (timeSpaceCons t x)) :=
    (contDiff_semilinearWaveEnergyDensity (m := 0)
      (hW.of_le (by norm_num)) (hu.of_le (by norm_num))).continuous.comp hspace
  have hintegrable (f : ℝ^n → ℝ) (hf : Continuous f) : IntegrableOn f (Metric.ball c (T - t)) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
      Metric.ball_subset_closedBall
  have hvolume : ballIntegral n (fun x ↦
          semilinearWaveEnergyBalanceResidual W u (timeSpaceCons t x)) c (T - t) ≤
        C * ballIntegral n (fun x ↦
          semilinearWaveEnergyDensity W u (timeSpaceCons t x)) c (T - t) := by
    unfold ballIntegral
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hintegrable _ hresidual)
      ((hintegrable _ hdensity).const_mul C) measurableSet_ball hbound
  have hflux :
      sphereIntegral n (semilinearWaveConeBoundaryFlux W u c t) c (T - t) ≤ 0 := by
    refine sphereIntegral_nonpos fun y hy ↦ ?_
    have hy' : y ∈ Metric.sphere c (T - t) := by
      simpa only [abs_of_pos (sub_pos.mpr ht)] using hy
    unfold semilinearWaveConeBoundaryFlux
    exact sub_nonpos.mpr ((classicalWaveConeBoundaryFlux_nonpos
      (t := t) u c y (sub_pos.mpr ht) hy').trans (hWnonneg y (Metric.sphere_subset_closedBall hy')))
  rw [(hasDerivAt_semilinearBackwardConeEnergy hW hu c T ht).deriv,
    semilinearBackwardConeEnergy_eq_ballIntegral hW.continuous
      (hu.of_le (by norm_num)) c T t]
  exact (add_le_of_nonpos_right hflux).trans hvolume

/-- Under the pointwise residual bound `≤ C · density` on `[a, T)`, the cone energy at
time `t` is at most its value at `a` times `exp (C (t - a))`. The constant `C` may have
either sign. -/
theorem semilinearBackwardConeEnergy_le_exp [Fact (0 < n)] {W : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hW : ContDiff ℝ 1 W) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T C : ℝ}
    (hWnonneg : ∀ s ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - s), 0 ≤ W (u (timeSpaceCons s x)))
    (hbound : ∀ s ∈ Ico a T, ∀ x ∈ Metric.ball c (T - s), semilinearWaveEnergyBalanceResidual W u
      (timeSpaceCons s x) ≤ C * semilinearWaveEnergyDensity W u (timeSpaceCons s x))
    {t : ℝ} (ht : t ∈ Ico a T) :
    semilinearBackwardConeEnergy W u c T t ≤
      semilinearBackwardConeEnergy W u c T a * Real.exp (C * (t - a)) := by
  have hderiv (s : ℝ) (hs : s ∈ Icc a t) : HasDerivWithinAt (semilinearBackwardConeEnergy W u c T)
        (deriv (semilinearBackwardConeEnergy W u c T) s) (Icc a t) s :=
    (hasDerivAt_semilinearBackwardConeEnergy hW hu c T
      (hs.2.trans_lt ht.2)).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hgrowth (s : ℝ) (hs : s ∈ Icc a t) : deriv (semilinearBackwardConeEnergy W u c T) s ≤
        C * semilinearBackwardConeEnergy W u c T s + 0 := by
    have hsT : s ∈ Ico a T := ⟨hs.1, hs.2.trans_lt ht.2⟩
    simpa only [add_zero] using deriv_semilinearBackwardConeEnergy_le hW hu c T hsT.2
        (hWnonneg s ⟨hs.1, hsT.2.le⟩) (hbound s hsT)
  have hgronwall := PDE.Analysis.Evolution.le_gronwallBound_of_hasDerivWithinAt_le
    hderiv le_rfl hgrowth t ⟨ht.1, le_rfl⟩
  simpa only [gronwallBound_ε0] using hgronwall

end WaveEquation
