/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.CapLimit
public import PDE.Analysis.Calculus.PowerPotential.Classical
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.FDeriv.SpaceTime
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The terminal cap for the defocusing quintic wave

Physical energy controls both the L⁶ displacement and the L² velocity.
The shrinking-ball estimate therefore removes the terminal scaling-current
cap using only bounded local energy, with no regularity at the cone tip.

In step 1 of the proof of Evans, §12.4, Theorem 2, the top term is said to tend to zero as `τ → T`
without an argument; the shrinking-ball estimate supplies one.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, step 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric PDE.Common Set
open scoped ENNReal Topology

namespace WaveEquation

/-- A uniform bound on the quintic energy suffices to remove the
terminal cap. The two norm bounds are consequences of energy. -/
theorem tendsto_quintic_ballIntegral_scalingCurrentDensity_zero {u : ℝ^(3 + 1) → ℝ} (c : ℝ^3)
    (T E : ℝ) (hu : ∀ᶠ t in 𝓝[<] T, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (henergy : ∀ᶠ t in 𝓝[<] T, PDE.Analysis.ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity
      (Real.signedPowerPotential 5) u (timeSpaceCons t x)) c (T - t) ≤ E) :
    Tendsto (fun t ↦ PDE.Analysis.ballIntegral 3
      (fun x ↦ scalingCurrentDensity (Real.signedPowerPotential 5) 1
        (timeSpaceCons T c) u (timeSpaceCons t x)) c (T - t)) (𝓝[<] T) (𝓝 0) := by
  let V := Real.signedPowerPotential 5
  have hV : ContDiff ℝ 1 V :=
    Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hVpos : ∀ z, 0 ≤ V z :=
    Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have hVeq (z : ℝ) : V z = |z| ^ 6 / 6 := by
    norm_num [V, Real.signedPowerPotential, Real.rpow_ofNat]
  have hnorms : ∀ᶠ t in 𝓝[<] T, eLpNorm (fun x ↦ u (timeSpaceCons t x)) 6
          (volume.restrict (ball c (T - t))) ≤ ENNReal.ofReal ((6 * E) ^ (6 : ℝ)⁻¹) ∧
      lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2
          (volume.restrict (ball c (T - t))) ≤ (2 * E) ^ (2 : ℝ)⁻¹ := by
    filter_upwards [hu, henergy] with t hut he
    let U : ℝ^3 → ℝ := fun x ↦ u (timeSpaceCons t x)
    let v : ℝ^3 → ℝ := fun x ↦ (∂[0] u) (timeSpaceCons t x)
    let e : ℝ^3 → ℝ := fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)
    let μ := volume.restrict (ball c (T - t))
    have hs := (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
    have hU : Continuous U := continuous_iff_continuousAt.mpr fun x ↦
      (hut x).continuousAt.comp hs.continuousAt
    have hv : Continuous v := continuous_iff_continuousAt.mpr fun x ↦
      (PDE.contDiffAt_partialDeriv 1 (hut x) 0).continuousAt.comp hs.continuousAt
    have hec : Continuous e := continuous_iff_continuousAt.mpr fun x ↦
      (contDiffAt_semilinearWaveEnergyDensity (m := 1) hV.contDiffAt
        (hut x)).continuousAt.comp hs.continuousAt
    have hint {f : ℝ^3 → ℝ} (hf : Continuous f) : Integrable f μ :=
      (hf.continuousOn.integrableOn_compact (isCompact_closedBall c (T - t))).mono_set
        ball_subset_closedBall
    have hUm : MemLp U 6 μ := hU.continuousOn.memLp_of_subset_isCompact
      (isCompact_closedBall c (T - t)) measurableSet_ball ball_subset_closedBall
    have hle {f : ℝ^3 → ℝ} {k : ℝ} (hf : Integrable f μ) (hk : 0 ≤ k)
        (hpt : ∀ x, f x ≤ k * e x) : (∫ x, f x ∂μ) ≤ k * E :=
      (integral_mono hf ((hint hec).const_mul k) hpt).trans
        (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left he hk)
    have h6 : (∫ x, |U x| ^ 6 ∂μ) ≤ 6 * E := hle (hint (hU.abs.pow 6)) (by norm_num) fun x ↦ by
      have hkin := classicalWaveEnergyDensity_nonneg u (timeSpaceCons t x)
      dsimp [e, semilinearWaveEnergyDensity]
      rw [hVeq]
      change |U x| ^ 6 ≤ 6 * (classicalWaveEnergyDensity u (timeSpaceCons t x) + |U x| ^ 6 / 6)
      linarith
    have h2 : (∫ x, |v x| ^ 2 ∂μ) ≤ 2 * E := hle (hint (hv.abs.pow 2)) (by norm_num) fun x ↦ by
      have hp := hVpos (U x)
      have hg := sq_nonneg ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖
      dsimp [v, e, semilinearWaveEnergyDensity, classicalWaveEnergyDensity]
      rw [sq_abs]
      dsimp [U] at hp
      linarith
    constructor
    · rw [hUm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) h6 (by norm_num)
    · rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hv.aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs]
      exact Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) h2 (by norm_num)
  exact tendsto_ballIntegral_scalingCurrentDensity_zero hV hVpos c T E
    ((2 * E) ^ (2 : ℝ)⁻¹) (q := 6) (C := ENNReal.ofReal ((6 * E) ^ (6 : ℝ)⁻¹))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top hu henergy
    (hnorms.mono fun _ h ↦ h.1) (hnorms.mono fun _ h ↦ h.2)

end WaveEquation
