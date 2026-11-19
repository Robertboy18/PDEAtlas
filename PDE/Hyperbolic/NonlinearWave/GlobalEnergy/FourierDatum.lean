/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.InitialEnergyNorm
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import PDE.FDeriv.SpaceTime
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Fourier initial energy controlled by physical energy

Schwartz Cauchy traces identify the derivative and velocity terms.
A nonnegative potential then bounds the squared Fourier datum norm by twice
the integrable physical energy. This is a fixed-time comparison, not a
conservation theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE PDE.Common PDE.Analysis
open scoped SchwartzMap

namespace WaveEquation.Strichartz

/-- Schwartz traces convert integrable nonnegative-potential energy to
an initial Fourier datum bound. This is a fixed-time estimate, not conservation. -/
theorem norm_initialEnergyDatum_sq_le_two_mul_energy (g h : 𝓢(ℝ^3, ℝ)) {u : ℝ^4 → ℝ} (t : ℝ)
    (V : ℝ → ℝ) (hV : ∀ z, 0 ≤ V z) (hu : ∀ x : ℝ^3, DifferentiableAt ℝ u (timeSpaceCons t x))
    (hpos : ∀ x, u (timeSpaceCons t x) = g x) (hvel : ∀ x, (∂[0] u) (timeSpaceCons t x) = h x)
    (hi : Integrable (semilinearWaveSpatialEnergyDensity V u t)) :
    ‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM)‖ ^ 2 ≤
      2 * semilinearWaveSpatialEnergy V u t := by
  have hgrad (x : ℝ^3) : ‖fderiv ℝ g x‖ ^ 2 =
      ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2 := by
    rw [norm_fderiv_sq_eq_sum_partialDeriv_sq g.differentiableAt, EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hp : (∂[i] (g : ℝ^3 → ℝ)) x = (∂[i.succ] u) (timeSpaceCons t x) := by
      rw [← partialDeriv_timeSpaceCons_spatial i u t x (hu x)]
      exact congrArg (fun f : ℝ^3 → ℝ ↦ (∂[i] f) x) (funext hpos).symm
    simp only [hp, classicalWaveSpatialGradient_apply]
  have hd : MemLp (fderiv ℝ g) 2 volume := (SchwartzMap.fderivCLM ℝ (ℝ^3) ℝ g).memLp 2 volume
  have hgI : ∫ x, ‖fderiv ℝ g x‖ ^ 2 = lpNorm (fderiv ℝ g) 2 volume ^ 2 := by
    simpa only [lpNorm_norm hd.aestronglyMeasurable] using hd.norm.integral_sq_eq_lpNorm_sq
  have hhI := (h.memLp 2 volume).integral_sq_eq_lpNorm_sq
  have hgint := hd.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hhint := (h.memLp 2 volume).integrable_sq
  rw [norm_initialEnergyDatum_real_sq, ← hgI, ← hhI, ← integral_add hgint hhint]
  calc
    _ ≤ ∫ x, 2 * semilinearWaveSpatialEnergyDensity V u t x := by
      refine integral_mono (hgint.add hhint) (hi.const_mul 2) fun x ↦ ?_
      change ‖fderiv ℝ g x‖ ^ 2 + h x ^ 2 ≤ 2 * semilinearWaveSpatialEnergyDensity V u t x
      rw [hgrad x, ← hvel x]
      unfold semilinearWaveSpatialEnergyDensity semilinearWaveEnergyDensity
        classicalWaveEnergyDensity
      linarith [hV (u (timeSpaceCons t x))]
    _ = _ := by rw [integral_const_mul]; rfl

end WaveEquation.Strichartz
