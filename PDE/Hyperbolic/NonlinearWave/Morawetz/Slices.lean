/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Current
public import PDE.Hyperbolic.NonlinearWave.Morawetz.InitialEnergy
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic

/-!
# Scaling current on a fixed time slice

The current is defined in spacetime coordinates, while its ball estimates use
ordinary spatial derivatives. These identities connect the two descriptions
without assuming regularity at the future cone tip.
-/

@[expose] public noncomputable section

open PDE.Common MeasureTheory Metric Set
open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- On a time slice, the scaling current is the dilation moment plus elapsed
time times the physical energy density. Only differentiability on that slice
is needed for this coordinate identity. -/
theorem scalingCurrentDensity_timeSlice {u : ℝ^(n + 1) → ℝ} (V : ℝ → ℝ)
    (a T t : ℝ) (c x : ℝ^n) (hu : DifferentiableAt ℝ u (timeSpaceCons t x)) :
    scalingCurrentDensity V a (timeSpaceCons T c) u (timeSpaceCons t x) =
      (t - T) * ((((∂[0] u) (timeSpaceCons t x)) ^ 2 +
        ‖fderiv ℝ (fun y ↦ u (timeSpaceCons t y)) x‖ ^ 2) / 2 +
          V (u (timeSpaceCons t x))) +
        (fderiv ℝ (fun y ↦ u (timeSpaceCons t y)) x (x - c) +
          a * u (timeSpaceCons t x)) * (∂[0] u) (timeSpaceCons t x) := by
  have hs : DifferentiableAt ℝ (fun y ↦ u (timeSpaceCons t y)) x :=
    hu.comp x (hasFDerivAt_timeSpaceCons_spatial n t x).differentiableAt
  have hnorm := PDE.norm_fderiv_sq_eq_sum_partialDeriv_sq hs
  simp_rw [PDE.partialDeriv_timeSpaceCons_spatial _ _ _ _ hu] at hnorm
  have hrad := PDE.fderiv_apply_eq_sum_partialDeriv_mul (fun y ↦ u (timeSpaceCons t y)) x (x - c)
  simp_rw [PDE.partialDeriv_timeSpaceCons_spatial _ _ _ _ hu, PiLp.sub_apply] at hrad
  have hsum : (∑ i : Fin n, (x i - c i) * (∂[i.succ] u) (timeSpaceCons t x)) =
      fderiv ℝ (fun y ↦ u (timeSpaceCons t y)) x (x - c) := by
    rw [hrad]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  simp only [scalingCurrentDensity, scalingMultiplier, waveLagrangianDensity,
    Fin.sum_univ_succ, timeSpaceCons_zero, timeSpaceCons_succ, hsum, ← hnorm]
  cas

/-- The initial-cap estimate for the spacetime scaling current. The
regularity assumptions concern the current time only, so this remains usable
when the cone's future tip is a possible singular time. -/
theorem ballIntegral_scalingCurrentDensity_le [Fact (0 < n)]
    {u : ℝ^(n + 1) → ℝ} {V : ℝ → ℝ} (hV : Continuous V) (T t : ℝ) (c : ℝ^n)
    (ht : t < T) (hu : ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x)) :
    PDE.Analysis.ballIntegral n
        (fun x ↦ scalingCurrentDensity V 1 (timeSpaceCons T c) u (timeSpaceCons t x))
        c (T - t) ≤
      -(T - t) * PDE.Analysis.ballIntegral n
          (fun x ↦ V (u (timeSpaceCons t x))) c (T - t) +
        PDE.Analysis.sphereIntegral n (fun x ↦ u (timeSpaceCons t x) ^ 2) c (T - t) / 2 -
          ((n : ℝ) - 1) / (2 * (T - t)) *
            PDE.Analysis.ballIntegral n (fun x ↦ u (timeSpaceCons t x) ^ 2) c (T - t) := by
  have hs : ContDiff ℝ 1 (fun x ↦ u (timeSpaceCons t x)) :=
    contDiff_iff_contDiffAt.mpr fun x ↦ ((hu x).of_le (by norm_num)).comp x
      (contDiff_timeSpaceCons_spatial n t).contDiffAt
  have hv : Continuous (fun x ↦ (∂[0] u) (timeSpaceCons t x)) := by
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    exact (PDE.contDiffAt_partialDeriv 1 (hu x) 0).continuousAt.comp
      (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have h := ballIntegral_scalingInitialDensity_le hs hv (hV.comp hs.continuous) c (sub_pos.mpr ht)
  simp only [Function.comp_def] at h
  convert h using 1
  congr 1
  funext x
  rw [scalingCurrentDensity_timeSlice V 1 T t c x ((hu x).differentiableAt (by norm_num))]
  simp only [one_mul, neg_sub]

end WaveEquation
