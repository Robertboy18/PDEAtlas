/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Analysis.MeasureTheory.Lp.IntegralPower
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity.Finset

/-!
# Continuity and decay of L4 time tails

Finite L4 integrability on a bounded interval gives continuous tail norms
and a zero limit at the terminal endpoint. Endpoint values do not affect
these Lebesgue integrals.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- Fourth-power tail norms are continuous on a finite interval. -/
theorem continuousOn_lpNorm_restrict_tail_four {f : ℝ → ℝ} {s T : ℝ}
    (hsT : s ≤ T) (hf : Measurable f)
    (hlocal : MemLp f 4 (volume.restrict (Icc s T))) :
    ContinuousOn (fun r ↦ lpNorm f 4 (volume.restrict (Icc r T))) (Icc s T) := by
  have hp := hlocal.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hc := intervalIntegral.continuousOn_primitive_interval_left (a := s) (b := T)
    (f := fun x ↦ ‖f x‖ ^ 4) (μ := volume)
    (by simpa only [uIcc_of_le hsT, IntegrableOn] using hp)
  have hc' := hc.rpow_const
    (fun _ _ ↦ Or.inr (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹))
  rw [uIcc_of_le hsT] at hc'
  apply hc'.congr
  intro r hr
  dsimp only
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [intervalIntegral.integral_of_le hr.2, integral_Icc_eq_integral_Ioc]

/-- Finite critical time integrability gives a vanishing terminal tail,
without a terminal value or terminal regularity assumption. -/
theorem tendsto_lpNorm_restrict_tail_four {f : ℝ → ℝ} {s T : ℝ}
    (hsT : s < T) (hf : Measurable f)
    (hlocal : MemLp f 4 (volume.restrict (Ico s T))) :
    Tendsto (fun r ↦ lpNorm f 4 (volume.restrict (Icc r T))) (𝓝[<] T) (𝓝 0) := by
  have hlocal' : MemLp f 4 (volume.restrict (Icc s T)) := by
    simpa only [restrict_Ico_eq_restrict_Icc] using hlocal
  have hc := continuousOn_lpNorm_restrict_tail_four hsT.le hf hlocal' T
    (right_mem_Icc.mpr hsT.le)
  rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hsT] at hc
  have hlim := hc.mono_left (nhdsWithin_mono T Iio_subset_Iic_self)
  simpa [Icc_self, Measure.restrict_singleton, lpNorm] using hlim

end MeasureTheory
