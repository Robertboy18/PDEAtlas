/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.Hyperbolic.Models.Wave.DAlembert.ClassicalSolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Potential
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.IntegrationTactic

/-!
# Growth of the displacement of a free wave

A nonnegative compactly supported initial velocity produces an expanding plateau in one space
dimension. Its displacement has unbounded squared L² norm, even though the velocity is smooth and
the physical wave energy stays finite.

The example concerns the bound `u ∈ L^∞((0,∞); H¹(ℝⁿ))` in the conclusion of Evans, §12.3.1,
Theorem 1. The reaction in this example is zero and satisfies the sign condition (2), and the data
satisfy the hypotheses of that theorem, but for `n = 1` the L² norm of the displacement is not
bounded in time. Evans's proof gives the L² bound (7) on each finite time interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, Theorem 1 and its proof, equation (7).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal
open PDE.Analysis (primitive continuous_primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Smooth initial velocity equal to one on `[-1,1]` and zero outside `[-2,2]`. -/
def freeWaveVelocity : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The free wave with zero initial displacement and a compact positive velocity. -/
def freeWave (t x : ℝ) : ℝ :=
  WaveEquation.dAlembertFormula (fun _ ↦ 0) freeWaveVelocity x t

/-- The initial velocity belongs to L². -/
theorem memLp_freeWaveVelocity : MemLp (freeWaveVelocity : ℝ → ℝ) 2 volume :=
  freeWaveVelocity.continuous.memLp_of_hasCompactSupport freeWaveVelocity.hasCompactSupport

/-- The example is a classical spacetime field. -/
theorem contDiff_freeWave : ContDiff ℝ 2 (fun p : ℝ^2 ↦ freeWave (p 0) (p 1)) :=
  WaveEquation.contDiff_two_dAlembertFormula _ _ contDiff_const freeWaveVelocity.contDiff

/-- The field satisfies the homogeneous wave equation. -/
theorem waveOperator_freeWave (p : ℝ^2) :
    WaveEquation.waveOperator (n := 1) (fun q ↦ freeWave (q 0) (q 1)) p = 0 :=
  WaveEquation.waveOperator_dAlembertFormula _ _ contDiff_const freeWaveVelocity.contDiff p

/-- The initial displacement vanishes. -/
@[simp] theorem freeWave_zero (x : ℝ) : freeWave 0 x = 0 := by
  simp [freeWave, WaveEquation.dAlembertFormula]

/-- The initial time derivative is the prescribed smooth velocity. -/
theorem partialDeriv_freeWave_zero (x : ℝ^1) :
    (∂[(0 : Fin 2)] (fun q : ℝ^2 ↦ freeWave (q 0) (q 1))) (timeSpaceCons 0 x) =
      freeWaveVelocity (x 0) := by
  unfold freeWave
  rw [WaveEquation.partialDeriv_dAlembert_time _ _ contDiff_const freeWaveVelocity.contDiff]
  have hspace : timeSpaceCons 0 x (1 : Fin 2) = x 0 := timeSpaceCons_succ 0 x (0 : Fin 1)
  simp only [one_div, Fin.isValue, hspace, timeSpaceCons_zero, add_zero, deriv_const', sub_zero,
    sub_self, mul_zero, zero_add]
  ring

/-- At each fixed time the displacement is continuous. -/
theorem continuous_freeWave (t : ℝ) : Continuous (freeWave t) := by
  have heq (x : ℝ) : freeWave t x = (1 / 2 : ℝ) *
      (primitive freeWaveVelocity (x + t) - primitive freeWaveVelocity (x - t)) := by
    unfold freeWave WaveEquation.dAlembertFormula primitive
    rw [intervalIntegral.integral_interval_sub_left
      (freeWaveVelocity.continuous.intervalIntegrable 0 (x + t))
      (freeWaveVelocity.continuous.intervalIntegrable 0 (x - t))]
    simp
  change Continuous (fun x ↦ freeWave t x)
  simp_rw [heq]
  exact continuous_const.mul (((continuous_primitive freeWaveVelocity.continuous).comp
      (continuous_id.add continuous_const)).sub
      ((continuous_primitive freeWaveVelocity.continuous).comp
        (continuous_id.sub continuous_const)))

/-- Finite propagation makes every nonnegative-time displacement compactly supported. -/
theorem hasCompactSupport_freeWave {t : ℝ} (ht : 0 ≤ t) :
    HasCompactSupport (freeWave t) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(t + 2)) (b := t + 2))
  intro x hx
  apply WaveEquation.dAlembertFormula_eq_zero_of_vanishes_on_domainOfDependence ht (fun _ _ ↦ rfl)
  intro y hy
  apply freeWaveVelocity.zero_of_le_dist
  simp only [Real.dist_eq, sub_zero]
  change 2 ≤ |y|
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact (neg_le_abs y).trans' (by linarith [hy.2])
  · exact (le_abs_self y).trans' (by linarith [hy.1])

/-- The squared displacement is integrable at every nonnegative time. -/
theorem integrable_sq_freeWave {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x ↦ freeWave t x ^ 2) := by
  apply ((continuous_freeWave t).pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (hasCompactSupport_freeWave ht).mul_right (f' := freeWave t)

/-- The expanding characteristic interval contains the unit plateau of the velocity. -/
theorem one_le_freeWave {t x : ℝ} (hx : x ∈ Icc (-(t - 1)) (t - 1)) :
    1 ≤ freeWave t x := by
  have hmass : (∫ y in (-1 : ℝ)..1, freeWaveVelocity y) = 2 := by
    calc
      _ = ∫ _ in (-1 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        simp only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hy
        apply freeWaveVelocity.one_of_mem_closedBall
        simpa [Metric.mem_closedBall, Real.dist_eq, abs_le, freeWaveVelocity] using hy
      _ = 2 := by cas
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (show x - t ≤ -1 by linarith [hx.2]) (show (-1 : ℝ) ≤ 1 by norm_num)
    (show 1 ≤ x + t by linarith [hx.1])
    (Filter.Eventually.of_forall (fun y ↦ freeWaveVelocity.nonneg' y))
    (freeWaveVelocity.continuous.intervalIntegrable (x - t) (x + t))
  rw [hmass] at hmono
  unfold freeWave WaveEquation.dAlembertFormula
  linarith

/-- The squared L² displacement grows at least linearly with time. -/
theorem integral_sq_freeWave_lower_bound {t : ℝ} (ht : 1 ≤ t) :
    2 * (t - 1) ≤ ∫ x, freeWave t x ^ 2 := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hab : -(t - 1) ≤ t - 1 := by linarith
  calc
    2 * (t - 1) = ∫ _ in Icc (-(t - 1)) (t - 1), (1 : ℝ) := by
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        smul_eq_mul, mul_one, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      cas
    _ ≤ ∫ x in Icc (-(t - 1)) (t - 1), freeWave t x ^ 2 := by
      apply setIntegral_mono_on (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
        (integrable_sq_freeWave ht0).integrableOn measurableSet_Icc
      intro x hx
      nlinarith [one_le_freeWave hx]
    _ ≤ ∫ x, freeWave t x ^ 2 := setIntegral_le_integral (integrable_sq_freeWave ht0)
        (Filter.Eventually.of_forall fun x ↦ sq_nonneg (freeWave t x))

/-- Even an almost-everywhere uniform bound on the squared displacement is impossible. -/
theorem not_ae_bounded_integral_sq_freeWave :
    ¬ ∃ C : ℝ, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), (∫ x, freeWave t x ^ 2) ≤ C := by
  rintro ⟨C, hC⟩
  have hs : Ioi (max 1 (C / 2 + 1)) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_trans zero_lt_one ((le_max_left _ _).trans_lt ht)
  have hres := ae_restrict_of_ae_restrict_of_subset hs hC
  obtain ⟨t, ht, hbound⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by simp : volume (Ioi (max 1 (C / 2 + 1))) ≠ 0) hres
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht.le
  have hlower := integral_sq_freeWave_lower_bound ht1
  have htC := (le_max_right 1 (C / 2 + 1)).trans_lt ht
  linarith

/-- The spatial L² norm does not belong to L∞ on the positive time half-line. -/
theorem not_memLp_lpNorm_freeWave :
    ¬ MemLp (fun t ↦ lpNorm (freeWave t) 2 volume) ∞ (volume.restrict (Ioi 0)) := by
  intro h
  apply not_ae_bounded_integral_sq_freeWave
  refine ⟨lpNorm (fun t ↦ lpNorm (freeWave t) 2 volume) ∞ (volume.restrict (Ioi 0)) ^ 2, ?_⟩
  filter_upwards [ae_le_lpNorm_exponent_top h, ae_restrict_mem measurableSet_Ioi] with t ht ht0
  have hmem : MemLp (freeWave t) 2 volume :=
    (continuous_freeWave t).memLp_of_hasCompactSupport (hasCompactSupport_freeWave ht0.le)
  rw [hmem.integral_sq_eq_lpNorm_sq]
  exact sq_le_sq₀ lpNorm_nonneg lpNorm_nonneg |>.mpr
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg lpNorm_nonneg] using! ht)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
