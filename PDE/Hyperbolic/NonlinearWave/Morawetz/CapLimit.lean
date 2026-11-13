/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Cap
import PDE.Analysis.MeasureTheory.Lp.VanishingMeasure
import PDE.FDeriv.SpaceTime
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Vanishing of the scaling-current cap

On a shrinking ball, a uniform higher Lᵖ bound makes the displacement L² norm
vanish. Combined with bounded energy and velocity, this removes the terminal
cap without assuming that the solution extends to the cone tip.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric PDE.Common Set
open scoped ENNReal Topology

namespace WaveEquation

variable {n : ℕ} [Fact (0 < n)]

private theorem tendsto_backwardBall_volume (c : ℝ^n) (T : ℝ) :
    Tendsto (fun t : ℝ ↦ volume (ball c (T - t))) (𝓝[<] T) (𝓝 0) := by
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hr : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := T)).sub
      (show Tendsto (fun t : ℝ ↦ t) (𝓝[<] T) (𝓝 T) from nhdsWithin_le_nhds)
  have hp := ENNReal.Tendsto.pow (n := n) (ENNReal.tendsto_ofReal hr)
  have hm := ENNReal.Tendsto.mul_const hp
    (b := ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)))
    (Or.inr ENNReal.ofReal_ne_top)
  simpa only [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_zero,
    zero_pow (Nat.ne_of_gt (Fact.out : 0 < n)), zero_mul] using hm

/-- Bounded energy, bounded L² velocity and a bounded displacement norm with
exponent strictly above two make the scaling-current cap vanish. Regularity
is required only on time slices strictly before the tip. -/
theorem tendsto_ballIntegral_scalingCurrentDensity_zero {u : ℝ^(n + 1) → ℝ} {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) (hpos : ∀ z, 0 ≤ V z) (c : ℝ^n) (T E K : ℝ) {q C : ℝ≥0∞} (hq : 2 < q)
    (hqfinite : q ≠ ∞) (hC : C ≠ ∞) (hu : ∀ᶠ t in 𝓝[<] T, ∀ x, ContDiffAt ℝ 2 u (timeSpaceCons t x))
    (henergy : ∀ᶠ t in 𝓝[<] T, PDE.Analysis.ballIntegral n
      (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T - t) ≤ E)
    (hdisplacement : ∀ᶠ t in 𝓝[<] T,
      eLpNorm (fun x ↦ u (timeSpaceCons t x)) q (volume.restrict (ball c (T - t))) ≤ C)
    (hvelocity : ∀ᶠ t in 𝓝[<] T,
      lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2 (volume.restrict (ball c (T - t))) ≤ K) :
    Tendsto (fun t ↦ PDE.Analysis.ballIntegral n (fun x ↦ scalingCurrentDensity V 1
      (timeSpaceCons T c) u (timeSpaceCons t x)) c (T - t)) (𝓝[<] T) (𝓝 0) := by
  have hmeas : ∀ᶠ t in 𝓝[<] T, AEStronglyMeasurable (fun x ↦ u (timeSpaceCons t x))
        (volume.restrict (ball c (T - t))) := by
    filter_upwards [hu] with t hut
    have hcont : Continuous (fun x ↦ u (timeSpaceCons t x)) :=
      continuous_iff_continuousAt.mpr fun x ↦ (hut x).continuousAt.comp
        (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
    exact hcont.aestronglyMeasurable
  have hmeasure : Tendsto
      (fun t : ℝ ↦ (volume.restrict (ball c (T - t))) univ) (𝓝[<] T) (𝓝 0) := by
    simpa only [Measure.restrict_apply_univ] using tendsto_backwardBall_volume c T
  have hnorm := tendsto_lpNorm_of_measure_univ_tendsto_zero
    (by norm_num : (0 : ℝ≥0∞) < 2) hq hqfinite hC hmeas hdisplacement hmeasure
  have hr : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := T)).sub
      (show Tendsto (fun t : ℝ ↦ t) (𝓝[<] T) (𝓝 T) from nhdsWithin_le_nhds)
  have hmajorant :=
    (((tendsto_const_nhds (x := (2 : ℝ))).mul hr).mul_const E).add (hnorm.mul_const K)
  simp only [mul_zero, zero_mul, add_zero] at hmajorant
  apply squeeze_zero_norm' ?_ hmajorant
  filter_upwards [self_mem_nhdsWithin, hu, henergy, hvelocity] with t ht hut he hv
  have hb := abs_ballIntegral_scalingCurrentDensity_le hV T t c ht hut (fun x _ ↦ hpos _)
  have henergy' := mul_le_mul_of_nonneg_left he
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sub_nonneg.mpr (le_of_lt ht)))
  have hvelocity' := mul_le_mul_of_nonneg_left hv
    (lpNorm_nonneg (f := fun x ↦ u (timeSpaceCons t x))
      (p := 2) (μ := volume.restrict (ball c (T - t))))
  simpa only [Real.norm_eq_abs] using hb.trans (add_le_add henergy' hvelocity')

end WaveEquation
