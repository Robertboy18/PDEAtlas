/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Energy
public import PDE.Analysis.MeasureTheory.Integral.RadialPower.Quadratic

/-!
# Inverse-radius control for the cone profile

Suppose a field is `C²` on an open time strip from before the base time to the tip
time and solves the defocusing quintic wave equation on the cone below its tip.
The cone profile belongs to `L⁶` on the base ball. If the cone has positive height,
the squared profile satisfies an inverse-radius bound. Neither result assumes
regularity at the tip.

The quintic equation supplies `L⁶` membership. The general quadratic radial-weight
estimate then applies without any further condition at the cone tip.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set PDE PDE.Common SobolevSpace SobolevSpace.GraphSpace

namespace WaveEquation.ConeProfile

/-- If `s₀ < s`, a field that is `C²` on `s₀ < t < T` and solves the defocusing quintic
wave equation on the cone for `s ≤ t < T` has an `L⁶` cone profile on the base ball.
Finite potential flux gives this `L⁶` membership. -/
theorem memLp_six_of_wave {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    MemLp (coneProfile T c u) 6 (volume.restrict (ball c (T - s))) := by
  obtain ⟨U, hU, _⟩ := exists_h1_of_wave hu c hs hwave
  have hm := ((memLp_congr_ae hU).mp (Lp.memLp (wkpBaseCoordinateCLM U))).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by norm_num : (6 : ENNReal) ≠ 0)
    (by norm_num)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
    (show Even 6 by decide).pow_abs, IntegrableOn, domainMeasure] using
      (integrable_densities_of_wave hu c hs hwave).2

/-- For a defocusing quintic wave on a cone of positive height, the inverse-radius integral
of the squared profile is bounded by its squared `L⁶` norm times the cone height and an
explicit universal factor. The field is `C²` on an open time strip from before the base
time to the tip time; neither the equation nor regularity is assumed at the tip. -/
theorem integral_sq_div_dist_le_of_wave {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (∫ x in ball c (T - s), coneProfile T c u x ^ 2 / ‖x - c‖) ≤
      (∫ x in ball c (T - s), |coneProfile T c u x| ^ 6) ^ (1 / 3 : ℝ) *
        ((∫ x in ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) * (T - s)) :=
  integral_sq_div_norm_sub_le_of_memLp_six (by simp) c (sub_pos.mpr hsT)
    (memLp_six_of_wave hu c hs hwave)

end WaveEquation.ConeProfile
