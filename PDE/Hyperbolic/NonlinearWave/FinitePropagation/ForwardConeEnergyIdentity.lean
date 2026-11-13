/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeEnergyIdentity
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Cone flux from forward smoothness

Smooth half-space extension transfers the normalized cone identity to fields
which are C² only on the closed forward half-space. The differential within
that half-space determines the initial energy and lateral flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), equation (3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- Lateral null flux computed from the forward differential. -/
def forwardSemilinearWaveConeDissipation (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (c : ℝ^n) (p : ℝ^(n + 1)) : ℝ :=
  (1 / 2 : ℝ) * ‖forwardDifferential u (p 0) (spatialPart p) (EuclideanSpace.single 0 1) •
      NormedSpace.normalize (spatialPart p - c) -
    (WithLp.toLp 2 (fun i : Fin n ↦ forwardDifferential u (p 0) (spatialPart p)
      (EuclideanSpace.single i.succ 1)) : ℝ^n)‖ ^ 2 + V (u p)

/-- The forward lateral density equals that of any smooth half-space representative. -/
theorem forwardSemilinearWaveConeDissipation_eq_of_extension (V : ℝ → ℝ) {u U : ℝ^(n + 1) → ℝ}
    (hU : ContDiff ℝ 2 U) (heq : EqOn U u {p | 0 ≤ p 0}) (c : ℝ^n) {p : ℝ^(n + 1)} (hp : 0 ≤ p 0) :
    forwardSemilinearWaveConeDissipation V u c p = semilinearWaveConeDissipation V U c p := by
  unfold forwardSemilinearWaveConeDissipation
  rw [forwardDifferential_eq_fderiv_of_extension hU heq hp, timeSpaceCons_spatialPart, ← heq hp]
  rfl

/-- The flux identity (3) of Evans, §12.1.2, with only closed-forward-halfspace C²
regularity. Both the initial energy and lateral flux use the forward
differential, independent of arbitrary negative-time values. -/
theorem normalized_integral_forwardSemilinearWaveConeDissipation [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0}) (c : ℝ^n)
    {T : ℝ} (hT : 0 ≤ T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    (1 / Real.sqrt 2) * (∫ p in backwardConeLateralSurface c T,
      forwardSemilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ∫ x in Metric.ball c T, forwardSemilinearWaveEnergyDensity V u 0 x := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace 0 2 hu
  have hΓ : MeasurableSet (backwardConeLateralSurface c T) := by
    rw [backwardConeLateralSurface_eq_image]
    obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
    exact ((isCompact_closedBall c T).image hK.continuous).measurableSet
  have hwaveU (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveOperator V U (timeSpaceCons t x) = 0 := by
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons t x) 0 by simpa only [timeSpaceCons_zero] using ht.1)
    unfold semilinearWaveOperator
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave t ht x hx
  calc
    _ = (1 / Real.sqrt 2) * (∫ p in backwardConeLateralSurface c T,
          semilinearWaveConeDissipation V U c p ∂Measure.euclideanHausdorffMeasure n) := by
      congr 1
      refine setIntegral_congr_fun hΓ fun p hp ↦ ?_
      exact forwardSemilinearWaveConeDissipation_eq_of_extension V hU heq c hp.1
    _ = semilinearBackwardConeEnergy V U c T 0 :=
      normalized_integral_semilinearWaveConeDissipation hV hU c hT hwaveU
    _ = _ := by
      rw [semilinearBackwardConeEnergy_eq_ballIntegral hV.continuous
        (hU.of_le (by norm_num))]
      simp only [sub_zero, ballIntegral]
      refine setIntegral_congr_fun measurableSet_ball fun x _ ↦ ?_
      exact (forwardSemilinearWaveEnergyDensity_eq_of_extension V hU heq le_rfl x).symm

end WaveEquation
