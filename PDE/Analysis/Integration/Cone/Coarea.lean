/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Surface
public import PDE.Analysis.Integration.EuclideanBall
import CAS.ExactTactic

/-!
# Spherical sections of the lateral cone

The normalized Hausdorff area formula and radial coarea identify a lateral
cone integral with the time integral of its spherical sections. This supplies
the geometric normalization in Evans, §12.1.2, Theorem 2(i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), (3), and step 1 of its proof,
  p. 661. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common

namespace WaveEquation

variable {n : ℕ}

/-- The normalized surface integral divides out the cone graph area factor. -/
theorem normalized_integral_backwardConeLateralSurface [Fact (0 < n)]
    (c : ℝ^n) (T : ℝ) (g : ℝ^(n + 1) → ℝ)
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure n).restrict (backwardConeLateralSurface c T))) :
    (1 / Real.sqrt 2) *
        (∫ p in backwardConeLateralSurface c T, g p ∂Measure.euclideanHausdorffMeasure n) =
      ∫ x in Metric.ball c T, g (backwardConeGraph c T x) := by
  rw [integral_backwardConeLateralSurface c T g hg, ← mul_assoc]
  have hscale : (1 / Real.sqrt 2) * Real.sqrt 2 = 1 := by cas
  rw [hscale, one_mul]

/-- Radial coarea turns normalized closed-cone surface integration into time
integration of the spherical sections, with the vertex handled by null sets. -/
theorem normalized_integral_backwardConeLateralSurface_eq_timeIntegral [Fact (0 < n)]
    (c : ℝ^n) {T : ℝ} (hT : 0 ≤ T) (g : ℝ^(n + 1) → ℝ)
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure n).restrict (backwardConeLateralSurface c T)))
    (hi : IntegrableOn (fun x ↦ g (backwardConeGraph c T x)) (Metric.ball c T)) :
    (1 / Real.sqrt 2) *
        (∫ p in backwardConeLateralSurface c T, g p ∂Measure.euclideanHausdorffMeasure n) =
      ∫ t in (0 : ℝ)..T,
        PDE.Analysis.sphereIntegral n (fun x ↦ g (timeSpaceCons t x)) c (T - t) := by
  rw [normalized_integral_backwardConeLateralSurface c T g hg]
  change PDE.Analysis.ballIntegral n (fun x ↦ g (backwardConeGraph c T x)) c T = _
  rw [PDE.Analysis.coarea_formula_ball _ c T hi, integral_Icc_eq_integral_Ioc]
  let F : ℝ → ℝ := fun t ↦
    PDE.Analysis.sphereIntegral n (fun x ↦ g (timeSpaceCons t x)) c (T - t)
  have hchange := intervalIntegral.integral_comp_sub_left (a := 0) (b := T) F T
  simp only [sub_self, sub_zero] at hchange
  rw [← hchange, intervalIntegral.integral_of_le hT]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  change PDE.Analysis.sphereIntegral n _ c r = F (T - r)
  dsimp only [F]
  rw [sub_sub_cancel]
  apply PDE.Analysis.sphereIntegral_congr_on_sphere hr.1
  intro x hx
  have hx' : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [backwardConeGraph, hx']

end WaveEquation
