/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Polar
public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The exterior Newtonian kernel in three dimensions

Polar integration gives the exact L⁶ norm of `1_(|x|>R)/|x|` for R > 0,
including its R^(-1/2) decay. The Newtonian normalization 1/(4π) is not included.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace WaveEquation.Strichartz

/-- The inverse-sixth-power tail in three dimensions is given by the exact polar integral. -/
theorem lintegral_norm_neg_six {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : ℝ^3 in {x | R < ‖x‖}, ENNReal.ofReal (‖x‖ ^ (-6 : ℝ))) =
      (volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (R ^ (-3 : ℝ) / 3) := by
  have hradial := lintegral_fun_norm_addHaar (volume : Measure (ℝ^3))
    (f := (Ioi R).indicator (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-6 : ℝ))))
    ((by fun_prop : Measurable (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-6 : ℝ)))).indicator
      measurableSet_Ioi)
  have hleft : (fun x : ℝ^3 ↦ (Ioi R).indicator (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-6 : ℝ))) ‖x‖) =
      {x : ℝ^3 | R < ‖x‖}.indicator
        (fun x : ℝ^3 ↦ ENNReal.ofReal (‖x‖ ^ (-6 : ℝ))) := by
    ext x
    simp only [Set.indicator_apply, mem_Ioi, mem_ofPred_eq]
  rw [hleft, lintegral_indicator (measurableSet_lt measurable_const measurable_norm)] at hradial
  rw [hradial]
  congr 1
  have hintegrand : (fun r : ℝ ↦ ENNReal.ofReal (r ^ (Module.finrank ℝ (ℝ^3) - 1)) *
      (Ioi R).indicator (fun s : ℝ ↦ ENNReal.ofReal (s ^ (-6 : ℝ))) r) =
      (Ioi R).indicator (fun r : ℝ ↦ ENNReal.ofReal (r ^ (-4 : ℝ))) := by
    ext r
    by_cases hr : R < r
    · simp only [indicator_apply, mem_Ioi, hr, ↓reduceIte]
      norm_num only [finrank_euclideanSpace_fin, Nat.reduceSub]
      rw [← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_add (hR.trans hr)]
      norm_num
    · simp only [indicator_apply, mem_Ioi, hr, ↓reduceIte, mul_zero]
  rw [hintegrand, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict
    measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hR.le)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hR]
    congr 1
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hR.trans hr).le _

/-- The inverse-norm Newtonian kernel restricted to the exterior of the radius-R ball. -/
noncomputable def exteriorNewtonKernel (R : ℝ) (x : ℝ^3) : ℝ :=
  {x : ℝ^3 | R < ‖x‖}.indicator (fun x ↦ ‖x‖⁻¹) x

/-- The exterior Newtonian kernel is measurable for every radius. -/
theorem measurable_exteriorNewtonKernel (R : ℝ) : Measurable (exteriorNewtonKernel R) :=
  measurable_norm.inv.indicator (measurableSet_lt measurable_const measurable_norm)

/-- The sixth-power integral of the exterior Newtonian kernel is finite and explicit. -/
theorem lintegral_enorm_exteriorNewtonKernel {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : ℝ^3, ‖exteriorNewtonKernel R x‖ₑ ^ (6 : ℝ)) =
      (volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (R ^ (-3 : ℝ) / 3) := by
  rw [← lintegral_norm_neg_six hR, ← lintegral_indicator
    (measurableSet_lt measurable_const measurable_norm)]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : R < ‖x‖
  · simp only [exteriorNewtonKernel, indicator_apply, mem_ofPred_eq, hx, ↓reduceIte]
    rw [Real.enorm_eq_ofReal_abs, abs_inv, abs_norm, ENNReal.ofReal_rpow_of_nonneg
      (inv_nonneg.mpr (norm_nonneg x)) (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    rw [Real.inv_rpow (norm_nonneg x), ← Real.rpow_neg (norm_nonneg x)]
  · simp [exteriorNewtonKernel, hx]

/-- The exterior Newtonian kernel belongs to L⁶ for every positive radius. -/
theorem memLp_exteriorNewtonKernel {R : ℝ} (hR : 0 < R) :
    MemLp (exteriorNewtonKernel R) 6 := by
  change eLpNorm (exteriorNewtonKernel R) 6 volume < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (measurable_exteriorNewtonKernel R).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_enorm_exteriorNewtonKernel hR]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top

/-- The exact L⁶ norm of the exterior Newtonian kernel decays as R^(-1/2). -/
theorem eLpNorm_exteriorNewtonKernel {R : ℝ} (hR : 0 < R) :
    eLpNorm (exteriorNewtonKernel R) 6 volume = ((volume : Measure (ℝ^3)).toSphere univ *
      ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ) * ENNReal.ofReal (R ^ (-1 / 2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_exteriorNewtonKernel R).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_enorm_exteriorNewtonKernel hR]
  have hfactor : ENNReal.ofReal (R ^ (-3 : ℝ) / 3) =
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (R ^ (-3 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    congr 1
    ring
  rw [hfactor, ← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hR.le _) (by norm_num : (0 : ℝ) ≤ 1 / 6),
    ← Real.rpow_mul hR.le]
  norm_num

end WaveEquation.Strichartz
