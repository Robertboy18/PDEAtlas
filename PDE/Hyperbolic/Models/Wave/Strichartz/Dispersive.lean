/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Convolution.Young
public import PDE.Hyperbolic.Models.Wave.Strichartz.ExteriorKernel

/-!
# Dispersive estimate for the exterior Newtonian convolution

General Young's inequality with exponents 6, 12/11 and 12 combines with the exact
L⁶ kernel norm to give inverse square-root time decay. Finite L^(12/11) data also
have an integrable convolution integrand almost everywhere.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- The exterior Newtonian convolution maps L^(12/11) to L¹² with inverse square-root decay. -/
theorem eLpNorm_integral_exteriorNewtonKernel_le {R : ℝ} (hR : 0 < R)
    {f : ℝ^3 → ℝ} (hf : Measurable f) :
    eLpNorm (fun x ↦ ∫ y, exteriorNewtonKernel R (x - y) * f y) 12 volume ≤
      (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ) *
      ENNReal.ofReal (R ^ (-1 / 2 : ℝ))) * eLpNorm f (12 / 11) volume := by
  have h := eLpNorm_integral_convolution_le volume (p := 6) (q := 12 / 11) (r := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (measurable_exteriorNewtonKernel R) hf
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11), ENNReal.ofReal_ofNat] at h
  rwa [eLpNorm_exteriorNewtonKernel hR] at h

/-- The dispersive convolution has an integrable defining integrand almost everywhere. -/
theorem ae_integrable_exteriorNewtonKernel_mul {R : ℝ} (hR : 0 < R)
    {f : ℝ^3 → ℝ} (hf : Measurable f) (hfp : MemLp f (12 / 11)) :
    ∀ᵐ x : ℝ^3, Integrable (fun y ↦ exteriorNewtonKernel R (x - y) * f y) := by
  apply ae_integrable_convolution_of_memLp volume (p := 6) (q := 12 / 11) (r := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (measurable_exteriorNewtonKernel R) hf
  · simpa using memLp_exteriorNewtonKernel hR
  · simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11),
      ENNReal.ofReal_ofNat] using hfp

end WaveEquation.Strichartz
