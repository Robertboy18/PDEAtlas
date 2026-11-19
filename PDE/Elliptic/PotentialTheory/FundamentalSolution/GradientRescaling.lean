/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.GradientDifference

/-!
# Rescaling the canonical fundamental-solution gradient

The gradient has degree minus the boundary dimension in every ambient dimension
at least two. Consequently a convergent nonzero rescaled displacement determines
the limit of its rescaled gradient, including in the logarithmic planar case.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open Filter PDE.Analysis
open scoped Gradient Topology

variable {m : ℕ}

/-- The canonical gradient is continuous away from the pole. -/
theorem continuousAt_gradient_fundamentalSolution (hm : 1 ≤ m)
    {z : ℝ^(m + 1)} (hz : z ≠ 0) :
    ContinuousAt (∇ (fundamentalSolution (m + 1))) z := by
  have hrad : ContinuousAt
      (fun y : ℝ^(m + 1) ↦ (-1 / (unitSphereArea (m + 1) * ‖y‖ ^ (m + 1))) • y) z :=
    (continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.norm.pow _))
      (mul_ne_zero (unitSphereArea_pos (n := m + 1)).ne'
        (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)))).smul continuousAt_id
  apply hrad.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with y hy
  exact gradient_fundamentalSolution (by omega) hy

/-- Positive dilation of the canonical gradient has the boundary-dimension scaling. -/
theorem pow_smul_gradient_fundamentalSolution_smul (hm : 1 ≤ m)
    {t : ℝ} (ht : 0 < t) {z : ℝ^(m + 1)} (hz : z ≠ 0) :
    t ^ m • ∇ (fundamentalSolution (m + 1)) (t • z) =
      ∇ (fundamentalSolution (m + 1)) z := by
  rw [gradient_fundamentalSolution (by omega) (smul_ne_zero ht.ne' hz),
    gradient_fundamentalSolution (by omega) hz, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow, pow_succ, smul_smul, smul_smul]
  congr 1
  field_simp [ht.ne', norm_ne_zero_iff.mpr hz]

/-- A nonzero limit of rescaled displacements gives the limit of the rescaled gradient. -/
theorem tendsto_pow_smul_gradient_fundamentalSolution (hm : 1 ≤ m)
    {f : ℝ → ℝ^(m + 1)} {z : ℝ^(m + 1)} (hz : z ≠ 0)
    (hf : Tendsto (fun t : ℝ ↦ t⁻¹ • f t) (𝓝[>] 0) (𝓝 z)) :
    Tendsto (fun t : ℝ ↦ t ^ m • ∇ (fundamentalSolution (m + 1)) (f t))
      (𝓝[>] 0) (𝓝 (∇ (fundamentalSolution (m + 1)) z)) := by
  have h := (continuousAt_gradient_fundamentalSolution hm hz).tendsto.comp hf
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hf.eventually_ne hz] with t ht hft
  have heq := pow_smul_gradient_fundamentalSolution_smul hm ht hft
  simpa only [Function.comp_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
    using heq.symm

end PotentialTheory
