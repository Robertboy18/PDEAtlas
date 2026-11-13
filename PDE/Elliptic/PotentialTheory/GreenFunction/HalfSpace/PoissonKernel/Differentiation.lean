/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.KernelHarmonic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability

/-!
# Interior regularity of the half-space Poisson extension

Measurable boundary data bounded on the boundary hyperplane give a `C²` Poisson extension on the
open half-space (`contDiffOn_poissonHalfSpaceExtension`;
`differentiableOn_poissonHalfSpaceExtension` is the first-order statement). A common Hessian
majorant proves continuity of the second derivative field. Evans asserts `u ∈ C^∞(ℝ^n₊)` in step 2
of the proof of §2.2.4(b), Theorem 14, because `x ↦ K(x, y)` is smooth for `x ≠ y`; the majorants
here justify differentiating twice under the integral sign.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), Theorem 14 (Poisson's formula for half-space),
  p. 37, and step 2 of its proof, p. 38.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open PDE.Analysis MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

open PoissonHalfSpace

/-- The half-space Poisson extension is differentiable throughout the open half-space. -/
theorem differentiableOn_poissonHalfSpaceExtension {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded : ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M) :
    DifferentiableOn ℝ
      (poissonHalfSpaceExtension (n := n) g)
      (SobolevSpace.HalfSpace.upper n) := by
  intro x hx
  rw [show poissonHalfSpaceExtension (n := n) g = _ from
    funext (poissonHalfSpaceExtension_eq_integral g hg)]
  exact ((by fun_prop : DifferentiableAt ℝ (fun z : ℝ^n ↦
    2 * z PDE.Common.lastIndex / ((n : ℝ) * unitBallVolume n)) x).mul
      (hasFDerivAt_halfSpaceIntegral_div_distance_pow hg hg_bounded hx).differentiableAt
    ).differentiableWithinAt

private theorem continuousOn_halfSpaceIntegral_hessian_apply
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (v w : ℝ^n) :
    ContinuousOn
      (fun z : ℝ^n ↦
        ∫ y : ℝ^(n - 1),
          g (halfSpaceEmb (n := n) y) *
            (let p : ℝ^n := halfSpaceEmb (n := n) y
             let S : ℝ := (-(n : ℝ)) / dist z p ^ (n + 2)
             let T : ℝ := (innerSL ℝ v) (z - p)
             S * (innerSL ℝ v) w +
              T * ((-(n : ℝ)) *
                EuclideanDistance.invDistPowFDerivFormula (n + 2) z p w))
          ∂(volume : Measure ℝ^(n - 1)))
      (SobolevSpace.HalfSpace.upper n) := by
  classical
  intro x hx
  obtain ⟨M, hM⟩ := hg_bounded
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (halfSpaceEmb_mem_boundary (n := n) 0))
  have hε : 0 < x PDE.Common.lastIndex / 2 := by
    have : 0 < x PDE.Common.lastIndex := by simpa [SobolevSpace.HalfSpace.upper] using hx
    positivity
  have hball := halfHeightBall_subset_upper (n := n) hx
  refine (continuousAt_of_dominated (bound := fun y ↦ M * ((n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ *
    ((2 : ℝ) ^ (n + 2) * (dist x (halfSpaceEmb (n := n) y) ^ (n + 2))⁻¹) * ‖w‖)) ?_ ?_ ?_ ?_
    ).continuousWithinAt
  · filter_upwards [Metric.ball_mem_nhds x hε] with z hz
    simpa only [EuclideanDistance.invDistPowSecondFDerivFormula, smul_apply, smul_eq_mul,
      add_apply] using ((integrable_boundary_invDistPowFDeriv_apply_fderiv hg ⟨M, hM⟩ (hball hz)
        v).apply_continuousLinearMap w).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x hε] with z hz
    refine ae_of_all _ fun y ↦ ?_
    calc _ = ‖g (halfSpaceEmb y)‖ *
          ‖EuclideanDistance.invDistPowSecondFDerivFormula n z (halfSpaceEmb y) v w‖ := by
          simp only [norm_mul, EuclideanDistance.invDistPowSecondFDerivFormula, smul_apply,
            smul_eq_mul, add_apply]
      _ ≤ M * ((n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ *
          (dist z (halfSpaceEmb (n := n) y) ^ (n + 2))⁻¹ * ‖w‖) := by
          gcongr
          · exact hM _ (halfSpaceEmb_mem_boundary y)
          · exact (ContinuousLinearMap.le_opNorm _ _).trans (by
              gcongr
              exact EuclideanDistance.norm_invDistPowFDerivFormula_apply_fderiv_le n
                (halfSpace_ne_halfSpaceEmb (hball hz) y))
      _ ≤ _ := by
          gcongr
          exact inv_distance_pow_le_of_mem_halfHeightBall hx hz y (n + 2)
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (integrable_inv_distance_pow_of_le x hx (m := n + 2) (by omega)).const_mul
        (M * ((n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ * 2 ^ (n + 2) * ‖w‖))
  · refine ae_of_all _ fun y ↦ ?_
    have hxp := halfSpace_ne_halfSpaceEmb (n := n) hx y
    have := (EuclideanDistance.contDiffAt_inv_dist_pow (m := (0 : ℕ∞)) (k := n + 2)
      hxp).continuousAt
    have := (EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply (k := n + 2) (v := w)
      hxp).continuousAt
    simp only [div_eq_mul_inv]
    fun_prop

private theorem contDiffOn_halfSpaceIntegral_invDistPowFDeriv_apply
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (v : ℝ^n) :
    ContDiffOn ℝ 1
      (fun z : ℝ^n ↦
        ∫ y : ℝ^(n - 1),
          g (halfSpaceEmb (n := n) y) *
            EuclideanDistance.invDistPowFDerivFormula n z
              (halfSpaceEmb (n := n) y) v
          ∂(volume : Measure ℝ^(n - 1)))
      (SobolevSpace.HalfSpace.upper n) := by
  refine contDiffOn_succ_of_fderiv_apply (n := (0 : WithTop ℕ∞)) (fun x hx ↦
    (hasFDerivAt_halfSpaceIntegral_invDistPowFDeriv_apply hg hg_bounded hx
      v).differentiableAt.differentiableWithinAt) (by intro h; cases h) fun w ↦ ?_
  refine (contDiffOn_congr fun x hx ↦ ?_).2
    (contDiffOn_zero.2 (continuousOn_halfSpaceIntegral_hessian_apply hg hg_bounded v w))
  rw [fderivWithin_of_isOpen (SobolevSpace.HalfSpace.isOpen_upper n) hx,
    (hasFDerivAt_halfSpaceIntegral_invDistPowFDeriv_apply hg hg_bounded hx v).fderiv,
    ContinuousLinearMap.integral_apply
      (integrable_boundary_invDistPowFDeriv_apply_fderiv hg hg_bounded hx v)]
  simp only [EuclideanDistance.invDistPowSecondFDerivFormula, smul_apply, smul_eq_mul, add_apply]

private theorem contDiffOn_halfSpaceIntegral_div_distance_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M) :
    ContDiffOn ℝ 2
      (fun z : ℝ^n ↦
        ∫ y : ℝ^(n - 1),
          g (halfSpaceEmb (n := n) y) /
            dist z (halfSpaceEmb (n := n) y) ^ n
          ∂(volume : Measure ℝ^(n - 1)))
      (SobolevSpace.HalfSpace.upper n) := by
  refine contDiffOn_succ_of_fderiv_apply (n := (1 : WithTop ℕ∞)) (fun x hx ↦
    (hasFDerivAt_halfSpaceIntegral_div_distance_pow hg hg_bounded
      hx).differentiableAt.differentiableWithinAt) (by intro h; cases h) fun v ↦ ?_
  refine (contDiffOn_congr fun x hx ↦ ?_).2
    (contDiffOn_halfSpaceIntegral_invDistPowFDeriv_apply hg hg_bounded v)
  rw [fderivWithin_of_isOpen (SobolevSpace.HalfSpace.isOpen_upper n) hx,
    (hasFDerivAt_halfSpaceIntegral_div_distance_pow hg hg_bounded hx).fderiv,
    ContinuousLinearMap.integral_apply
      (integrable_boundary_smul_invDistPowFDeriv hg hg_bounded hx n (by omega))]
  simp only [smul_apply, smul_eq_mul]

/-- Measurable data bounded on the boundary have a `C²` Poisson extension on the
open half-space. This is the finite regularity needed for classical
harmonicity. -/
theorem contDiffOn_poissonHalfSpaceExtension
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M) :
    ContDiffOn ℝ 2
      (poissonHalfSpaceExtension (n := n) g)
      (SobolevSpace.HalfSpace.upper n) := by
  rw [show poissonHalfSpaceExtension (n := n) g = _ from
    funext (poissonHalfSpaceExtension_eq_integral g hg)]
  exact (by fun_prop : ContDiffOn ℝ 2 (fun z : ℝ^n ↦
    2 * z PDE.Common.lastIndex / ((n : ℝ) * unitBallVolume n)) _).mul
      (contDiffOn_halfSpaceIntegral_div_distance_pow hg hg_bounded)

end GreenFunction
