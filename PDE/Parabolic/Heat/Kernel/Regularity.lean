/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic
public import PDE.Analysis.SpecialFunctions.Exponential.Flatness
import CAS.ExactTactic

/-!
# Smoothness of the heat kernel away from its pole

The retarded Gaussian is smooth at time zero whenever the spatial variable is nonzero. Expressing it
through Mathlib's flat exponential `expNegInvGlue` proves this across the time junction, including
in odd dimensions. Evans uses this regularity when he notes that the kernel `K` of (38) is smooth on
`C - C'`, in step 3 of his proof of §2.3.3(b), Theorem 8.

## Main results

* `contDiffAt_fundamentalSolutionHeat_of_spatial_ne_zero`: smoothness at every time when the spatial
  argument is nonzero.
* `contDiffOn_fundamentalSolutionHeat`: the kernel, extended by zero to `t ≤ 0`, is `C^m` on
  spacetime minus the origin.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(a), the definition of the fundamental solution, p. 46,
  and §2.3.3(b), step 3 of the proof of Theorem 8, (38), p. 61.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open PDE.Common Filter Set
open scoped Topology

variable {n : ℕ}

/-- Away from the spatial origin, the retarded Gaussian is a smooth spatial
factor times a real power multiplied by the flat exponential. -/
theorem fundamentalSolutionHeat_eq_rpow_mul_expNegInvGlue
    {x : ℝ^n} (hx : x ≠ 0) (t : ℝ) :
    fundamentalSolutionHeat x t =
      (Real.pi * ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) *
        ((4 * t / ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) *
          expNegInvGlue (4 * t / ‖x‖ ^ 2)) := by
  have hx2 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  rcases le_or_gt t 0 with ht | ht
  · have harg : 4 * t / ‖x‖ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hx2.le
    simp [fundamentalSolutionHeat, ht, expNegInvGlue.zero_of_nonpos harg]
  · have harg : 0 < 4 * t / ‖x‖ ^ 2 := by positivity
    rw [fundamentalSolutionHeat, ite_eq_right ht.not_ge, expNegInvGlue,
      ite_eq_right harg.not_ge]
    have he : -(4 * t / ‖x‖ ^ 2)⁻¹ = -(‖x‖ ^ 2 / (4 * t)) := by
      cas
    rw [he, ← mul_assoc, ← Real.mul_rpow (by positivity : 0 ≤ Real.pi * ‖x‖ ^ 2)
      harg.le]
    congr 2
    cas using hx2

/-- Joint smoothness on positive time; no spatial boundedness is needed. -/
theorem contDiffAt_fundamentalSolutionHeat_of_time_pos {m : ℕ∞}
    {p : ℝ^n × ℝ} (ht : 0 < p.2) :
    ContDiffAt ℝ m (Function.uncurry fundamentalSolutionHeat) p := by
  have hbase : 4 * Real.pi * p.2 ≠ 0 := by positivity
  have htime : 4 * p.2 ≠ 0 := by positivity
  have hnorm : ContDiffAt ℝ m (fun q : ℝ^n × ℝ ↦ ‖q.1‖ ^ 2) p :=
    contDiffAt_fst.norm_sq ℝ
  have hformula : ContDiffAt ℝ m
      (fun q : ℝ^n × ℝ ↦ (4 * Real.pi * q.2) ^ (-(n : ℝ) / 2) *
        Real.exp (-(‖q.1‖ ^ 2 / (4 * q.2)))) p :=
    ((contDiffAt_const.mul contDiffAt_snd).rpow_const_of_ne hbase).mul
      ((hnorm.div (contDiffAt_const.mul contDiffAt_snd) htime).neg.exp)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds ht)] with q hq
  simp [Function.uncurry_def, fundamentalSolutionHeat, hq.not_ge]

/-- Joint smoothness at every time when the spatial argument is nonzero. -/
theorem contDiffAt_fundamentalSolutionHeat_of_spatial_ne_zero {m : ℕ∞}
    {p : ℝ^n × ℝ} (hx : p.1 ≠ 0) :
    ContDiffAt ℝ m (Function.uncurry fundamentalSolutionHeat) p := by
  have hx2 : ‖p.1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hbase : Real.pi * ‖p.1‖ ^ 2 ≠ 0 := mul_ne_zero Real.pi_ne_zero hx2
  have hnorm : ContDiffAt ℝ m (fun q : ℝ^n × ℝ ↦ ‖q.1‖ ^ 2) p :=
    contDiffAt_fst.norm_sq ℝ
  have harg : ContDiffAt ℝ m (fun q : ℝ^n × ℝ ↦ 4 * q.2 / ‖q.1‖ ^ 2) p :=
    (contDiffAt_const.mul contDiffAt_snd).div hnorm hx2
  have hflat : ContDiffAt ℝ m
      (fun z : ℝ ↦ z ^ (-(n : ℝ) / 2) * expNegInvGlue z) (4 * p.2 / ‖p.1‖ ^ 2) :=
    (expNegInvGlue.contDiff_rpow_mul (m := m) (-(n : ℝ) / 2)).contDiffAt
  have hcomp : ContDiffAt ℝ m
      (fun q : ℝ^n × ℝ ↦ (4 * q.2 / ‖q.1‖ ^ 2) ^ (-(n : ℝ) / 2) *
        expNegInvGlue (4 * q.2 / ‖q.1‖ ^ 2)) p := by
    simpa only [Function.comp_def] using hflat.comp p harg
  have hformula : ContDiffAt ℝ m
      (fun q : ℝ^n × ℝ ↦ (Real.pi * ‖q.1‖ ^ 2) ^ (-(n : ℝ) / 2) *
        ((4 * q.2 / ‖q.1‖ ^ 2) ^ (-(n : ℝ) / 2) *
          expNegInvGlue (4 * q.2 / ‖q.1‖ ^ 2))) p :=
    ((contDiffAt_const.mul hnorm).rpow_const_of_ne hbase).mul hcomp
  apply hformula.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (eventually_ne_nhds hx)] with q hq
  exact fundamentalSolutionHeat_eq_rpow_mul_expNegInvGlue hq q.2

/-- The heat kernel, extended by zero to `t ≤ 0`, is smooth away from the spacetime origin. -/
theorem contDiffAt_fundamentalSolutionHeat {m : ℕ∞} {p : ℝ^n × ℝ}
    (hp : p ≠ 0) :
    ContDiffAt ℝ m (Function.uncurry fundamentalSolutionHeat) p := by
  rcases lt_trichotomy p.2 0 with ht | ht | ht
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually (gt_mem_nhds ht)] with q hq
    simp [Function.uncurry_def, fundamentalSolutionHeat, hq.le]
  · apply contDiffAt_fundamentalSolutionHeat_of_spatial_ne_zero
    intro hx
    exact hp (Prod.ext hx ht)
  · exact contDiffAt_fundamentalSolutionHeat_of_time_pos ht

/-- The heat kernel is `C^m` on spacetime minus the origin, for every `m : ℕ∞`. -/
theorem contDiffOn_fundamentalSolutionHeat {m : ℕ∞} :
    ContDiffOn ℝ m (Function.uncurry (fundamentalSolutionHeat (n := n))) ({0}ᶜ) :=
  fun _ hp ↦ (contDiffAt_fundamentalSolutionHeat hp).contDiffWithinAt

end HeatEquation
