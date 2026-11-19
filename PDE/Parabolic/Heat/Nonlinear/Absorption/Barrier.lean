/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Laplacian
public import PDE.Parabolic.Heat.Equation
import CAS.ExactTactic

/-!
# A rational supersolution for quadratic absorption

The barrier is linear in time and diverges at the boundary of a ball. Completing
a square controls its quadratic absorption residual. SymLean's `cas` tactic checks the
scalar calculations; the Laplacian uses the squared-radius formula `laplacian_comp_norm_sq`
in arbitrary dimension.
-/

@[expose] public noncomputable section

open Filter Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

/-- A rational barrier singular at the sphere of squared radius `b`. -/
def ballAbsorptionBarrier {n : ℕ} (a b : ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  a ^ 2 * t / (b - ‖x‖ ^ 2) ^ 4

/-- The barrier is spatially smooth away from its singular sphere. -/
theorem ballAbsorptionBarrier_contDiffAt {n : ℕ} (a b t : ℝ) {x : ℝ^n}
    (hx : b - ‖x‖ ^ 2 ≠ 0) :
    ContDiffAt ℝ 2 (fun y ↦ ballAbsorptionBarrier a b y t) x := by
  unfold ballAbsorptionBarrier
  exact contDiffAt_const.div
    ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).pow 4) (pow_ne_zero 4 hx)

/-- The time derivative of the rational barrier. -/
theorem ballAbsorptionBarrier_hasDerivAt {n : ℕ} (a b t : ℝ) (x : ℝ^n)
    (hx : b - ‖x‖ ^ 2 ≠ 0) :
    HasDerivAt (ballAbsorptionBarrier a b x) (a ^ 2 / (b - ‖x‖ ^ 2) ^ 4) t := by
  unfold ballAbsorptionBarrier
  generalize b - ‖x‖ ^ 2 = s at hx ⊢
  cas using hx

/-- The Laplacian of the rational barrier, valid also at the center. -/
theorem laplacian_ballAbsorptionBarrier {n : ℕ} (a b t : ℝ) (x : ℝ^n)
    (hx : b - ‖x‖ ^ 2 ≠ 0) :
    laplacian (fun y ↦ ballAbsorptionBarrier a b y t) x =
      80 * ‖x‖ ^ 2 * a ^ 2 * t / (b - ‖x‖ ^ 2) ^ 6 +
        8 * (n : ℝ) * a ^ 2 * t / (b - ‖x‖ ^ 2) ^ 5 := by
  have hfirst (r : ℝ) (hr : b - r ≠ 0) :
      deriv (fun s : ℝ ↦ a ^ 2 * t / (b - s) ^ 4) r =
        4 * a ^ 2 * t / (b - r) ^ 5 := by
    have hd : HasDerivAt (fun s : ℝ ↦ a ^ 2 * t / s ^ 4)
        (-4 * a ^ 2 * t / (b - r) ^ 5) (b - r) := by
      generalize b - r = q at hr ⊢
      cas using hr
    convert (HasDerivAt.comp_const_sub b r hd).deriv using 1
    generalize b - r = q at hr ⊢
    cas using hr
  have hsecond (r : ℝ) (hr : b - r ≠ 0) :
      deriv (deriv (fun s : ℝ ↦ a ^ 2 * t / (b - s) ^ 4)) r =
        20 * a ^ 2 * t / (b - r) ^ 6 := by
    have he : deriv (fun s : ℝ ↦ a ^ 2 * t / (b - s) ^ 4) =ᶠ[𝓝 r]
        fun s ↦ 4 * a ^ 2 * t / (b - s) ^ 5 := by
      filter_upwards [(continuous_const.sub continuous_id).continuousAt.eventually_ne hr]
        with s hs
      exact hfirst s hs
    rw [he.deriv_eq]
    have hd : HasDerivAt (fun s : ℝ ↦ 4 * a ^ 2 * t / s ^ 5)
        (-20 * a ^ 2 * t / (b - r) ^ 6) (b - r) := by
      generalize b - r = q at hr ⊢
      cas using hr
    convert (HasDerivAt.comp_const_sub b r hd).deriv using 1
    generalize b - r = q at hr ⊢
    cas using hr
  have hf : ContDiffAt ℝ 2 (fun s : ℝ ↦ a ^ 2 * t / (b - s) ^ 4) (‖x‖ ^ 2) :=
    contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).pow 4)
      (pow_ne_zero 4 hx)
  unfold ballAbsorptionBarrier
  rw [EuclideanLaplacian.laplacian_comp_norm_sq
    (fun s ↦ a ^ 2 * t / (b - s) ^ 4) x hf, hfirst _ hx, hsecond _ hx]
  generalize ‖x‖ ^ 2 = q at hx ⊢
  generalize (n : ℝ) = d
  generalize b - q = s at hx ⊢
  cas using hx

/-- Completing a square gives the absorption residual of the rational barrier. -/
theorem ballAbsorptionBarrier_residual_eq {n : ℕ} (a b t : ℝ) (x : ℝ^n)
    (hx : b - ‖x‖ ^ 2 ≠ 0) :
    heatParabolicOperator (ballAbsorptionBarrier a b) x t +
        ballAbsorptionBarrier a b x t ^ 2 =
      a ^ 2 / (b - ‖x‖ ^ 2) ^ 8 *
        (((b - ‖x‖ ^ 2) ^ 2 - a * t) ^ 2 +
          t * (b - ‖x‖ ^ 2) ^ 2 *
            (2 * a - (8 * (n : ℝ) * (b - ‖x‖ ^ 2) + 80 * ‖x‖ ^ 2))) := by
  unfold heatParabolicOperator
  rw [(ballAbsorptionBarrier_hasDerivAt a b t x hx).deriv,
    laplacian_ballAbsorptionBarrier a b t x hx]
  unfold ballAbsorptionBarrier
  generalize ‖x‖ ^ 2 = q at hx ⊢
  generalize (n : ℝ) = d
  generalize b - q = s at hx ⊢
  cas using hx

/-- A scalar coefficient bound makes the barrier a supersolution of quadratic
absorption, by the square-completion identity. -/
theorem ballAbsorptionBarrier_residual_nonneg {n : ℕ} {a b t : ℝ} (x : ℝ^n)
    (ht : 0 ≤ t) (hx : b - ‖x‖ ^ 2 ≠ 0)
    (ha : 8 * (n : ℝ) * (b - ‖x‖ ^ 2) + 80 * ‖x‖ ^ 2 ≤ 2 * a) :
    0 ≤ heatParabolicOperator (ballAbsorptionBarrier a b) x t +
      ballAbsorptionBarrier a b x t ^ 2 := by
  rw [ballAbsorptionBarrier_residual_eq a b t x hx]
  exact mul_nonneg (div_nonneg (sq_nonneg a) (by positivity))
    (add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg ht (sq_nonneg _)) (sub_nonneg.mpr ha)))

/-- The coefficient `(4n + 40)b` gives an absorption supersolution throughout
the ball of squared radius `b`. -/
theorem ballAbsorptionBarrier_supersolution {n : ℕ} {b t : ℝ} (x : ℝ^n)
    (ht : 0 ≤ t) (hx : ‖x‖ ^ 2 < b) :
    0 ≤ heatParabolicOperator (ballAbsorptionBarrier ((4 * (n : ℝ) + 40) * b) b)
      x t + ballAbsorptionBarrier ((4 * (n : ℝ) + 40) * b) b x t ^ 2 := by
  apply ballAbsorptionBarrier_residual_nonneg x ht (sub_pos.mpr hx).ne'
  have hdim : 0 ≤ 8 * (n : ℝ) * ‖x‖ ^ 2 := by positivity
  nlinarith

/-- At positive times the chosen ball barrier is a strict supersolution. -/
theorem ballAbsorptionBarrier_strict_supersolution {n : ℕ} {b t : ℝ} (x : ℝ^n)
    (ht : 0 < t) (hx : ‖x‖ ^ 2 < b) :
    0 < heatParabolicOperator (ballAbsorptionBarrier ((4 * (n : ℝ) + 40) * b) b)
      x t + ballAbsorptionBarrier ((4 * (n : ℝ) + 40) * b) b x t ^ 2 := by
  have hs : 0 < b - ‖x‖ ^ 2 := sub_pos.mpr hx
  have hb : 0 < b := (sq_nonneg ‖x‖).trans_lt hx
  have ha : 0 < (4 * (n : ℝ) + 40) * b := mul_pos (by positivity) hb
  rw [ballAbsorptionBarrier_residual_eq _ _ _ _ hs.ne']
  apply mul_pos (div_pos (sq_pos_of_pos ha) (pow_pos hs 8))
  apply add_pos_of_nonneg_of_pos (sq_nonneg _)
  apply mul_pos (mul_pos ht (sq_pos_of_pos hs))
  have hdim : 0 ≤ 8 * (n : ℝ) * ‖x‖ ^ 2 := by positivity
  nlinarith

end HeatEquation.Nonlinear
