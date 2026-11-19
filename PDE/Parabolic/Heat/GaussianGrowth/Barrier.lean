/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation
public import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic

/-!
# Growing Gaussian barriers for the heat equation

The function `exp ((b * ‖x‖² + 1) / (1 - c * t))` is a heat supersolution before
its denominator vanishes, provided `c ≥ 4b` and `c ≥ 2nb`. Its spatial growth
dominates `exp (b * ‖x‖²)` for nonnegative time. These two facts allow comparison
on large balls without assuming that the solution is bounded on the whole space.
SymLean's `cas` tactic computes the time derivative and the Laplacian profile and checks
the supersolution identity.
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace HeatEquation

open Set

/-- A growing Gaussian, used before the time `1 / c`. -/
def growingGaussian {n : ℕ} (b c : ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  Real.exp ((b * ‖x‖ ^ 2 + 1) / (1 - c * t))

/-- The growing Gaussian is positive. -/
theorem growingGaussian_pos {n : ℕ} (b c : ℝ) (x : ℝ^n) (t : ℝ) :
    0 < growingGaussian b c x t :=
  Real.exp_pos _

/-- Spatial smoothness does not require a nonzero denominator: division is by a constant. -/
theorem growingGaussian_contDiff_space {n : ℕ} (b c t : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ^n ↦ growingGaussian b c x t) := by
  unfold growingGaussian
  have hq : ContDiff ℝ ⊤ (fun x : ℝ^n ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact ((contDiff_const.mul hq).add contDiff_const).div_const _ |>.exp

/-- The first time derivative of the growing Gaussian. -/
theorem growingGaussian_hasDerivAt {n : ℕ} (b c : ℝ) (x : ℝ^n) (t : ℝ)
    (ht : 1 - c * t ≠ 0) :
    HasDerivAt (growingGaussian b c x)
      (growingGaussian b c x t * (c * (b * ‖x‖ ^ 2 + 1) / (1 - c * t) ^ 2)) t := by
  unfold growingGaussian
  generalize b * ‖x‖ ^ 2 + 1 = q
  cas using ht

/-- The spatial Laplacian of a growing Gaussian, including at the origin. -/
theorem laplacian_growingGaussian {n : ℕ} (b c : ℝ) (x : ℝ^n) (t : ℝ)
    (ht : 1 - c * t ≠ 0) :
    laplacian (fun y ↦ growingGaussian b c y t) x =
      growingGaussian b c x t *
        (4 * ‖x‖ ^ 2 * b ^ 2 / (1 - c * t) ^ 2 + 2 * n * b / (1 - c * t)) := by
  have hfirst (r : ℝ) :
      deriv (fun s : ℝ ↦ Real.exp ((b * s + 1) / (1 - c * t))) r =
        Real.exp ((b * r + 1) / (1 - c * t)) * b / (1 - c * t) := by
    cas using ht
  have hsecond (r : ℝ) :
      deriv (deriv (fun s : ℝ ↦ Real.exp ((b * s + 1) / (1 - c * t)))) r =
        Real.exp ((b * r + 1) / (1 - c * t)) * b ^ 2 / (1 - c * t) ^ 2 := by
    cas using ht
  unfold growingGaussian
  rw [EuclideanLaplacian.laplacian_comp_norm_sq
    (fun s ↦ Real.exp ((b * s + 1) / (1 - c * t))) x (by fun_prop)]
  rw [hfirst, hsecond]
  ring

/-- For suitable coefficients the growing Gaussian is a classical heat supersolution. -/
theorem growingGaussian_supersolution {n : ℕ} {b c t : ℝ} (x : ℝ^n)
    (hb : 0 ≤ b) (hc₁ : 4 * b ≤ c) (hc₂ : 2 * n * b ≤ c)
    (ht : 0 ≤ t) (hden : 0 < 1 - c * t) :
    0 ≤ heatParabolicOperator (growingGaussian b c) x t := by
  have hc : 0 ≤ c := (by positivity : 0 ≤ 4 * b).trans hc₁
  have hden_le : 1 - c * t ≤ 1 := sub_le_self _ (mul_nonneg hc ht)
  have hquad : 0 ≤ (c * b - 4 * b ^ 2) * ‖x‖ ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hconst : 0 ≤ c - 2 * n * b * (1 - c * t) := by
    have := mul_le_mul_of_nonneg_left hden_le (by positivity : 0 ≤ 2 * (n : ℝ) * b)
    nlinarith
  unfold heatParabolicOperator
  rw [(growingGaussian_hasDerivAt b c x t hden.ne').deriv,
    laplacian_growingGaussian b c x t hden.ne']
  have hid (q e : ℝ) :
      e * (c * (b * q + 1) / (1 - c * t) ^ 2) -
          e * (4 * q * b ^ 2 / (1 - c * t) ^ 2 + 2 * n * b / (1 - c * t)) =
        e / (1 - c * t) ^ 2 * ((c * b - 4 * b ^ 2) * q +
          (c - 2 * n * b * (1 - c * t))) := by
    cas using hden.ne'
  rw [hid]
  exact mul_nonneg (div_nonneg (growingGaussian_pos b c x t).le (sq_nonneg _))
    (add_nonneg hquad hconst)

/-- On its forward interval the barrier dominates a fixed growing Gaussian. -/
theorem exp_norm_sq_le_growingGaussian {n : ℕ} {b c t : ℝ} (x : ℝ^n)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t) (hden : 0 < 1 - c * t) :
    Real.exp (b * ‖x‖ ^ 2) ≤ growingGaussian b c x t := by
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ hden).mpr
  have hq : 0 ≤ b * ‖x‖ ^ 2 := mul_nonneg hb (sq_nonneg _)
  nlinarith [mul_nonneg hq (mul_nonneg hc ht)]

end HeatEquation
