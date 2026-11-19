/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

import CAS.ExactTactic

/-!
# The fast log-cosh law

The fixed law `kδ(s) = 2s + δ log(cosh s)` is smooth on the whole real line.
Its first derivative stays within `|δ|` of two. Its second derivative is
`δ / cosh(s)²`, which is strictly positive everywhere when `δ > 0`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open scoped ContDiff

/-- The fast scalar law, with its linear coefficient fixed at two. -/
def fastLogCosh (δ s : ℝ) : ℝ :=
  2 * s + δ * Real.log (Real.cosh s)

/-- The fast law is smooth jointly in its parameter and state on the whole plane. -/
theorem contDiff_fastLogCosh_joint :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ fastLogCosh p.1 p.2) := by
  unfold fastLogCosh
  exact (contDiff_const.mul contDiff_snd).add
    (contDiff_fst.mul ((Real.contDiff_cosh.comp contDiff_snd).log
      (fun p ↦ (Real.cosh_pos p.2).ne')))

/-- The logarithm is smooth globally because `cosh` never vanishes. -/
theorem contDiff_fastLogCosh (δ : ℝ) : ContDiff ℝ ∞ (fastLogCosh δ) :=
  contDiff_fastLogCosh_joint.comp₂ (contDiff_const (c := δ)) contDiff_id

/-- The first derivative of the fast law, for arbitrary real parameters. -/
theorem hasDerivAt_fastLogCosh (δ s : ℝ) :
    HasDerivAt (fastLogCosh δ) (2 + δ * Real.tanh s) s := by
  unfold fastLogCosh
  have hcosh : 0 < Real.cosh s := Real.cosh_pos s
  cas using hcosh

/-- The ordinary derivative agrees with the explicit hyperbolic formula. -/
theorem deriv_fastLogCosh (δ s : ℝ) :
    deriv (fastLogCosh δ) s = 2 + δ * Real.tanh s :=
  (hasDerivAt_fastLogCosh δ s).deriv

/-- Differentiating the first derivative gives the reciprocal-square formula. -/
theorem hasDerivAt_deriv_fastLogCosh (δ s : ℝ) :
    HasDerivAt (deriv (fastLogCosh δ)) (δ / Real.cosh s ^ 2) s := by
  have hfirst : deriv (fastLogCosh δ) = fun t ↦ 2 + δ * Real.tanh t := funext (deriv_fastLogCosh δ)
  rw [hfirst]
  have hcosh : 0 < Real.cosh s := Real.cosh_pos s
  cas using hcosh

/-- The second derivative formula holds at every real state, including zero. -/
theorem deriv_deriv_fastLogCosh (δ s : ℝ) :
    deriv (deriv (fastLogCosh δ)) s = δ / Real.cosh s ^ 2 :=
  (hasDerivAt_deriv_fastLogCosh δ s).deriv

/-- The slope perturbation is bounded uniformly over all real states. -/
theorem abs_deriv_fastLogCosh_sub_two_le (δ s : ℝ) :
    |deriv (fastLogCosh δ) s - 2| ≤ |δ| := by
  rw [deriv_fastLogCosh, add_sub_cancel_left, abs_mul]
  calc
    |δ| * |Real.tanh s| ≤ |δ| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one s).le (abs_nonneg δ)
    _ = |δ| := mul_one _

/-- Perturbations of magnitude less than one quarter keep the slope above `7/4`. -/
theorem seven_fourths_lt_deriv_fastLogCosh {δ : ℝ} (hδ : |δ| < 1 / 4) (s : ℝ) :
    7 / 4 < deriv (fastLogCosh δ) s := by
  have h := (abs_lt.mp (lt_of_le_of_lt (abs_deriv_fastLogCosh_sub_two_le δ s) hδ)).1
  linarith

/-- Perturbations of magnitude less than one quarter keep the slope below `9/4`. -/
theorem deriv_fastLogCosh_lt_nine_fourths {δ : ℝ} (hδ : |δ| < 1 / 4) (s : ℝ) :
    deriv (fastLogCosh δ) s < 9 / 4 := by
  have h := (abs_lt.mp (lt_of_le_of_lt (abs_deriv_fastLogCosh_sub_two_le δ s) hδ)).2
  linarith

/-- Every positive perturbation has strictly positive second derivative everywhere. -/
theorem deriv_deriv_fastLogCosh_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 < deriv (deriv (fastLogCosh δ)) s := by
  rw [deriv_deriv_fastLogCosh]
  exact div_pos hδ (pow_pos (Real.cosh_pos s) 2)

end PDE.Analysis
