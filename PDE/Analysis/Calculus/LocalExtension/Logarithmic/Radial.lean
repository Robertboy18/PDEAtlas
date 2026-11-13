/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Scalar

import CAS.ExactTactic

/-!
# A radial logarithmic cutoff through the squared norm

Composing the scalar profile with the globally smooth squared norm avoids any
regularity question for the norm at zero. Squaring the outer radius and doubling
the logarithmic width preserves the inner radius `δ * exp (-L)`.

The constant in the scalar theorem also bounds the weighted first derivative.
Three times that constant bounds the full second Fréchet derivative. Neither
estimate requires finite dimension or completeness; finite dimension is used
only for the compact-support corollary.
-/

@[expose] public noncomputable section

open Function Set Metric
open scoped ContDiff

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar logarithmic profile composed with the squared norm, with outer
radius `δ` and inner radius `δ * Real.exp (-L)` for positive parameters. -/
def radialLogarithmicCutoff (δ L : ℝ) (x : E) : ℝ :=
  logarithmicCutoff (δ ^ 2) (2 * L) (‖x‖ ^ 2)

-- The derivative of the squared norm is a linear family of linear functionals.
-- Differentiating its scalar multiple gives the entire bilinear second derivative.
private theorem radialLogarithmicCutoff_derivative_norms {δ L : ℝ}
    (hχ : ContDiff ℝ 2 (logarithmicCutoff (δ ^ 2) (2 * L))) (x : E) :
    ‖fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ) x‖ =
        2 * ‖x‖ * |deriv (logarithmicCutoff (δ ^ 2) (2 * L)) (‖x‖ ^ 2)| ∧
      ‖fderiv ℝ (fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ)) x‖ ≤
        4 * ‖x‖ ^ 2 * |deriv (deriv (logarithmicCutoff (δ ^ 2) (2 * L)))
          (‖x‖ ^ 2)| +
        2 * |deriv (logarithmicCutoff (δ ^ 2) (2 * L)) (‖x‖ ^ 2)| := by
  let χ : ℝ → ℝ := logarithmicCutoff (δ ^ 2) (2 * L)
  let J : E →L[ℝ] E →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ
  have hJx (y : E) : ‖J y‖ = 2 * ‖y‖ := by
    simp only [J, smul_apply, norm_smul, Real.norm_ofNat,
      innerSL_apply_norm ℝ y]
  have hJ : ‖J‖ ≤ 2 := by
    calc
      ‖J‖ ≤ 2 * ‖innerSL ℝ (E := E)‖ := by
        simpa only [J, Real.norm_ofNat] using
          ContinuousLinearMap.opNorm_smul_le (2 : ℝ) (innerSL ℝ (E := E))
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
        (norm_innerSL_le (𝕜 := ℝ) (E := E)) (by norm_num)
      _ = 2 := by norm_num
  have hq (y : E) : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2) (J y) y := by
    simpa only [J, smul_apply, two_smul] using
      (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hfirst (y : E) : fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ) y =
      deriv χ (‖y‖ ^ 2) • J y := by
    exact ((hχ.differentiable (by norm_num) (‖y‖ ^ 2)).hasDerivAt.comp_hasFDerivAt
      y (hq y)).fderiv
  have hsecond : fderiv ℝ (fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ)) x =
      deriv χ (‖x‖ ^ 2) • J +
        (deriv (deriv χ) (‖x‖ ^ 2) • J x).smulRight (J x) := by
    have hcoefficient : HasFDerivAt (fun y : E ↦ deriv χ (‖y‖ ^ 2))
        (deriv (deriv χ) (‖x‖ ^ 2) • J x) x := by
      exact (hχ.differentiable_deriv_two (‖x‖ ^ 2)).hasDerivAt.comp_hasFDerivAt x (hq x)
    rw [show fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ) =
      (fun y : E ↦ deriv χ (‖y‖ ^ 2) • J y) from funext hfirst]
    exact (hcoefficient.smul J.hasFDerivAt).fderiv
  constructor
  · rw [hfirst x, norm_smul, hJx x, Real.norm_eq_abs]
    cas
  · rw [hsecond]
    calc
      ‖deriv χ (‖x‖ ^ 2) • J +
          (deriv (deriv χ) (‖x‖ ^ 2) • J x).smulRight (J x)‖ ≤
          ‖deriv χ (‖x‖ ^ 2) • J‖ +
            ‖(deriv (deriv χ) (‖x‖ ^ 2) • J x).smulRight (J x)‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ |deriv χ (‖x‖ ^ 2)| * ‖J‖ +
          (|deriv (deriv χ) (‖x‖ ^ 2)| * (2 * ‖x‖)) * (2 * ‖x‖) := by
        refine add_le_add ?_ (le_of_eq ?_)
        · simpa only [Real.norm_eq_abs] using
            ContinuousLinearMap.opNorm_smul_le (deriv χ (‖x‖ ^ 2)) J
        · simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, hJx,
            Real.norm_eq_abs]
      _ ≤ |deriv χ (‖x‖ ^ 2)| * 2 +
          (|deriv (deriv χ) (‖x‖ ^ 2)| * (2 * ‖x‖)) * (2 * ‖x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hJ (abs_nonneg _)) le_rfl
      _ = 4 * ‖x‖ ^ 2 * |deriv (deriv χ) (‖x‖ ^ 2)| +
          2 * |deriv χ (‖x‖ ^ 2)| := by cas

/-- The scalar cutoff's fixed constant controls the weighted operator norms of
both radial derivatives, uniformly over outer radius and logarithmic width.
The second derivative is measured as a continuous bilinear map. -/
theorem exists_pos_radialLogarithmicCutoff_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ δ L : ℝ, 0 < δ → 1 ≤ L →
      ContDiff ℝ ∞ (radialLogarithmicCutoff δ L : E → ℝ) ∧
      (∀ x : E, ‖x‖ ≤ δ * Real.exp (-L) → radialLogarithmicCutoff δ L x = 1) ∧
      (∀ x : E, δ ≤ ‖x‖ → radialLogarithmicCutoff δ L x = 0) ∧
      (∀ x : E, radialLogarithmicCutoff δ L x ∈ Icc (0 : ℝ) 1) ∧
      tsupport (radialLogarithmicCutoff δ L : E → ℝ) ⊆ closedBall (0 : E) δ ∧
      (∀ x : E, x ≠ 0 →
        ‖x‖ * ‖fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ) x‖ ≤ C / L ∧
        ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ
          (radialLogarithmicCutoff δ L : E → ℝ)) x‖ ≤ 3 * C / L) := by
  obtain ⟨C, hC, hscalar⟩ := exists_pos_logarithmicCutoff_bounds
  refine ⟨C, hC, ?_⟩
  intro δ L hδ hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hwidth : 1 ≤ 2 * L := by cas using [hL]
  obtain ⟨_, _, hχ, hinner, houter, hrange, hweighted⟩ :=
    hscalar (δ ^ 2) (2 * L) (sq_pos_of_pos hδ) hwidth
  have hεsq : (δ * Real.exp (-L)) ^ 2 = δ ^ 2 * Real.exp (-(2 * L)) := by
    rw [mul_pow, show -(2 * L) = -L + -L by cas, Real.exp_add]
    simp only [pow_two]
  have hone (x : E) (hx : ‖x‖ ≤ δ * Real.exp (-L)) :
      radialLogarithmicCutoff δ L x = 1 := by
    apply hinner
    rw [← hεsq]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hzero (x : E) (hx : δ ≤ ‖x‖) : radialLogarithmicCutoff δ L x = 0 :=
    houter _ (pow_le_pow_left₀ hδ.le hx 2)
  have hsupport : tsupport (radialLogarithmicCutoff δ L : E → ℝ) ⊆
      closedBall (0 : E) δ := by
    change closure (Function.support (radialLogarithmicCutoff δ L : E → ℝ)) ⊆ _
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    by_contra hxδ
    exact hx (hzero x (lt_of_not_ge hxδ).le)
  refine ⟨hχ.comp (contDiff_norm_sq ℝ), hone, hzero, (fun x ↦ hrange (‖x‖ ^ 2)),
    hsupport, ?_⟩
  intro x hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hw := hweighted (‖x‖ ^ 2) (sq_pos_of_pos hr)
  obtain ⟨hfirst, hsecond⟩ :=
    radialLogarithmicCutoff_derivative_norms (hχ.of_le (by simp)) x
  constructor
  · calc
      ‖x‖ * ‖fderiv ℝ (radialLogarithmicCutoff δ L : E → ℝ) x‖ =
          2 * (‖x‖ ^ 2 * |deriv (logarithmicCutoff (δ ^ 2) (2 * L)) (‖x‖ ^ 2)|) := by
        rw [hfirst]
        cas
      _ ≤ 2 * (C / (2 * L)) := mul_le_mul_of_nonneg_left hw.1 (by norm_num)
      _ = C / L := by cas using [hLpos]
  · calc
      ‖x‖ ^ 2 * ‖fderiv ℝ (fderiv ℝ
          (radialLogarithmicCutoff δ L : E → ℝ)) x‖ ≤
          ‖x‖ ^ 2 * (4 * ‖x‖ ^ 2 *
            |deriv (deriv (logarithmicCutoff (δ ^ 2) (2 * L))) (‖x‖ ^ 2)| +
            2 * |deriv (logarithmicCutoff (δ ^ 2) (2 * L)) (‖x‖ ^ 2)|) :=
        mul_le_mul_of_nonneg_left hsecond (sq_nonneg ‖x‖)
      _ = 4 * ((‖x‖ ^ 2) ^ 2 *
            |deriv (deriv (logarithmicCutoff (δ ^ 2) (2 * L))) (‖x‖ ^ 2)|) +
          2 * (‖x‖ ^ 2 * |deriv (logarithmicCutoff (δ ^ 2) (2 * L)) (‖x‖ ^ 2)|) := by
        cas
      _ ≤ 4 * (C / (2 * L)) + 2 * (C / (2 * L)) := add_le_add
        (mul_le_mul_of_nonneg_left hw.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hw.1 (by norm_num))
      _ = 3 * C / L := by cas using [hLpos]

/-- In finite dimension, the closed-ball support bound gives compact support. -/
theorem hasCompactSupport_radialLogarithmicCutoff [FiniteDimensional ℝ E]
    {δ L : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L) :
    HasCompactSupport (radialLogarithmicCutoff δ L : E → ℝ) := by
  obtain ⟨_, _, hbounds⟩ := exists_pos_radialLogarithmicCutoff_bounds (E := E)
  obtain ⟨_, _, _, _, hsupport, _⟩ := hbounds δ L hδ hL
  exact (isCompact_closedBall (0 : E) δ).of_isClosed_subset
    (isClosed_tsupport _) hsupport

end PDE.Analysis
