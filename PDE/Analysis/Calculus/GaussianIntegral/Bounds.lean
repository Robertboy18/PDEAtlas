/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Common.Euclidean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Bounds for Gaussian integrals with linear parameters

The exponent `-a ‖y‖² + ⟪y,b⟫` is linear in `(a,b)`. On a neighborhood of any
parameter with `a > 0`, its exponential is bounded by a fixed integrable Gaussian.
Every polynomial weight remains integrable. These estimates allow repeated
differentiation without differentiability assumptions on the amplitude.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology

namespace PDE.Analysis.GaussianIntegral

variable {n : ℕ}

/-- The Gaussian exponent, viewed as a linear functional of its parameters. -/
def exponentCLM (y : ℝ^n) : (ℝ × ℝ^n) →L[ℝ] ℝ :=
  (-‖y‖ ^ 2) • ContinuousLinearMap.fst ℝ ℝ (ℝ^n) +
    (innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ^n))

@[simp]
theorem exponentCLM_apply (y : ℝ^n) (p : ℝ × ℝ^n) :
    exponentCLM y p = -p.1 * ‖y‖ ^ 2 + inner ℝ y p.2 := by
  simp [exponentCLM, mul_comm]

theorem continuous_exponentCLM : Continuous (exponentCLM (n := n)) := by
  unfold exponentCLM
  fun_prop

/-- Differentiating the exponential adds at most a quadratic weight. -/
theorem norm_exponentCLM_le (y : ℝ^n) :
    ‖exponentCLM y‖ ≤ 2 * (1 + ‖y‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  have hy : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  calc
    ‖exponentCLM y p‖ ≤ ‖p.1‖ * ‖y‖ ^ 2 + ‖y‖ * ‖p.2‖ := by
      rw [exponentCLM_apply]
      exact (norm_add_le _ _).trans (add_le_add
        (by simp [norm_mul]) (norm_inner_le_norm _ _))
    _ ≤ ‖p‖ * ‖y‖ ^ 2 + (1 + ‖y‖ ^ 2) * ‖p‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le p) (sq_nonneg _))
        (mul_le_mul hy (norm_snd_le p) (norm_nonneg _) (by positivity))
    _ ≤ 2 * (1 + ‖y‖ ^ 2) * ‖p‖ := by nlinarith [norm_nonneg p]

/-- All polynomial moments of a positive-rate Gaussian are integrable. -/
theorem integrable_polynomial_gaussian (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Integrable (fun y : ℝ^n ↦ (1 + ‖y‖ ^ 2) ^ k * Real.exp (-a * ‖y‖ ^ 2)) := by
  have hgauss (b : ℝ) (hb : 0 < b) :
      Integrable (fun y : ℝ^n ↦ Real.exp (-b * ‖y‖ ^ 2)) := by
    have h :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
        (ι := Fin n) (b := (b : ℂ)) (by simpa using hb) 0 0
    refine h.norm.congr (Filter.Eventually.of_forall fun y ↦ ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have hexp (b : ℝ) (hb : b < 0) :
      Integrable (fun y : ℝ^n ↦ Real.exp (b * (1 + ‖y‖ ^ 2))) := by
    convert (hgauss (-b) (neg_pos.mpr hb)).const_mul (Real.exp b) using 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  have hmoment := ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (X := fun y : ℝ^n ↦ 1 + ‖y‖ ^ 2) (v := -a) (t := a / 2)
    (by positivity) (hexp _ (by linarith)) (hexp _ (by linarith)) k
  convert hmoment.mul_const (Real.exp a) using 1
  funext y
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A single Gaussian controls all nearby parameters with positive quadratic rate. -/
theorem exists_local_gaussian_bound (p : ℝ × ℝ^n) (hp : 0 < p.1) :
    ∃ ε a C : ℝ, 0 < ε ∧ 0 < a ∧ 0 ≤ C ∧
      ∀ q ∈ Metric.ball p ε, ∀ y : ℝ^n,
        Real.exp (exponentCLM y q) ≤ C * Real.exp (-a * ‖y‖ ^ 2) := by
  let B : ℝ := ‖p.2‖ + 1
  refine ⟨min (p.1 / 2) 1, p.1 / 4, Real.exp (B ^ 2 / p.1),
    lt_min (half_pos hp) one_pos, by positivity, (Real.exp_pos _).le, ?_⟩
  intro q hq y
  have hd := Metric.mem_ball.mp hq
  rw [Prod.dist_eq] at hd
  have ht : p.1 / 2 ≤ q.1 := by
    have h := (le_max_left _ _).trans_lt (hd.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have hb : ‖q.2‖ ≤ B := by
    have h := (le_max_right _ _).trans_lt (hd.trans_le (min_le_right _ _))
    have htri := norm_add_le (q.2 - p.2) p.2
    rw [sub_add_cancel] at htri
    rw [dist_eq_norm] at h
    dsimp [B]
    linarith
  have hinner : inner ℝ y q.2 ≤ ‖y‖ * B :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hquad :
      -(p.1 / 2) * ‖y‖ ^ 2 + ‖y‖ * B ≤ B ^ 2 / p.1 - (p.1 / 4) * ‖y‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hp).mp
    have hcancel : B ^ 2 / p.1 * p.1 = B ^ 2 := div_mul_cancel₀ _ hp.ne'
    nlinarith [sq_nonneg (p.1 * ‖y‖ - 2 * B)]
  have he : exponentCLM y q ≤ B ^ 2 / p.1 - (p.1 / 4) * ‖y‖ ^ 2 := by
    rw [exponentCLM_apply]
    have hrate := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖y‖)
    linarith
  calc
    Real.exp (exponentCLM y q) ≤
        Real.exp (B ^ 2 / p.1 - (p.1 / 4) * ‖y‖ ^ 2) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring

end PDE.Analysis.GaussianIntegral
