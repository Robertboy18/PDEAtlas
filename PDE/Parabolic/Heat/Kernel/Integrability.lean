/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Probability.Moments.IntegrableExpMul
import CAS.ExactTactic

/-!
# Integrability and mass of the Euclidean heat kernel

For each `t > 0` the heat kernel `Φ(x, t) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` has total spatial
mass one, `∫ Φ(x, t) dx = 1` (Evans, PDE, §2.3.1, the lemma on the integral of the fundamental
solution). The normalising constant `(4πt)^(-n/2)` is exactly the reciprocal of the Gaussian
integral `∫ exp(-‖x‖² / (4t)) dx = (4πt)^(n/2)`, which is Mathlib's
`GaussianFourier.integral_rexp_neg_mul_sq_norm` with rate `b = 1 / (4t)`.

The integrability and moment statements come from the same Gaussian:
`exp(-b‖w‖²)` and `‖w‖² exp(-b‖w‖²)` are integrable for `b > 0`.
Translation invariance of Lebesgue measure moves the centre to any point `x`,
and the kernel itself is integrable because its integral is nonzero.

## Main results

* `integrable_exp_neg_mul_sq_norm_sub_left`: `y ↦ exp(-b‖x - y‖²)` is integrable for `b > 0`.
* `fundamentalSolutionHeat_integral`: unit mass of the kernel at every positive time.
* `integral_norm_sq_mul_fundamentalSolutionHeat_one`: the time-one second moment is `2n`.
* `fundamentalSolutionHeat_integrable`: spatial integrability of the kernel at every positive
  time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Lemma (Integral of fundamental solution).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Topology

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-! ## Gaussian integrability -/

private theorem integrable_exp_neg_mul_sq_norm (b : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun w : ℝ^n ↦ Real.exp (-b * ‖w‖ ^ 2))
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))) := by
  have hcomplex :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      (ι := Fin n) (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hcomplex.norm.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

private theorem integrable_norm_sq_mul_exp_neg_mul_sq_norm
    (b : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun w : ℝ^n ↦ ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2))
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))) := by
  have hplus :
      MeasureTheory.Integrable
        (fun w : ℝ^n ↦
          Real.exp ((-b + b / 2) * ‖w‖ ^ 2)) := by
    convert integrable_exp_neg_mul_sq_norm (n := n) (b / 2) (by positivity) using 1
    funext w
    congr 1
    ring
  have hminus :
      MeasureTheory.Integrable
        (fun w : ℝ^n ↦
          Real.exp ((-b - b / 2) * ‖w‖ ^ 2)) := by
    convert
      integrable_exp_neg_mul_sq_norm (n := n) (3 * b / 2) (by positivity)
        using 1
    funext w
    congr 1
    ring
  simpa [pow_one] using
    (ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
      (X := fun w : ℝ^n ↦ ‖w‖ ^ 2)
      (v := -b) (t := b / 2)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n)))
      (by positivity) hplus hminus 1)

private theorem integral_neg_norm_sq_mul_exp_neg_mul_sq_norm
    (b : ℝ) (hb : 0 < b) :
    ∫ w : ℝ^n, (-‖w‖ ^ 2) * Real.exp (-b * ‖w‖ ^ 2) =
      (-Real.pi / b ^ 2) * ((n : ℝ) / 2) *
        (Real.pi / b) ^ ((n : ℝ) / 2 - 1) := by
  let F : ℝ → ℝ^n → ℝ :=
    fun c w ↦ Real.exp (-c * ‖w‖ ^ 2)
  let F' : ℝ → ℝ^n → ℝ :=
    fun c w ↦ (-‖w‖ ^ 2) * Real.exp (-c * ‖w‖ ^ 2)
  let bound : ℝ^n → ℝ :=
    fun w ↦ ‖w‖ ^ 2 * Real.exp (-(b / 2) * ‖w‖ ^ 2)
  have hFmeas :
      ∀ᶠ c in 𝓝 b, MeasureTheory.AEStronglyMeasurable (F c) :=
    Filter.Eventually.of_forall fun c ↦
      (by fun_prop : Continuous (F c)).aestronglyMeasurable
  have hFint : MeasureTheory.Integrable (F b) := by
    simpa [F] using integrable_exp_neg_mul_sq_norm (n := n) b hb
  have hF'meas : MeasureTheory.AEStronglyMeasurable (F' b) :=
    (by fun_prop : Continuous (F' b)).aestronglyMeasurable
  have hbound : MeasureTheory.Integrable bound := by
    simpa [bound] using
      integrable_norm_sq_mul_exp_neg_mul_sq_norm
        (n := n) (b / 2) (by positivity)
  have hdom :
      ∀ᵐ w, ∀ c ∈ Metric.ball b (b / 2), ‖F' c w‖ ≤ bound w :=
    Filter.Eventually.of_forall fun w c hc ↦ by
      have hdist : |c - b| < b / 2 := by simpa [Real.dist_eq] using hc
      have hbc : b / 2 ≤ c := by linarith [(abs_lt.mp hdist).1]
      dsimp only [F', bound]
      rw [norm_mul, norm_neg, Real.norm_of_nonneg (sq_nonneg _),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
  have hdiff :
      ∀ᵐ w, ∀ c ∈ Metric.ball b (b / 2),
        HasDerivAt (F · w) (F' c w) c :=
    Filter.Eventually.of_forall fun w c _ ↦ by
      dsimp only [F, F']
      cas
  have hintegral :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := bound) (F := F) (F' := F')
      (Metric.ball_mem_nhds b (by positivity : 0 < b / 2))
      hFmeas hFint hF'meas hdom hbound hdiff
  have hclosedForm :
      HasDerivAt (fun c : ℝ ↦ (Real.pi / c) ^ ((n : ℝ) / 2))
        ((-Real.pi / b ^ 2) * ((n : ℝ) / 2) *
          (Real.pi / b) ^ ((n : ℝ) / 2 - 1)) b := by
    cas using hb
  have heq :
      (fun c : ℝ ↦ ∫ w, F c w) =ᶠ[𝓝 b]
        fun c : ℝ ↦ (Real.pi / c) ^ ((n : ℝ) / 2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hb] with c hc
    simpa [F] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := ℝ^n) (b := c) hc)
  simpa [F'] using hintegral.2.unique (hclosedForm.congr_of_eventuallyEq heq)

private theorem integral_norm_sq_mul_exp_neg_mul_sq_norm
    (b : ℝ) (hb : 0 < b) :
    ∫ w : ℝ^n, ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2) =
      ((n : ℝ) / (2 * b)) *
        (Real.pi / b) ^ ((n : ℝ) / 2) := by
  have hnegative :=
    integral_neg_norm_sq_mul_exp_neg_mul_sq_norm (n := n) b hb
  have hintegral :
      (∫ w : ℝ^n, (-‖w‖ ^ 2) * Real.exp (-b * ‖w‖ ^ 2)) =
        -(∫ w : ℝ^n, ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) := by
    rw [← MeasureTheory.integral_neg]
    simp only [neg_mul]
  rw [hintegral] at hnegative
  rw [show (Real.pi / b) ^ ((n : ℝ) / 2) =
      (Real.pi / b) ^ (((n : ℝ) / 2 - 1) + 1) by ring_nf,
    Real.rpow_add (by positivity), Real.rpow_one]
  linear_combination -hnegative

/-- The Gaussian `y ↦ exp(-b‖x - y‖²)` centred at `x` is integrable on `ℝ^n` for every rate
`b > 0`. Lebesgue measure is invariant under `y ↦ x - y`, so this is the centred Gaussian
integrability transported to an arbitrary centre. -/
theorem integrable_exp_neg_mul_sq_norm_sub_left (x : ℝ^n) (b : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun y : ℝ^n ↦ Real.exp (-b * ‖x - y‖ ^ 2))
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))) := by
  let μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))
  have h0 : MeasureTheory.Integrable (fun w : (ℝ^n) ↦ Real.exp (-b * ‖w‖ ^ 2)) (μ := μ) :=
    integrable_exp_neg_mul_sq_norm (n := n) b hb
  change MeasureTheory.Integrable
    (fun y : (ℝ^n) ↦ Real.exp (-b * ‖x - y‖ ^ 2)) (μ := μ)
  rw [show (fun y : (ℝ^n) ↦ Real.exp (-b * ‖x - y‖ ^ 2)) =
    (fun w : (ℝ^n) ↦ Real.exp (-b * ‖w‖ ^ 2)) ∘ fun y ↦ x - y by rfl]
  exact (μ.measurePreserving_sub_left x).integrable_comp_of_integrable h0

/-! ## Unit mass -/

/-- Integral of the fundamental solution equals `1` for each `t > 0`. -/
theorem fundamentalSolutionHeat_integral (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ^n, fundamentalSolutionHeat (n := n) x t = 1 := by
  have hgauss : (∫ x : ℝ^n, Real.exp (-(‖x‖ ^ 2 / (4 * t)))) =
      (4 * Real.pi * t) ^ ((n : ℝ) / 2) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ^n) (b := (4 * t)⁻¹) (by positivity)
  calc (∫ x : ℝ^n, fundamentalSolutionHeat (n := n) x t)
      = ∫ x : ℝ^n, (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 / (4 * t))) := by
        simp [fundamentalSolutionHeat, not_le.mpr ht, mul_assoc]
    _ = 1 := by
      rw [MeasureTheory.integral_const_mul, hgauss, neg_div, Real.rpow_neg (by positivity),
        inv_mul_cancel₀ (by positivity)]

/-- The quadratic spatial moment of the time-one heat kernel is `2n`. -/
theorem integral_norm_sq_mul_fundamentalSolutionHeat_one (n : ℕ) :
    ∫ w : ℝ^n, ‖w‖ ^ 2 * fundamentalSolutionHeat (n := n) w 1 =
      2 * (n : ℝ) := by
  calc
    ∫ w : ℝ^n, ‖w‖ ^ 2 * fundamentalSolutionHeat (n := n) w 1 =
        (4 * Real.pi) ^ (-(n : ℝ) / 2) *
          ∫ w : ℝ^n,
            ‖w‖ ^ 2 * Real.exp (-(1 / 4 : ℝ) * ‖w‖ ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with w
      norm_num [fundamentalSolutionHeat]
      ring_nf
    _ = (4 * Real.pi) ^ (-(n : ℝ) / 2) *
        (((n : ℝ) / (2 * (1 / 4 : ℝ))) *
          (Real.pi / (1 / 4 : ℝ)) ^ ((n : ℝ) / 2)) := by
      rw [integral_norm_sq_mul_exp_neg_mul_sq_norm
        (n := n) (1 / 4) (by norm_num)]
    _ = 2 * (n : ℝ) := by
      have hfourPi : (0 : ℝ) < 4 * Real.pi := by positivity
      rw [show Real.pi / (1 / 4 : ℝ) = 4 * Real.pi by field_simp]
      rw [show (4 * Real.pi) ^ (-(n : ℝ) / 2) *
          ((n : ℝ) / (2 * (1 / 4 : ℝ)) *
            (4 * Real.pi) ^ ((n : ℝ) / 2)) =
          ((n : ℝ) / (2 * (1 / 4 : ℝ))) *
            ((4 * Real.pi) ^ (-(n : ℝ) / 2) *
              (4 * Real.pi) ^ ((n : ℝ) / 2)) by ring]
      rw [← Real.rpow_add hfourPi,
        show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring,
        Real.rpow_zero]
      ring

/-- The fundamental solution is integrable in the spatial variables for each `t > 0`. -/
theorem fundamentalSolutionHeat_integrable (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun x : ℝ^n ↦ fundamentalSolutionHeat (n := n) x t)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ^n))) := by
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [fundamentalSolutionHeat_integral (n := n) t ht]
  exact one_ne_zero

end HeatEquation
