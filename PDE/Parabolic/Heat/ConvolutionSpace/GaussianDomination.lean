/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Parabolic.Heat.Kernel.SpatialDerivatives
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import PDE.Parabolic.Heat.Kernel.Integrability
import CAS.ExactTactic

/-!
# Gaussian domination for heat-kernel convolutions

Differentiating `x ↦ ∫ Γ(x - y, t) g(y) dy` under the integral sign, where
`Γ(z, t) = (4πt)^(-n/2) exp(-‖z‖²/(4t))` is the heat kernel and `g` is bounded, requires
one integrable function dominating the derivative kernels for all `x'` near `x` (and, for
the joint derivative, for all `(t', x')` near `(t, x)`). The mechanism is the elementary
inequality `‖x' - y‖² ≥ ‖x - y‖²/2 - ‖x - x'‖²`: a kernel centred at a nearby point is
bounded by a slower Gaussian centred at `x`, and the polynomial factors produced by the
gradient and Hessian are absorbed by giving up a further factor in the Gaussian exponent.
The results are those majorants and the Bochner integrability of the gradient and Hessian
kernels against bounded continuous data.

In step 1 of the proof of Theorem 1 in §2.3.1, Evans differentiates under the integral sign
after noting that the kernel is smooth with uniformly bounded derivatives of all orders on
`ℝ^n × [δ, ∞)`. For bounded `g` this needs an integrable majorant, and we write one out. Two
constants are fixed by hand: the Gaussian rate `b = 1/(16 t)` for the spatial
majorant and `b = 1/(24 t)` for the joint one, each half of the rate that
`heatKernel_local_gaussian_bound` leaves after `8t` or `12t`, and that half is what
`quadratic_mul_exp_le_exp` spends to absorb the polynomial factor `r² + 1`.

## Main results

* `heatKernel_local_gaussian_bound`: for `‖x' - x‖ ≤ 1`,
  `Γ(x' - y, t) ≤ (4πt)^(-n/2) e^(1/(4t)) exp(-‖x - y‖²/(8t))`.
* `exists_integrable_bound_heatKernelHessian`: an integrable majorant, uniform over
  `x' ∈ ball x 1`, for both the gradient kernel and the Hessian kernel weighted by `g`.
* `exists_integrable_bound_heatKernel_timeSpace`: an integrable majorant, uniform over a
  neighbourhood of `(t, x)`, for the joint time-space derivative kernel.
* `integrable_heatKernel_gradient`, `integrable_heatKernelHessian_coord`: Bochner
  integrability of the gradient kernel and of each evaluated Hessian slot.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 1 and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

namespace ConvolutionSpace

/-- A quadratic polynomial times a faster Gaussian is bounded by a constant times a slower
Gaussian. This elementary estimate supplies the integrable majorant for second spatial
derivatives of heat-kernel convolutions. -/
private theorem quadratic_mul_exp_le_exp {b r : ℝ} (hb : 0 < b) :
    (r ^ 2 + 1) * Real.exp (-(2 * b * r ^ 2)) ≤
      (((Real.sqrt (b / 2))⁻¹) ^ 2 + 1) * Real.exp (-b * r ^ 2) := by
  have hsq : Real.mulExpNegMulSq (b / 2) r ^ 2 ≤ (Real.sqrt (b / 2))⁻¹ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Real.abs_mulExpNegMulSq_le (by positivity)) 2
  have hsplit : r ^ 2 * Real.exp (-(2 * b * r ^ 2)) =
      Real.mulExpNegMulSq (b / 2) r ^ 2 * Real.exp (-b * r ^ 2) := by
    unfold Real.mulExpNegMulSq
    cas
  have hmono : Real.exp (-(2 * b * r ^ 2)) ≤ Real.exp (-b * r ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg r])
  rw [add_mul, one_mul, hsplit, add_mul, one_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right hsq (by positivity)) hmono

/-- A unit perturbation of the center changes the squared distance by at most a factor two and
an additive one: `‖x - y‖² / 2 - 1 ≤ ‖x' - y‖²` when `‖x' - x‖ ≤ 1`. -/
private theorem norm_sub_sq_half_sub_one_le (x x' y : ℝ^n) (hx' : ‖x' - x‖ ≤ 1) :
    ‖x - y‖ ^ 2 / 2 - 1 ≤ ‖x' - y‖ ^ 2 := by
  have hd : ‖x - x'‖ ≤ 1 := by rwa [norm_sub_rev]
  nlinarith only [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_norm_sub_add_norm_sub x x' y) 2,
    hd, norm_nonneg (x - x'), sq_nonneg (‖x - x'‖ - ‖x' - y‖)]

/-- A unit perturbation of the center of a positive-time heat kernel is controlled by a slower
Gaussian centered at the original point. -/
theorem heatKernel_local_gaussian_bound
    (x x' y : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hx' : ‖x' - x‖ ≤ 1) :
    fundamentalSolutionHeat (n := n) (x' - y) t ≤
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
        Real.exp (-(‖x - y‖ ^ 2 / (8 * t))) := by
  have h := norm_sub_sq_half_sub_one_le x x' y hx'
  rw [fundamentalSolutionHeat, ite_eq_right (not_le.mpr ht),
    mul_assoc ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)), ← Real.exp_add]
  gcongr
  have : ‖x - y‖ ^ 2 / (8 * t) ≤ (‖x' - y‖ ^ 2 + 1) / (4 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [add_div] at this
  linarith

/-- Data bounded by `|M|`, times a weight at most `P (r ^ 2 + 1)` times a kernel at most
`C exp (-2 b r ^ 2)`, is at most `|M| C P Q exp (-b r ^ 2)`, with the constant `Q` of
`quadratic_mul_exp_le_exp`. -/
private theorem abs_mul_le_gaussian {v M X P C K b r : ℝ} (hb : 0 < b) (hv : |v| ≤ |M|)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hKC : K ≤ C * Real.exp (-(2 * b * r ^ 2))) (hX0 : 0 ≤ X)
    (hX : X ≤ P * (r ^ 2 + 1) * K) :
    |v| * X ≤ |M| * C * P * ((Real.sqrt (b / 2))⁻¹ ^ 2 + 1) * Real.exp (-b * r ^ 2) :=
  calc |v| * X ≤ |M| * (P * (r ^ 2 + 1) * (C * Real.exp (-(2 * b * r ^ 2)))) := by
        gcongr
        exact hX.trans (by gcongr)
    _ = |M| * C * P * ((r ^ 2 + 1) * Real.exp (-(2 * b * r ^ 2))) := by ring
    _ ≤ |M| * C * P * (((Real.sqrt (b / 2))⁻¹ ^ 2 + 1) * Real.exp (-b * r ^ 2)) :=
        mul_le_mul_of_nonneg_left (quadratic_mul_exp_le_exp hb) (by positivity)
    _ = _ := by ring

/-- For bounded `g` and `t > 0`, one integrable function bounds both the gradient kernel and
the Hessian kernel of the heat kernel, weighted by `g y`, for every centre `x'` in `ball x 1`. -/
theorem exists_integrable_bound_heatKernelHessian
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    ∃ bound : ℝ^n → ℝ,
      MeasureTheory.Integrable bound ∧
        (∀ y, 0 ≤ bound y) ∧
          ∀ y x', x' ∈ Metric.ball x 1 →
          ‖(g y) •
              ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x' - y) t) •
                innerSL ℝ (x' - y))‖ ≤ bound y ∧
            ‖(g y) • fundamentalSolutionHeatHessian (n := n) (x' - y) t‖ ≤ bound y := by
  obtain ⟨M, hM⟩ := hg_bdd
  have hb : 0 < 1 / (16 * t) := by positivity
  refine ⟨fun y ↦ |M| * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t))) *
      (2 * (1 / (2 * t)) + 2 * (1 / (2 * t)) ^ 2) * ((Real.sqrt (1 / (16 * t) / 2))⁻¹ ^ 2 + 1) *
      Real.exp (-(1 / (16 * t)) * ‖x - y‖ ^ 2),
    (integrable_exp_neg_mul_sq_norm_sub_left x _ hb).const_mul _, fun y ↦ by positivity,
    fun y x' hx' ↦ ?_⟩
  have hxnorm : ‖x' - x‖ ≤ 1 := by simpa [dist_eq_norm] using (Metric.mem_ball.1 hx').le
  have hdist : ‖x' - y‖ ≤ ‖x - y‖ + 1 := by
    linarith [norm_sub_le_norm_sub_add_norm_sub x' x y]
  have hgy : |g y| ≤ |M| := (hM y).trans (le_abs_self M)
  have hA : 0 ≤ 1 / (2 * t) := by positivity
  have hKC := (heatKernel_local_gaussian_bound x x' y t ht hxnorm).trans_eq (by
    rw [show ‖x - y‖ ^ 2 / (8 * t) = 2 * (1 / (16 * t)) * ‖x - y‖ ^ 2 by ring])
  set Γ := fundamentalSolutionHeat (x' - y) t
  have hΓ : 0 ≤ Γ := (fundamentalSolutionHeat_pos _ t ht).le
  constructor
  · rw [norm_smul, Real.norm_eq_abs]
    refine abs_mul_le_gaussian hb hgy (by positivity) (by positivity) hKC (norm_nonneg _) ?_
    calc _ = 1 / (2 * t) * ‖x' - y‖ * Γ := by
          rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_neg,
            abs_of_nonneg hA, abs_of_nonneg hΓ]
          ring
      _ ≤ _ := by
          gcongr ?_ * Γ
          nlinarith [mul_le_mul_of_nonneg_left hdist hA, mul_nonneg hA (sq_nonneg (‖x - y‖ - 1)),
            mul_nonneg hA (sq_nonneg ‖x - y‖), mul_nonneg hA (norm_nonneg (x - y)),
            mul_nonneg (sq_nonneg (1 / (2 * t))) (sq_nonneg ‖x - y‖)]
  · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    refine abs_mul_le_gaussian hb hgy (by positivity) (by positivity) hKC (norm_nonneg _)
      ((norm_fundamentalSolutionHeatHessian_le _ t ht).trans ?_)
    rw [mul_comm Γ, show 1 / (4 * t ^ 2) = (1 / (2 * t)) ^ 2 by ring]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2)
      (sq_nonneg (1 / (2 * t))), mul_nonneg hA (sq_nonneg ‖x - y‖),
      mul_nonneg (sq_nonneg (1 / (2 * t))) (sq_nonneg (‖x - y‖ - 1))]

/-- A point `q` of the ball of radius `min (t / 2) 1` around `(t, x)` has time coordinate in
`(t / 2, 3 t / 2)` and space coordinate within distance `1` of `x`. -/
private theorem fst_mem_Ioo_and_norm_snd_sub_le_of_mem_ball {t : ℝ} {x : ℝ^n}
    {q : ℝ × ℝ^n} (hq : q ∈ Metric.ball (t, x) (min (t / 2) 1)) :
    q.1 ∈ Set.Ioo (t / 2) (3 * t / 2) ∧ ‖q.2 - x‖ ≤ 1 := by
  have h := Metric.mem_ball.mp hq
  rw [Prod.dist_eq, max_lt_iff] at h
  have htime : dist q.1 t < t / 2 := h.1.trans_le (min_le_left _ _)
  have hspace : dist q.2 x < 1 := h.2.trans_le (min_le_right _ _)
  rw [Real.dist_eq, abs_lt] at htime
  rw [dist_eq_norm] at hspace
  exact ⟨⟨by linarith only [htime.1], by linarith only [htime.2]⟩, hspace.le⟩

/-- For `t / 2 < s < 3 t / 2` and `‖x' - x‖ ≤ 1`, the heat kernel centered at `x'` at time `s`
is controlled by a slower Gaussian centered at `x`:
`Γ(x' - y, s) ≤ (4π(t/2))^(-n/2) e^(1/(6t)) exp(-‖x - y‖²/(12t))`. -/
theorem heatKernel_local_gaussian_bound_timeSpace
    (x x' y : ℝ^n) (t s : ℝ) (hs : s ∈ Set.Ioo (t / 2) (3 * t / 2))
    (hx' : ‖x' - x‖ ≤ 1) :
    fundamentalSolutionHeat (n := n) (x' - y) s ≤
      (4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) * Real.exp (1 / (6 * t)) *
        Real.exp (-(‖x - y‖ ^ 2 / (12 * t))) := by
  obtain ⟨hs₁, hs₂⟩ := hs
  have ht : 0 < t := by linarith only [hs₁, hs₂]
  have hs_pos : 0 < s := by linarith only [ht, hs₁]
  have h := norm_sub_sq_half_sub_one_le x x' y hx'
  rw [fundamentalSolutionHeat, ite_eq_right (not_le.mpr hs_pos),
    mul_assoc ((4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2)), ← Real.exp_add]
  gcongr ?_ * Real.exp ?_
  · exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left hs₁.le (by positivity))
      (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  · have h1 : ‖x' - y‖ ^ 2 / (6 * t) ≤ ‖x' - y‖ ^ 2 / (4 * s) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith only [hs₂])
    have h2 : ‖x - y‖ ^ 2 / (12 * t) ≤ (‖x' - y‖ ^ 2 + 1) / (6 * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [add_div] at h2
    linarith

/-- The coproduct of continuous linear functionals `A` on `ℝ` and `B` on `ℝ^n` has operator
norm at most `‖A‖ + ‖B‖`. -/
private theorem norm_coprod_le (A : ℝ →L[ℝ] ℝ) (B : (ℝ^n) →L[ℝ] ℝ) :
    ‖A.coprod B‖ ≤ ‖A‖ + ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [ContinuousLinearMap.coprod_apply]
  calc
    ‖A v.1 + B v.2‖ ≤ ‖A‖ * ‖v.1‖ + ‖B‖ * ‖v.2‖ :=
      (norm_add_le _ _).trans (add_le_add (A.le_opNorm v.1) (B.le_opNorm v.2))
    _ ≤ ‖A‖ * ‖v‖ + ‖B‖ * ‖v‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg A))
        (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg B))
    _ = (‖A‖ + ‖B‖) * ‖v‖ := by ring

/-- For `0 < t` and `t / 2 < s`, the joint time-space derivative kernel of `Γ` at `(s, z)` has
operator norm at most `(‖z‖²/t² + n/t + ‖z‖/t) Γ(z, s)`. -/
private theorem norm_heatKernel_timeSpace_deriv_le (z : ℝ^n) {t s : ℝ} (ht : 0 < t)
    (hs : t / 2 < s) :
    ‖(ContinuousLinearMap.coprod
        (((‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) *
              fundamentalSolutionHeat (n := n) z s) •
          (1 : ℝ →L[ℝ] ℝ))
        ((-(1 / (2 * s)) * fundamentalSolutionHeat (n := n) z s) • innerSL ℝ z) :
        (ℝ × ℝ^n) →L[ℝ] ℝ)‖ ≤
      (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t + ‖z‖ / t) * fundamentalSolutionHeat (n := n) z s := by
  have hs_pos : 0 < s := by linarith only [ht, hs]
  have hK : 0 ≤ fundamentalSolutionHeat (n := n) z s :=
    (fundamentalSolutionHeat_pos (n := n) z s hs_pos).le
  have hcoef :
      |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| ≤ ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t :=
    (abs_sub _ _).trans (add_le_add
      ((abs_of_nonneg (by positivity)).trans_le
        (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith only [ht, hs])))
      ((abs_of_nonneg (by positivity)).trans_le
        (div_le_div_of_nonneg_left (Nat.cast_nonneg n) ht (by linarith only [hs]))))
  have hhalf : 1 / (2 * s) ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith only [hs])
  refine (norm_coprod_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_one, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_neg, abs_of_nonneg hK, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * s))]
  calc _ ≤ (‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t) * fundamentalSolutionHeat (n := n) z s * 1 +
        1 / t * fundamentalSolutionHeat (n := n) z s * ‖z‖ := by gcongr
    _ = _ := by ring

/-- The polynomial weight of the joint derivative kernel is absorbed by `r² + 1`: for
`0 ≤ t` and `0 ≤ w ≤ r + 1`, `w²/t² + n/t + w/t ≤ (2/t² + n/t + 2/t) (r² + 1)`. -/
private theorem timeSpace_poly_le {t r w : ℝ} (ht : 0 ≤ t) (hw : 0 ≤ w) (hwr : w ≤ r + 1) :
    w ^ 2 / t ^ 2 + (n : ℝ) / t + w / t ≤ (2 / t ^ 2 + (n : ℝ) / t + 2 / t) * (r ^ 2 + 1) := by
  have hsq : w ^ 2 ≤ 2 * (r ^ 2 + 1) := by
    nlinarith only [pow_le_pow_left₀ hw hwr 2, sq_nonneg (r - 1)]
  have hw2 : w ≤ 2 * (r ^ 2 + 1) := by nlinarith only [hwr, sq_nonneg (r - 1), sq_nonneg r]
  calc _ ≤ 2 * (r ^ 2 + 1) / t ^ 2 + (n : ℝ) * (r ^ 2 + 1) / t + 2 * (r ^ 2 + 1) / t := by
        gcongr
        exact le_mul_of_one_le_right (Nat.cast_nonneg n) (by nlinarith only [sq_nonneg r])
    _ = _ := by ring

/-- A locally uniform integrable majorant for the joint time-space derivative of the heat
kernel against bounded data. -/
theorem exists_integrable_bound_heatKernel_timeSpace
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    ∃ bound : ℝ^n → ℝ,
      MeasureTheory.Integrable bound ∧
        ∀ y q,
          q ∈ Metric.ball (t, x) (min (t / 2) 1) →
            ‖(g y) •
                (ContinuousLinearMap.coprod
                  (((‖q.2 - y‖ ^ 2 / (4 * q.1 ^ 2) - (n : ℝ) / (2 * q.1)) *
                        fundamentalSolutionHeat (n := n) (q.2 - y) q.1) •
                    (1 : ℝ →L[ℝ] ℝ))
                  ((-(1 / (2 * q.1)) *
                        fundamentalSolutionHeat (n := n) (q.2 - y) q.1) •
                    innerSL ℝ (q.2 - y)) :
                  (ℝ × ℝ^n) →L[ℝ] ℝ)‖ ≤
              bound y := by
  obtain ⟨M, hM⟩ := hg_bdd
  have hb : 0 < 1 / (24 * t) := by positivity
  refine ⟨fun y ↦ |M| * ((4 * Real.pi * (t / 2)) ^ (-(n : ℝ) / 2) * Real.exp (1 / (6 * t))) *
      (2 / t ^ 2 + (n : ℝ) / t + 2 / t) * ((Real.sqrt (1 / (24 * t) / 2))⁻¹ ^ 2 + 1) *
      Real.exp (-(1 / (24 * t)) * ‖x - y‖ ^ 2),
    (integrable_exp_neg_mul_sq_norm_sub_left x _ hb).const_mul _, fun y q hq ↦ ?_⟩
  obtain ⟨hq_time, hxnorm⟩ := fst_mem_Ioo_and_norm_snd_sub_le_of_mem_ball hq
  have hdist : ‖q.2 - y‖ ≤ ‖x - y‖ + 1 := by
    linarith only [norm_sub_le_norm_sub_add_norm_sub q.2 x y, hxnorm]
  rw [norm_smul, Real.norm_eq_abs]
  exact abs_mul_le_gaussian hb ((hM y).trans (le_abs_self M)) (by positivity) (by positivity)
    ((heatKernel_local_gaussian_bound_timeSpace x q.2 y t q.1 hq_time hxnorm).trans_eq (by
      rw [show ‖x - y‖ ^ 2 / (12 * t) = 2 * (1 / (24 * t)) * ‖x - y‖ ^ 2 by ring]))
    (norm_nonneg _)
    ((norm_heatKernel_timeSpace_deriv_le (n := n) (q.2 - y) ht hq_time.1).trans
      (mul_le_mul_of_nonneg_right (timeSpace_poly_le (n := n) ht.le (norm_nonneg _) hdist)
        (fundamentalSolutionHeat_pos (n := n) (q.2 - y) q.1 (by linarith [hq_time.1])).le))

/-- The spatial heat-kernel gradient against bounded continuous data is Bochner integrable. -/
theorem integrable_heatKernel_gradient
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    MeasureTheory.Integrable (fun y : ℝ^n ↦
      (g y) •
        ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x - y) t) •
          innerSL ℝ (x - y))) := by
  obtain ⟨bound, hbound_int, -, hbound⟩ := exists_integrable_bound_heatKernelHessian g x t ht hg_bdd
  have hgradient_cont : Continuous fun z : (ℝ^n) ↦
      (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) z t) • innerSL ℝ z :=
    continuous_iff_continuousAt.mpr fun z ↦
      (hasFDerivAt_fundamentalSolutionHeat_gradient (n := n) t ht z).continuousAt
  exact hbound_int.mono'
    (hg_cont.smul (hgradient_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun y ↦ (hbound y x (Metric.mem_ball_self one_pos)).1)

/-- One evaluated Hessian slot against bounded continuous data is Bochner integrable. -/
theorem integrable_heatKernelHessian_coord
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (i : Fin n) (ht : 0 < t) (hg_cont : Continuous g)
    (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    MeasureTheory.Integrable (fun y : ℝ^n ↦
      (g y) •
        (((ContinuousLinearMap.apply ℝ ℝ)
            (EuclideanSpace.single i (1 : ℝ))).comp
          (fundamentalSolutionHeatHessian (n := n) (x - y) t))) := by
  obtain ⟨bound, hbound_int, -, hbound⟩ := exists_integrable_bound_heatKernelHessian g x t ht hg_bdd
  refine hbound_int.mono' (hg_cont.smul ((continuous_fundamentalSolutionHeatHessian_apply t
    (EuclideanSpace.single i 1)).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun y ↦ ?_)
  refine (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    fun h ↦ ?_).trans
    (hbound y x (Metric.mem_ball_self one_pos)).2
  calc _ = ‖(g y • fundamentalSolutionHeatHessian (n := n) (x - y) t) h
        (EuclideanSpace.single i 1)‖ := by simp [smul_eq_mul]
    _ ≤ ‖(g y • fundamentalSolutionHeatHessian (n := n) (x - y) t) h‖ *
        ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      rw [PiLp.norm_single, norm_one, mul_one]
      exact ContinuousLinearMap.le_opNorm _ _

end ConvolutionSpace

end HeatEquation
