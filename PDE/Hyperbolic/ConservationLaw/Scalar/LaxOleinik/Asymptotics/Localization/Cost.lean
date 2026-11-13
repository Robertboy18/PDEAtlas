/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Support
import CAS.ExactTactic

/-!
# Local quadratic cost and state errors

Pointwise decay puts solution states in a fixed Taylor neighborhood. A separate
velocity estimate handles a competing point whose distance from the drift is `O(s)`
at time `s²`. These constants do not depend on the front displacement.

In the proof of Evans, §3.4.5(b), Theorem 6, at time `t = s²` and with `σ = F'(0)` and
`d = F''(0)` as in (64), these are the bound (69) of the state by the linear profile
`(1/d)((x - σt) - y)/t` at the minimizing footpoint `y = y(x, t)`, and the quadratic expansion
(74) of the cost `tL((x - y)/t)`, which we prove at that footpoint and for every competitor with
`|(x - σt) - y| ≤ (M + 1)t^{1/2}`. Evans obtains (69) from (68); we use the decay
`|u| = O(t^{-1/2})` of Theorem 5 and expand `F'` at `0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(a), Theorem 5, equation (57); §3.4.5(b),
  equation (64), Theorem 6 and steps 1 and 3 of its proof, equations (68)-(69) and (74).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- At sufficiently large squared times, the solution has uniform cubic cost
and quadratic state errors. Pointwise decay places every solution state in the fixed
compact interval where the original flux's Taylor bounds hold. -/
theorem exists_uniform_cost_and_state_error {F g : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) :
    ∃ S : ℝ, 0 < S ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, S ≤ s → ∀ x : ℝ,
      let u := solution F g !₂[s ^ 2, x]
      s ^ 2 * |HopfLax1D.legendreTransform F (deriv F u) -
          (deriv F u - deriv F 0) ^ 2 / (2 * deriv (deriv F) 0)| ≤ C / s ∧
      |u - (deriv F u - deriv F 0) / deriv (deriv F) 0| ≤ C / s ^ 2 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  obtain ⟨K, hK, hcost⟩ :=
    HopfLax1D.exists_abs_legendreTransform_deriv_sub_quadratic_le_cube hF hθ hlower
  obtain ⟨B, hB, hlinear⟩ := exists_abs_sub_linear_le_sq (f := deriv F) hF.deriv'
  let A := √(2 * (∫ y, |g y|) / θ)
  let d := deriv (deriv F) 0
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hd : 0 < d := hθ.trans_le (hlower 0)
  have hC₁ : 0 ≤ K * A ^ 3 := by positivity
  have hC₂ : 0 ≤ B * A ^ 2 / d := by positivity
  refine ⟨max 1 A, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    K * A ^ 3 + B * A ^ 2 / d, add_nonneg hC₁ hC₂, fun s hs x ↦ ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) ((le_max_left (1 : ℝ) A).trans hs)
  have hAs : A ≤ s := (le_max_right 1 A).trans hs
  let u := solution F g !₂[s ^ 2, x]
  have hu : |u| ≤ A / s := by
    simpa only [Real.sqrt_sq hs0.le] using
      abs_solution_le_sqrt_div_sqrt hF2 hθ hlower hzero hg hg1 (sq_pos_of_pos hs0) x
  have hu1 : |u| ≤ 1 := hu.trans ((div_le_one hs0).2 hAs)
  have hu2 : u ^ 2 ≤ (A / s) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) (div_nonneg hA hs0.le)).2 hu
  have hu3 : |u| ^ 3 ≤ (A / s) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) hu 3
  change s ^ 2 * |HopfLax1D.legendreTransform F (deriv F u) -
      (deriv F u - deriv F 0) ^ 2 / (2 * d)| ≤ _ ∧
    |u - (deriv F u - deriv F 0) / d| ≤ _
  constructor
  · have hc := hcost u hu1
    rw [hzero, add_zero] at hc
    calc
      s ^ 2 * |HopfLax1D.legendreTransform F (deriv F u) - (deriv F u - deriv F 0) ^ 2 / (2 * d)|
          ≤ s ^ 2 * (K * |u| ^ 3) := mul_le_mul_of_nonneg_left hc (sq_nonneg s)
      _ ≤ s ^ 2 * (K * (A / s) ^ 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu3 hK) (sq_nonneg s)
      _ = K * A ^ 3 / s := by cas
      _ ≤ (K * A ^ 3 + B * A ^ 2 / d) / s :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right hC₂) hs0.le
  · have heq : u - (deriv F u - deriv F 0) / d =
        -(deriv F u - deriv F 0 - d * u) / d := by cas
    rw [heq, abs_div, abs_neg, abs_of_pos hd]
    calc
      |deriv F u - deriv F 0 - d * u| / d ≤ B * u ^ 2 / d :=
        div_le_div_of_nonneg_right (hlinear u hu1) hd.le
      _ ≤ B * (A / s) ^ 2 / d := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 hB) hd.le
      _ = (B * A ^ 2 / d) / s ^ 2 := by cas
      _ ≤ (K * A ^ 3 + B * A ^ 2 / d) / s ^ 2 :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left hC₁) (sq_nonneg s)

/-- Rewriting the Legendre remainder in spatial coordinates at squared time. -/
theorem scaled_legendre_cost_error_eq (F : ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hd : 0 < deriv (deriv F) 0) (x w : ℝ) :
    |s ^ 2 * HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
        (x - deriv F 0 * s ^ 2 - w) ^ 2 / (2 * deriv (deriv F) 0 * s ^ 2)| =
    s ^ 2 * |HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
        (((x - w) / s ^ 2) - deriv F 0) ^ 2 / (2 * deriv (deriv F) 0)| := by
  have heq : s ^ 2 * HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
      (x - deriv F 0 * s ^ 2 - w) ^ 2 / (2 * deriv (deriv F) 0 * s ^ 2) =
      s ^ 2 * (HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
        (((x - w) / s ^ 2) - deriv F 0) ^ 2 / (2 * deriv (deriv F) 0)) := by cas
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg s)]

/-- Uniform cost comparison for minimizing footpoints and bounded competing
velocities. The constants are chosen before any front displacement; the competing point is
controlled through its velocity. -/
theorem exists_uniform_scaled_cost_error {F g : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {M : ℝ} (hM : 0 ≤ M) :
    ∃ S : ℝ, 0 < S ∧ ∃ E : ℝ, 0 ≤ E ∧ ∀ s : ℝ, S ≤ s →
      (∀ x : ℝ,
        let y := minimizingFootpoint (HopfLax1D.legendreTransform F)
          (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2) x
        |s ^ 2 * HopfLax1D.legendreTransform F ((x - y) / s ^ 2) -
          (x - deriv F 0 * s ^ 2 - y) ^ 2 / (2 * deriv (deriv F) 0 * s ^ 2)| ≤ E / s ∧
        |solution F g !₂[s ^ 2, x] -
          (((x - y) / s ^ 2) - deriv F 0) / deriv (deriv F) 0| ≤ E / s ^ 2) ∧
      (∀ x w : ℝ, |x - deriv F 0 * s ^ 2 - w| ≤ (M + 1) * s →
        |s ^ 2 * HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
          (x - deriv F 0 * s ^ 2 - w) ^ 2 / (2 * deriv (deriv F) 0 * s ^ 2)| ≤ E / s) := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hd : 0 < deriv (deriv F) 0 := hθ.trans_le (hlower 0)
  obtain ⟨S₀, hS₀, A, hA, hactual⟩ := exists_uniform_cost_and_state_error hF hθ hlower hzero hg hg1
  obtain ⟨K, hK, hlocal⟩ :=
    HopfLax1D.exists_abs_legendreTransform_sub_quadratic_le_cube hF hθ hlower
  have hKA : 0 ≤ K * (M + 1) ^ 3 := by positivity
  refine ⟨max S₀ ((M + 1) / θ), hS₀.trans_le (le_max_left _ _),
    A + K * (M + 1) ^ 3, add_nonneg hA hKA, fun s hs ↦ ?_⟩
  have hsA : S₀ ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := hS₀.trans_le hsA
  have hsθ : (M + 1) / θ ≤ s := (le_max_right _ _).trans hs
  constructor
  · intro x
    obtain ⟨hc, hu⟩ := hactual s hsA x
    rw [deriv_solution_eq_footpoint_slope hF2 hθ hlower (sq_pos_of_pos hs0) x] at hc hu
    constructor
    · rw [scaled_legendre_cost_error_eq F hs0 hd]
      exact hc.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hKA) hs0.le)
    · exact hu.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hKA) (sq_nonneg s))
  · intro x w hx
    have hvel : (x - w) / s ^ 2 - deriv F 0 =
        (x - deriv F 0 * s ^ 2 - w) / s ^ 2 := by cas
    have hv : |(x - w) / s ^ 2 - deriv F 0| ≤ (M + 1) / s := by
      rw [hvel, abs_div, abs_of_pos (sq_pos_of_pos hs0)]
      apply (div_le_iff₀ (sq_pos_of_pos hs0)).2
      calc
        |x - deriv F 0 * s ^ 2 - w| ≤ (M + 1) * s := hx
        _ = (M + 1) / s * s ^ 2 := by cas
    have hvθ : |(x - w) / s ^ 2 - deriv F 0| ≤ θ := hv.trans (by
      apply (div_le_iff₀ hs0).2
      have h := (div_le_iff₀ hθ).1 hsθ
      nlinarith only [h])
    have h := hlocal ((x - w) / s ^ 2) hvθ
    rw [hzero, add_zero] at h
    rw [scaled_legendre_cost_error_eq F hs0 hd]
    calc
      s ^ 2 * |HopfLax1D.legendreTransform F ((x - w) / s ^ 2) -
          (((x - w) / s ^ 2) - deriv F 0) ^ 2 / (2 * deriv (deriv F) 0)|
          ≤ s ^ 2 * (K * |(x - w) / s ^ 2 - deriv F 0| ^ 3) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg s)
      _ ≤ s ^ 2 * (K * ((M + 1) / s) ^ 3) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hv 3) hK) (sq_nonneg s)
      _ = K * (M + 1) ^ 3 / s := by cas
      _ ≤ (A + K * (M + 1) ^ 3) / s := div_le_div_of_nonneg_right (le_add_of_nonneg_left hA) hs0.le

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
