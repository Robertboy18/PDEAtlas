/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Radial
public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Euclidean.NormSq
import CAS.ExactTactic

/-!
# Radial profiles in `ℝ^n`

A radial profile is a function `x ↦ ψ (1 - |x|² / R²)` on `ℝ^n`, for `ψ : ℝ → ℝ` and `R > 0`. When
`ψ` vanishes on `(-∞, 0]` its support is in the ball of radius `R`. We prove, for every `n`
unless said otherwise:

* `hasCompactSupport_profile`: every multiple of the profile has compact support, when `ψ`
  vanishes on `(-∞, 0]` and `R > 0`;
* `contDiff_profile`: every multiple of the profile is as smooth as `ψ`;
* `partialDeriv_profile`, `sum_sq_partialDeriv_profile`: the gradient
  `∂ᵢ ψ (1 - |x|² / R²) = -2 xᵢ / R² · ψ'` and its square `4 / R² · (|x| / R)² ψ'²`, at every
  point where `ψ` has a derivative; the first is `EuclideanLaplacian.partialDeriv_comp_norm_sq`;
* `integral_profile`, for `n ≥ 1` and `R > 0`:
  `∫ Φ (|x| / R, (1 - |x|² / R²)₊) dx = σ Rⁿ ∫₀¹ s^(n-1) Φ (s, 1 - s²) ds` when `Φ (s, 0) = 0`, by
  `integral_radial_of_support` and the substitution `r = R s`, with `σ = unitSphereArea n`.

So an integral over `ℝ^n` of a function of a profile and of its gradient is one integral over
`[0, 1]`, which `cas` evaluates when `ψ` is a polynomial on `[0, 1]`.

`Euler.Cylinder.radialBump` is a profile of this form on `ℝ³`, with `ψ = Real.smoothTransition`;
its smoothness and its compact support are the cases `A = 1` of `contDiff_profile` and
`hasCompactSupport_profile`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis

variable {n : ℕ} {R : ℝ} {ψ : ℝ → ℝ}

/-- For `R > 0`, `1 - r² / R² ≤ 0` at every `r > R`. -/
theorem one_sub_sq_div_nonpos (hR : 0 < R) {r : ℝ} (hr : R < r) : 1 - r ^ 2 / R ^ 2 ≤ 0 := by
  rw [sub_nonpos, one_le_div (by positivity)]
  gcongr

/-- Every multiple of a radial profile `x ↦ ψ (1 - |x|² / R²)` on `ℝ^n`, `R > 0`, has compact
support when `ψ` vanishes on `(-∞, 0]`. -/
theorem hasCompactSupport_profile (hψ : ∀ P ≤ 0, ψ P = 0) (hR : 0 < R) (A : ℝ) :
    HasCompactSupport fun x : ℝ^n ↦ A * ψ (1 - ‖x‖ ^ 2 / R ^ 2) :=
  (HasCompactSupport.intro (f := fun x : ℝ^n ↦ ψ (1 - ‖x‖ ^ 2 / R ^ 2))
    (isCompact_closedBall 0 R) fun x hx ↦ hψ _ (one_sub_sq_div_nonpos hR
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hx))).mul_left

/-- Every multiple of a radial profile `x ↦ ψ (1 - |x|² / R²)` on `ℝ^n` is as smooth as `ψ`. -/
theorem contDiff_profile {k : WithTop ℕ∞} (hψ : ContDiff ℝ k ψ) (A R : ℝ) :
    ContDiff ℝ k fun x : ℝ^n ↦ A * ψ (1 - ‖x‖ ^ 2 / R ^ 2) :=
  contDiff_const.mul (hψ.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _)))

/-- The gradient of a radial profile on `ℝ^n`:
`∂ᵢ ψ (1 - |x|² / R²) = -2 xᵢ / R² · ψ' (1 - |x|² / R²)`, at every point where `ψ` has the
derivative `ψ'`. -/
theorem partialDeriv_profile {d : ℝ} {x : ℝ^n} (hψ : HasDerivAt ψ d (1 - ‖x‖ ^ 2 / R ^ 2))
    (i : Fin n) : (∂[i] fun y : ℝ^n ↦ ψ (1 - ‖y‖ ^ 2 / R ^ 2)) x = -2 / R ^ 2 * x i * d := by
  have hin : HasDerivAt (fun s : ℝ ↦ ψ (1 - s / R ^ 2)) (-d / R ^ 2) (‖x‖ ^ 2) := by
    refine (hψ.comp (‖x‖ ^ 2) (((hasDerivAt_id _).div_const (R ^ 2)).const_sub 1)).congr_deriv ?_
    cas
  refine (EuclideanLaplacian.partialDeriv_comp_norm_sq i hin.differentiableAt).trans ?_
  rw [hin.deriv]
  cas

/-- The gradient of a radial profile on `ℝ^n` has
`|∇ ψ (1 - |x|² / R²)|² = 4 / R² · (|x| / R)² ψ' (1 - |x|² / R²)²`, at every point where `ψ` has
the derivative `ψ'`. -/
theorem sum_sq_partialDeriv_profile {d : ℝ} {x : ℝ^n}
    (hψ : HasDerivAt ψ d (1 - ‖x‖ ^ 2 / R ^ 2)) :
    ∑ i, ((∂[i] fun y : ℝ^n ↦ ψ (1 - ‖y‖ ^ 2 / R ^ 2)) x) ^ 2 =
      4 / R ^ 2 * (‖x‖ / R) ^ 2 * d ^ 2 :=
  calc ∑ i, ((∂[i] fun y : ℝ^n ↦ ψ (1 - ‖y‖ ^ 2 / R ^ 2)) x) ^ 2
      = ∑ i, 4 / R ^ 4 * d ^ 2 * x i ^ 2 :=
        Finset.sum_congr rfl fun i _ ↦ by rw [partialDeriv_profile hψ]; cas
    _ = 4 / R ^ 2 * (‖x‖ / R) ^ 2 * d ^ 2 := by
        rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
        cas

/-- **Radial integrals of a profile.** In `ℝ^n`, `n ≥ 1`, for `R > 0` and `Φ` with `Φ s 0 = 0`,
`∫ Φ (|x| / R, (1 - |x|² / R²)₊) dx = σ Rⁿ ∫₀¹ s^(n-1) Φ (s, 1 - s²) ds`, with
`σ = unitSphereArea n`. -/
theorem integral_profile (n : ℕ) [Fact (0 < n)] (hR : 0 < R) (Φ : ℝ → ℝ → ℝ)
    (hΦ : ∀ s, Φ s 0 = 0) :
    ∫ x : ℝ^n, Φ (‖x‖ / R) (1 - ‖x‖ ^ 2 / R ^ 2)⁺ =
      unitSphereArea n * R ^ n * ∫ s in (0 : ℝ)..1, s ^ (n - 1) * Φ s (1 - s ^ 2) := by
  have hrad : ∫ x : ℝ^n, Φ (‖x‖ / R) (1 - ‖x‖ ^ 2 / R ^ 2)⁺ =
      unitSphereArea n * ∫ r in (0 : ℝ)..R, r ^ (n - 1) * Φ (r / R) (1 - r ^ 2 / R ^ 2)⁺ :=
    integral_radial_of_support n (f := fun r ↦ Φ (r / R) (1 - r ^ 2 / R ^ 2)⁺) hR.le
      fun r hr ↦ by rw [posPart_eq_zero.mpr (one_sub_sq_div_nonpos hR hr), hΦ]
  have hsub := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (f := fun r ↦ r ^ (n - 1) * Φ (r / R) (1 - r ^ 2 / R ^ 2)⁺) R
  rw [mul_zero, mul_one] at hsub
  rw [hrad, ← hsub, intervalIntegral.integral_congr
    (g := fun s ↦ R ^ (n - 1) * (s ^ (n - 1) * Φ s (1 - s ^ 2))) fun s hs ↦ ?_,
    intervalIntegral.integral_const_mul, smul_eq_mul]
  · rw [← mul_assoc R, mul_pow_sub_one (Fact.out : 0 < n).ne', mul_assoc]
  · rw [uIcc_of_le zero_le_one] at hs
    have h1 : R * s / R = s := mul_div_cancel_left₀ s hR.ne'
    have h2 : (R * s) ^ 2 / R ^ 2 = s ^ 2 := by cas using [hR.ne']
    have h3 : 0 ≤ 1 - s ^ 2 := by cas
    simp only [h1, h2, posPart_eq_self.mpr h3]
    rw [mul_pow, mul_assoc]

end PDE.Analysis
