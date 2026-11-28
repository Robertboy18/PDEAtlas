/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Convolution
public import PDE.Analysis.Calculus.SymbolDecay
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Group.Integral

/-!
# The decay gained from a source of mean zero

How fast does a convolution `K ⋆ g` decay at infinity when the kernel `K` has symbol decay of
order `d` and the source `g` is supported in a ball? In general like `K` itself, at the order
`d`. When `g` has mean zero it decays one order faster: `‖(K ⋆ g) x‖ ≤ C ‖x‖ ^ (d - 1)` far
out. For the Newtonian potential this is the decay of the potential of a compactly supported
source of mean zero (`PoissonEquation.hasSymbolDecay_fundamentalSolutionConvolution`), the step
that Hou, Wang and Yang take after (2.3) for the potential `P_c` of their far field. Only the
first moment is used. A source whose moments vanish up to order `m` gains `m + 1` orders (the
multipole expansion), and that is not proved here.

## Main results

* `HasSymbolDecay.exists_norm_sub_le`: a function with symbol decay of order `d` varies by at
  most `C ‖x‖ ^ (d - 1) ‖y - x‖` between a point `x` with `‖x‖ ≥ 2 R + 2` and a point `y`
  within distance `R` of it.
* `HasSymbolDecay.exists_norm_convolution_le_of_integral_eq_zero`: the mean-zero gain
  `‖(K ⋆ g) x‖ ≤ C ‖x‖ ^ (d - 1)` for `‖x‖ ≥ 2 R + 2`, for every kernel `K` of order `d`, every
  integrable source `g` of mean zero that vanishes outside the ball of radius `R`, every
  bilinear pairing and every measure invariant under translation and negation.
* `zpow_le_two_pow_natAbs_mul`: between half and twice a positive number, an integer power
  `e` changes by at most the factor `2 ^ |e|`.

## How it works

Far from the support of `g` we may subtract the constant `K x` from the kernel, because
`∫ g = 0`. What is left is `K t - K x` for `t` in the ball of radius `R` around `x`. Every point
of that ball has norm between `‖x‖ / 2` and `2 ‖x‖`, so the derivative of `K` is of order
`‖x‖ ^ (d - 1)` there, and the mean value inequality bounds the difference by `R` times that.
Integrating against `|g|` gives the bound.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.1, (2.1)-(2.3) and
  the sentence after (2.3), p. 9. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff Topology Convolution

namespace PDE.Analysis

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Between half and twice a positive number, an integer power changes by at most the factor
`2 ^ |e|`: if `a / 2 ≤ b ≤ 2 a` with `a > 0`, then `b ^ e ≤ 2 ^ |e| a ^ e`. -/
theorem zpow_le_two_pow_natAbs_mul {a b : ℝ} (ha : 0 < a) (hab : a / 2 ≤ b)
    (hba : b ≤ 2 * a) (e : ℤ) : b ^ e ≤ 2 ^ e.natAbs * a ^ e := by
  have hb : 0 < b := lt_of_lt_of_le (half_pos ha) hab
  obtain ⟨n, rfl | rfl⟩ := e.eq_nat_or_neg
  · rw [Int.natAbs_natCast, zpow_natCast, zpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ hb.le hba n
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    calc (b ^ n)⁻¹ ≤ ((a / 2) ^ n)⁻¹ :=
          inv_anti₀ (pow_pos (half_pos ha) n) (pow_le_pow_left₀ (half_pos ha).le hab n)
      _ = 2 ^ n * (a ^ n)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]

namespace HasSymbolDecay

variable {d : ℤ} {f : E → F}

/-- A function with symbol decay of order `d` varies slowly far out: if `‖x‖ ≥ 2 R + 2` and
`‖y - x‖ ≤ R`, then `‖f y - f x‖ ≤ C ‖x‖ ^ (d - 1) ‖y - x‖`, with `C` depending on `f` and `R`
only. This is the mean value inequality on the ball of radius `R` around `x`, where the
derivative is of order `‖x‖ ^ (d - 1)`. -/
theorem exists_norm_sub_le (hf : HasSymbolDecay d f) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x y : E, 2 * R + 2 ≤ ‖x‖ → ‖y - x‖ ≤ R →
      ‖f y - f x‖ ≤ C * ‖x‖ ^ (d - 1) * ‖y - x‖ := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_nonneg
  refine ⟨C 1 * 2 ^ (d - 1).natAbs, mul_nonneg (hC0 1) (by positivity), fun x y hx hy ↦ ?_⟩
  have hR : 0 ≤ R := (norm_nonneg _).trans hy
  have hxpos : 0 < ‖x‖ := by linarith
  -- Every point of the ball has norm between `‖x‖ / 2` and `2 ‖x‖`, and at least one.
  have hfar : ∀ z ∈ Metric.closedBall x R, ‖x‖ / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖x‖ ∧ 1 ≤ ‖z‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
      calc ‖x‖ = ‖z - (z - x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - x‖ := norm_sub_le _ _
    have h2 : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
      calc ‖z‖ = ‖x + (z - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
    exact ⟨by linarith, by linarith, by linarith⟩
  have hbound : ∀ z ∈ Metric.closedBall x R,
      ‖_root_.fderiv ℝ f z‖ ≤ C 1 * 2 ^ (d - 1).natAbs * ‖x‖ ^ (d - 1) := by
    intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := hfar z hz
    have h := hC 1 z hz3
    rw [norm_iteratedFDeriv_one, Nat.cast_one] at h
    rw [mul_assoc]
    exact h.trans (mul_le_mul_of_nonneg_left (zpow_le_two_pow_natAbs_mul hxpos hz1 hz2 _) (hC0 1))
  have hdiff : ∀ z ∈ Metric.closedBall x R, DifferentiableAt ℝ f z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      have h1 := (hfar 0 hz).2.2
      rw [norm_zero] at h1
      linarith
    exact (hf.contDiffAt hz0).differentiableAt (by simp)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall x R)
    (Metric.mem_closedBall_self hR) (by rwa [Metric.mem_closedBall, dist_eq_norm])

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddLeftInvariant]
  [μ.IsNegInvariant] [CompleteSpace G] [CompleteSpace H]

/-- **The mean-zero gain.** Let the kernel `K` have symbol decay of order `d`, and let `g` be
integrable, supported in the ball of radius `R` and of mean zero. Then the convolution `K ⋆ g`
is `O(‖x‖ ^ (d - 1))` at infinity, one order better than `K`: for `‖x‖ ≥ 2 R + 2` we may
replace `K t` by `K t - K x` under the integral, and this difference is small by
`exists_norm_sub_le`. -/
theorem exists_norm_convolution_le_of_integral_eq_zero {K : E → F} (hK : HasSymbolDecay d K)
    (L : F →L[ℝ] G →L[ℝ] H) {g : E → G} {R : ℝ} (hg : Integrable g μ)
    (hsupp : ∀ y, R < ‖y‖ → g y = 0) (hmean : ∫ y, g y ∂μ = 0) :
    ∃ C, ∀ x, 2 * R + 2 ≤ ‖x‖ → ‖(K ⋆[L, μ] g) x‖ ≤ C * ‖x‖ ^ (d - 1) := by
  obtain ⟨C, hC0, hC⟩ := hK.exists_norm_sub_le R
  refine ⟨‖L‖ * (C * |R| * ∫ y, ‖g y‖ ∂μ), fun x hx ↦ ?_⟩
  have hpow : 0 ≤ ‖x‖ ^ (d - 1) := zpow_nonneg (norm_nonneg _) _
  have hshift : Integrable (fun t ↦ g (x - t)) μ := hg.comp_sub_left x
  rw [convolution_def]
  by_cases hint : Integrable (fun t ↦ L (K t) (g (x - t))) μ
  · -- The constant `K x` integrates against `g` to zero.
    have hzero : ∫ t, L (K x) (g (x - t)) ∂μ = 0 := by
      rw [(L (K x)).integral_comp_comm hshift, integral_sub_left_eq_self g μ x, hmean, map_zero]
    have hsub : ∫ t, L (K t) (g (x - t)) ∂μ = ∫ t, L (K t - K x) (g (x - t)) ∂μ := by
      have h := integral_sub hint ((L (K x)).integrable_comp hshift)
      rw [hzero, sub_zero] at h
      rw [← h]
      refine integral_congr_ae (.of_forall fun t ↦ ?_)
      change L (K t) (g (x - t)) - L (K x) (g (x - t)) = L (K t - K x) (g (x - t))
      rw [map_sub]
      rfl
    -- The difference `K t - K x` is small on the support of `g (x - ·)`.
    have hbd : ∀ t, ‖L (K t - K x) (g (x - t))‖ ≤
        ‖L‖ * (C * ‖x‖ ^ (d - 1) * |R|) * ‖g (x - t)‖ := by
      intro t
      by_cases ht : ‖x - t‖ ≤ R
      · have htx : ‖t - x‖ ≤ R := by rwa [norm_sub_rev]
        have hCx : 0 ≤ C * ‖x‖ ^ (d - 1) := mul_nonneg hC0 hpow
        calc ‖L (K t - K x) (g (x - t))‖ ≤ ‖L‖ * ‖K t - K x‖ * ‖g (x - t)‖ := L.le_opNorm₂ _ _
          _ ≤ ‖L‖ * (C * ‖x‖ ^ (d - 1) * |R|) * ‖g (x - t)‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
              (norm_nonneg _)
            exact (hC x t hx htx).trans
              (mul_le_mul_of_nonneg_left (htx.trans (le_abs_self R)) hCx)
      · rw [hsupp _ (not_le.mp ht), map_zero, norm_zero, norm_zero, mul_zero]
    rw [hsub]
    calc ‖∫ t, L (K t - K x) (g (x - t)) ∂μ‖
        ≤ ∫ t, ‖L‖ * (C * ‖x‖ ^ (d - 1) * |R|) * ‖g (x - t)‖ ∂μ :=
          norm_integral_le_of_norm_le (hshift.norm.const_mul _) (.of_forall hbd)
      _ = ‖L‖ * (C * ‖x‖ ^ (d - 1) * |R|) * ∫ y, ‖g y‖ ∂μ := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y ↦ ‖g y‖) μ x]
      _ = ‖L‖ * (C * |R| * ∫ y, ‖g y‖ ∂μ) * ‖x‖ ^ (d - 1) := by ring
  · rw [integral_undef hint, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg L) (mul_nonneg (mul_nonneg hC0 (abs_nonneg R))
      (integral_nonneg fun y ↦ norm_nonneg _))) hpow

end HasSymbolDecay

end PDE.Analysis
