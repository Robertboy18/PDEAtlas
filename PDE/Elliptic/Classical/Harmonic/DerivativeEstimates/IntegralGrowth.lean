/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates

/-!
# Liouville's theorem under integral growth

An entire harmonic function on `ℝⁿ` whose integrals over balls `B(x, r)`, `r ≥ 1`, are at most
`C (1 + ‖x‖ + r) r^a` with `a + 1 < n` vanishes identically. Evans's `L¹` interior estimate
bounds `‖Du(x)‖` by `r^{-n-1}` times the ball integral, which tends to zero as `r → ∞`, so `u`
is constant; the growth bound at the origin then forces the constant to be zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 7 (Estimates on derivatives), p. 29, and the
  proof of Theorem 8 (Liouville's Theorem), p. 30.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory PDE.Analysis Set Filter Topology

/-- An entire harmonic function whose ball integrals satisfy
`∫_{B(x,r)} |u| ≤ C (1 + ‖x‖ + r) r^a` for `r ≥ 1`, with `a + 1 < n`, is identically zero. -/
theorem IsHarmonicPDE.eq_zero_of_integral_abs_le
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} (hu : IsHarmonicPDE n u univ) {a C : ℝ}
    (ha : a + 1 < n)
    (hgrowth : ∀ x r, 1 ≤ r → ∫ y in Metric.ball x r, |u y| ≤ C * (1 + ‖x‖ + r) * r ^ a) :
    u = 0 := by
  have hα := unitBallVolume_pos n
  have hC : 0 ≤ C := by
    have h := hgrowth 0 1 le_rfl
    have h0 : 0 ≤ ∫ y in Metric.ball (0 : ℝ^n) 1, |u y| := integral_nonneg fun y ↦ abs_nonneg _
    simp only [norm_zero, Real.one_rpow, mul_one] at h
    nlinarith
  -- Gradient bound for every radius `r ≥ 1`.
  have hderiv (x : ℝ^n) (r : ℝ) (hr : 1 ≤ r) :
      ‖fderiv ℝ u x‖ ≤ ((2 : ℝ) ^ (n + 1) * (n : ℝ) / unitBallVolume n) * C * (2 + ‖x‖) *
        r ^ (a - n) := by
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    calc ‖fderiv ℝ u x‖ ≤ (2 : ℝ) ^ (n + 1) * (n : ℝ) / (unitBallVolume n * r ^ (n + 1)) *
          (C * (1 + ‖x‖ + r) * r ^ a) :=
        (hu.norm_fderiv_le_integral_abs hr0 (fun _ _ ↦ mem_univ _)).trans
          (by gcongr; exact hgrowth x r hr)
      _ ≤ (2 : ℝ) ^ (n + 1) * (n : ℝ) / (unitBallVolume n * r ^ (n + 1)) *
          (C * ((2 + ‖x‖) * r) * r ^ a) := by
        gcongr
        nlinarith [norm_nonneg x]
      _ = _ := by
        rw [Real.rpow_sub hr0, Real.rpow_natCast]
        field_simp
        ring
  have hzero (x : ℝ^n) : fderiv ℝ u x = 0 := by
    have hlim : Tendsto (fun r : ℝ ↦ ((2 : ℝ) ^ (n + 1) * (n : ℝ) / unitBallVolume n) * C *
        (2 + ‖x‖) * r ^ (a - n)) atTop (𝓝 0) := by
      simpa only [mul_zero, neg_sub] using
        (tendsto_rpow_neg_atTop (show 0 < (n : ℝ) - a by linarith)).const_mul
          (((2 : ℝ) ^ (n + 1) * (n : ℝ) / unitBallVolume n) * C * (2 + ‖x‖))
    exact norm_le_zero_iff.1 (ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hderiv x⟩))
  have hconst (x : ℝ^n) : u x = u 0 := is_const_of_fderiv_eq_zero
    ((contDiffOn_univ.mp hu.contDiffOn).differentiable (by norm_num)) hzero x 0
  -- The constant vanishes: its ball integrals grow like `r^n`.
  have hc : u 0 = 0 := by
    by_contra hne
    have hbound (r : ℝ) (hr : 1 ≤ r) : |u 0| ≤ (2 * C / unitBallVolume n) * r ^ (a + 1 - n) := by
      have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
      have hg := hgrowth 0 r hr
      have hint : ∫ y in Metric.ball (0 : ℝ^n) r, |u y| = unitBallVolume n * r ^ n * |u 0| := by
        simp only [hconst]
        rw [setIntegral_const, smul_eq_mul, ← ballVolume_eq_unitBallVolume_mul_pow n r hr0.le]
        rfl
      rw [hint, norm_zero] at hg
      have h2 : C * (1 + 0 + r) * r ^ a ≤ 2 * C * r ^ (a + 1) := by
        rw [Real.rpow_add hr0, Real.rpow_one]
        nlinarith [mul_nonneg hC (Real.rpow_nonneg hr0.le a)]
      have hrn : 0 < r ^ n := by positivity
      rw [Real.rpow_sub hr0, Real.rpow_natCast, div_mul_div_comm, le_div_iff₀ (by positivity)]
      nlinarith
    have hlim : Tendsto (fun r : ℝ ↦ (2 * C / unitBallVolume n) * r ^ (a + 1 - n)) atTop
        (𝓝 0) := by
      simpa only [mul_zero, neg_sub] using
        (tendsto_rpow_neg_atTop (show 0 < (n : ℝ) - (a + 1) by linarith)).const_mul
          (2 * C / unitBallVolume n)
    linarith [ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hbound⟩), abs_pos.mpr hne]
  exact funext fun x ↦ (hconst x).trans hc

end LaplacianEquation
