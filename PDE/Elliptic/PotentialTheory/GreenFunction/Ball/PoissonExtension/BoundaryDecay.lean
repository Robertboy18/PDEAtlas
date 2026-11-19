/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.Definitions
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep
import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.SphereDerivatives.Continuity

/-!
# Boundary decay for the ball Poisson extension

If continuous boundary data vanishes near a point `x₀` of the boundary sphere `∂B(0, r)`, its
Poisson extension tends to zero when `x₀` is approached from inside the ball. This is the ball
version of the estimate of the term `J` in step 3 of Evans's proof of §2.2.4(b), Theorem 14: away
from `x₀` the kernel factor `(r² - ‖x‖²) / ‖x - y‖ⁿ` tends to zero uniformly as `x → x₀`, because
`r² - ‖x‖² → 0` while `‖x - y‖` stays bounded below on the part of the sphere where the datum is
nonzero.

## Main results

* `poissonBallExtension_tendsto_zero_of_eq_zero_nhds`: for `0 < r`, continuous `g` with `g = 0`
  on a neighbourhood of `x₀ ∈ ∂B(0, r)`, and any `ε > 0`, there is `δ > 0` such that
  `|poissonBallExtension r g x| < ε` for all `x ∈ B(0, r)` with `dist x x₀ < δ`.

## Implementation notes

The proof bounds `|g|` on the sphere by compactness, splits the sphere integral according to
whether `‖y - x₀‖` is below or above half the radius of the vanishing neighbourhood, and uses the
normalization of the sphere measure to estimate the remaining integral by a constant multiple of
`r² - ‖x‖²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), step 3 of the proof of Theorem 14, p. 38;
  §2.2.4(c), Theorem 15 (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

/-- Boundary data vanishing near `x₀` contributes negligibly as an interior point tends to `x₀`. -/
theorem poissonBallExtension_tendsto_zero_of_eq_zero_nhds
    {n : ℕ} {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : Continuous g) {x₀ : ℝ^n}
    (hx₀ : x₀ ∈ Metric.sphere (0 : ℝ^n) r) (hg0 : ∀ᶠ y in nhds x₀, g y = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Metric.ball (0 : ℝ^n) r, dist x x₀ < δ →
      |poissonBallExtension (n := n) r g x| < ε := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hzero⟩ := Metric.mem_nhds_iff.1 hg0
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℝ^n) r).exists_bound_of_continuousOn hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hpt (x : ℝ^n) (hxx₀ : dist x x₀ < δ₀ / 2) (y : ℝ^n) (hy : y ∈ Metric.sphere (0 : ℝ^n) r) :
      ‖g y / dist x y ^ n‖ ≤ M / (δ₀ / 2) ^ n := by
    by_cases hclose : dist y x₀ < δ₀
    · rw [show g y = 0 from hzero hclose, zero_div, norm_zero]
      positivity
    have hd : δ₀ / 2 ≤ dist x y := by
      linarith [dist_triangle y x x₀, dist_comm x y, not_lt.1 hclose]
    rw [norm_div, norm_pow, Real.norm_of_nonneg dist_nonneg]
    gcongr
    exact hM y hy
  obtain ⟨C, hC⟩ : ∃ C, ∀ x : ℝ^n, dist x x₀ < δ₀ / 2 →
      |sphereIntegral n (fun y ↦ g y / dist x y ^ n) 0 r| ≤ C := by
    refine ⟨|r| ^ (n - 1) * (M / (δ₀ / 2) ^ n * unitSphereArea n), fun x hxx₀ ↦ ?_⟩
    rw [sphereIntegral, abs_mul, abs_pow, abs_abs]
    gcongr
    exact norm_integral_le_of_norm_le_const (ae_of_all _ fun ω ↦
      hpt x hxx₀ _ (by simpa using smul_unitSphere_mem_sphere hr.le ω))
  have hcont : ContinuousAt
      (fun x : ℝ^n ↦ |r ^ 2 - ‖x‖ ^ 2| / |(n : ℝ) * unitBallVolume n * r| * C) x₀ := by
    fun_prop
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.1 hcont ε hε
  refine ⟨min (δ₀ / 2) δ₁, lt_min (by positivity) hδ₁, fun x hx hxx₀ ↦ ?_⟩
  have h := h₁ (hxx₀.trans_le (min_le_right _ _))
  rw [show ‖x₀‖ = r by simpa using hx₀, sub_self, abs_zero, zero_div, zero_mul, dist_zero_right,
    Real.norm_eq_abs] at h
  calc |poissonBallExtension (n := n) r g x|
      = |r ^ 2 - ‖x‖ ^ 2| / |(n : ℝ) * unitBallVolume n * r| *
          |sphereIntegral n (fun y ↦ g y / dist x y ^ n) 0 r| := by
        rw [poissonBallExtension, abs_mul, abs_div]
    _ ≤ |r ^ 2 - ‖x‖ ^ 2| / |(n : ℝ) * unitBallVolume n * r| * C := by
        gcongr
        exact hC x (hxx₀.trans_le (min_le_left _ _))
    _ ≤ _ := le_abs_self _
    _ < ε := h

end GreenFunction
