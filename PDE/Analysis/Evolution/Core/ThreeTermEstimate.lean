/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.GardingEstimate

/-!
# Three-term data bounds

The Gårding energy estimates bound the squares of the pivot norm `x`, the
energy-space norm `y` and the dual norm `z` of the time derivative in terms of
data norms `d, f ≥ 0`. These three squared bounds give `x + y + z ≤ C (d + f)`. The
constant `C = gardingThreeTermConstant θ γ L M K` depends only on the Gårding
constants, the interval length `L` and the bounds `M`, `K`. The proof takes
square roots.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2, estimate (20).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

/-- The constant `√(A E) + √(F A) + √(2 K² (1 + M² F A))`, where `A = 1 + θ⁻¹`,
`E = e^{2γL}` and `F = θ⁻¹ (1 + 2γL E)`, of the three Gårding estimates. -/
def gardingThreeTermConstant (theta gamma length M K : ℝ) : ℝ :=
  let A := 1 + 1 / theta
  let E := Real.exp (2 * gamma * length)
  let F := (1 / theta) * (1 + 2 * gamma * length * E)
  Real.sqrt (A * E) + Real.sqrt (F * A) + Real.sqrt (2 * K ^ 2 * (1 + M ^ 2 * (F * A)))

/-- Three squared Gårding bounds imply Evans's sum-of-norms estimate
`x + y + z ≤ C (d + f)`, with `C = gardingThreeTermConstant θ γ L M K`
independent of `d` and `f`. -/
theorem three_term_le_of_garding_squared_bounds
    {theta gamma length M K : ℝ} (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (hlength : 0 ≤ length) {x y z d f : ℝ} (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hx : x ^ 2 ≤ (d ^ 2 + (1 / theta) * f ^ 2) * Real.exp (2 * gamma * length))
    (hy : y ^ 2 ≤
      ((1 / theta) * (1 + 2 * gamma * length * Real.exp (2 * gamma * length))) *
        (d ^ 2 + (1 / theta) * f ^ 2))
    (hz : z ^ 2 ≤ 2 * K ^ 2 * (f ^ 2 + M ^ 2 *
      (((1 / theta) * (1 + 2 * gamma * length * Real.exp (2 * gamma * length))) *
        (d ^ 2 + (1 / theta) * f ^ 2)))) :
    x + y + z ≤ gardingThreeTermConstant theta gamma length M K * (d + f) := by
  let A := 1 + 1 / theta
  let E := Real.exp (2 * gamma * length)
  let F := (1 / theta) * (1 + 2 * gamma * length * E)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hR : 0 ≤ d + f := add_nonneg hd hf
  have hdR : d ^ 2 ≤ (d + f) ^ 2 := by nlinarith
  have hfR : f ^ 2 ≤ (d + f) ^ 2 := by nlinarith
  have hD : d ^ 2 + (1 / theta) * f ^ 2 ≤ A * (d + f) ^ 2 := by
    have hscale := mul_le_mul_of_nonneg_left hfR (show 0 ≤ 1 / theta by positivity)
    dsimp only [A]
    nlinarith
  have hxs : x ^ 2 ≤ (A * E) * (d + f) ^ 2 := by
    exact hx.trans (by dsimp only [E]; nlinarith [mul_le_mul_of_nonneg_right hD hE])
  have hys : y ^ 2 ≤ (F * A) * (d + f) ^ 2 := by
    exact hy.trans (by dsimp only [F, E] at *; nlinarith [mul_le_mul_of_nonneg_left hD hF])
  have hzs : z ^ 2 ≤ (2 * K ^ 2 * (1 + M ^ 2 * (F * A))) * (d + f) ^ 2 := by
    apply hz.trans
    change 2 * K ^ 2 * (f ^ 2 + M ^ 2 * (F * (d ^ 2 + 1 / theta * f ^ 2))) ≤ _
    have hscaled := mul_le_mul_of_nonneg_left hD hF
    have hscaledM := mul_le_mul_of_nonneg_left hscaled (sq_nonneg M)
    have hsum := add_le_add hfR hscaledM
    have hscaledK := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * K ^ 2 by positivity)
    nlinarith
  have bound {r c : ℝ} (hc : 0 ≤ c) (hr : r ^ 2 ≤ c * (d + f) ^ 2) :
      r ≤ Real.sqrt c * (d + f) := by
    calc
      r ≤ Real.sqrt (c * (d + f) ^ 2) := Real.le_sqrt_of_sq_le hr
      _ = Real.sqrt c * (d + f) := by rw [Real.sqrt_mul hc, Real.sqrt_sq hR]
  have hsum := add_le_add (add_le_add (bound (mul_nonneg hA hE) hxs)
    (bound (mul_nonneg hF hA) hys)) (bound (by positivity) hzs)
  exact hsum.trans_eq (by dsimp only [gardingThreeTermConstant, A, E, F]; ring)

end PDE.Analysis.Evolution
