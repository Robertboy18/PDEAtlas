/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Definitions
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Normalization

/-!
# Uniform bound for the half-space Poisson extension

The nonnegative Poisson kernel has mass one, so the Poisson extension preserves any absolute bound
on the boundary data: `abs_poissonHalfSpaceExtension_le` gives `|u(x)| ≤ M` on `ℝ^n₊` for measurable
`g` with `|g| ≤ M` on the boundary hyperplane. This is the boundedness in part (i) of Evans's
§2.2.4(b), Theorem 14, which he reads off (34) in step 2 of the proof; we use only the defining
integral, with no harmonicity assumption.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), Theorem 14 (Poisson's formula for half-space),
  p. 37, and step 2 of its proof, (34), p. 38.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open MeasureTheory PDE.Analysis

variable {n : ℕ} [Fact (0 < n)]

/-- An absolute bound on measurable boundary data also bounds their Poisson extension
throughout the upper half-space. Only the values on the boundary need to be bounded. -/
theorem abs_poissonHalfSpaceExtension_le {g : ℝ^n → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ ℝ^n₊) : |poissonHalfSpaceExtension g x| ≤ M := by
  let c := (2 * x PDE.Common.lastIndex) / (n * unitBallVolume n)
  let k := fun y : ℝ^(n - 1) ↦ (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹
  have hc : 0 ≤ c :=
    div_nonneg (mul_nonneg (by norm_num) (le_of_lt hx))
      (mul_nonneg (Nat.cast_nonneg n) (unitBallVolume_pos n).le)
  have hk : Integrable k := integrable_inv_distance_pow x hx
  have hk_nonneg (y : ℝ^(n - 1)) : 0 ≤ k y :=
    inv_nonneg.mpr (pow_nonneg dist_nonneg n)
  have hbound : |∫ y, g (halfSpaceEmb (n := n) y) * k y| ≤ M * ∫ y, k y := by
    have hdom : ∀ᵐ y, ‖g (halfSpaceEmb (n := n) y) * k y‖ ≤ M * k y := by
      refine ae_of_all _ fun y ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk_nonneg y)]
      exact mul_le_mul_of_nonneg_right
        (hM _ (halfSpaceEmb_mem_boundary y)) (hk_nonneg y)
    simpa only [Real.norm_eq_abs, integral_const_mul] using
      norm_integral_le_of_norm_le (hk.const_mul M) hdom
  have hunit : c * ∫ y, k y = 1 := by
    simpa only [poissonHalfSpaceExtension_eq_integral _ measurable_const, one_div] using
      poissonHalfSpaceExtension_one_eq_one x hx
  rw [poissonHalfSpaceExtension_eq_integral g hg x]
  simp only [div_eq_mul_inv]
  change |c * ∫ y, g (halfSpaceEmb (n := n) y) * k y| ≤ M
  rw [abs_mul, abs_of_nonneg hc]
  calc
    c * |∫ y, g (halfSpaceEmb (n := n) y) * k y| ≤ c * (M * ∫ y, k y) :=
      mul_le_mul_of_nonneg_left hbound hc
    _ = M := by rw [mul_left_comm, hunit, mul_one]

end GreenFunction
