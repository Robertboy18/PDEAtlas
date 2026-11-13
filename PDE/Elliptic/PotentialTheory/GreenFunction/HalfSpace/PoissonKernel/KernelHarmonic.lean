/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.SecondDerivative
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian

/-!
# Harmonicity of the half-space Poisson kernel

For a pole `y` on the boundary hyperplane, `halfSpacePoissonKernel_harmonic` shows that
`x ↦ K(x, y)` has zero Laplacian on `ℝ^n₊`, and `laplacian_poissonHalfSpaceExtension_eq_zero`
integrates this against measurable data bounded on the boundary to get `Δu = 0` for the Poisson
extension. These are step 1 and the end of step 2 of the proof of Evans's §2.2.4(b), Theorem 14.

## How it works

Evans deduces the harmonicity of `K` from that of `G` and the symmetry `G(x, y) = G(y, x)`. We
compute directly: for a boundary pole the height factor cancels the Laplacian of the
inverse-distance factor, `Δ(xₙ ‖x - y‖⁻ⁿ) = xₙ Δ‖x - y‖⁻ⁿ + 2 ∂ₙ‖x - y‖⁻ⁿ = 0` when `yₙ = 0`.
Integrating the same identity, with the Laplacian moved under the boundary integral, gives
harmonicity of the extension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), steps 1-2 of the proof of Theorem 14 (Poisson's
  formula for half-space), p. 38.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace GreenFunction

open PDE.Analysis MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

open PoissonHalfSpace

/-!
### Pointwise kernel harmonicity
-/

/-- For a boundary pole, the half-space Poisson kernel is harmonic in its
interior variable.

The calculation is the classical cancellation
`Δ(xₙ |x-y|⁻ⁿ) = xₙ Δ|x-y|⁻ⁿ + 2 ∂ₙ|x-y|⁻ⁿ = 0`,
using `yₙ = 0`. -/
theorem halfSpacePoissonKernel_harmonic
    {x y : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n)
    (hy : y ∈ SobolevSpace.HalfSpace.boundary n) :
    laplacian (n := n)
      (fun z ↦ halfSpacePoissonKernel (n := n) z y) x = 0 := by
  let last := PDE.Common.lastIndex (n := n)
  have hxpos : 0 < x last := by simpa [last, SobolevSpace.HalfSpace.upper] using hx
  have hyzero : y last = 0 := by simpa [last, SobolevSpace.HalfSpace.boundary] using hy
  have hxy : x ≠ y := by
    rintro rfl
    linarith
  let f : ℝ^n → ℝ := fun z ↦ (dist z y ^ n)⁻¹
  have hpartial : (∂[last] f) x = (-(n : ℝ) / dist x y ^ (n + 2)) * x last := by
    unfold partialDeriv
    rw [(EuclideanDistance.hasFDerivAt_inv_dist_pow (k := n) hxy).fderiv,
      EuclideanDistance.invDistPowFDerivFormula_apply_eq_of_ne n hxy, innerSL_apply_apply,
      EuclideanSpace.inner_single_left]
    simp [last, hyzero]
  have hkernel : (fun z ↦ halfSpacePoissonKernel (n := n) z y) =
      fun z ↦ 2 / ((n : ℝ) * unitBallVolume n) * (z last * f z) := by
    funext z
    simp only [halfSpacePoissonKernel, f, last]
    field_simp
  rw [hkernel, PDE.laplacian_const_smul, PDE.laplacian_coordinate_mul last f x
    (by simpa [f] using EuclideanDistance.contDiffAt_inv_dist_pow (m := (2 : ℕ∞)) (k := n) hxy),
    EuclideanLaplacian.laplacian_inv_dist_pow hxy, hpartial]
  push_cast
  ring

/-- The half-space Poisson extension has zero Euclidean Laplacian at every
interior point. -/
theorem laplacian_poissonHalfSpaceExtension_eq_zero
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    laplacian (n := n)
      (poissonHalfSpaceExtension (n := n) g) x = 0 := by
  classical
  let last := PDE.Common.lastIndex (n := n)
  let I : ℝ^n → ℝ := fun z ↦
    ∫ y : ℝ^(n - 1), g (halfSpaceEmb (n := n) y) / dist z (halfSpaceEmb (n := n) y) ^ n
  let J : ℝ := ∫ y : ℝ^(n - 1),
    g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ (n + 2)
  have hxpos : 0 < x last := by simpa [last, SobolevSpace.HalfSpace.upper] using hx
  have hI : ∀ᶠ z in nhds x, DifferentiableAt ℝ I z := by
    filter_upwards [Metric.ball_mem_nhds x (half_pos hxpos)] with z hz
    exact (hasFDerivAt_halfSpaceIntegral_div_distance_pow hg hg_bounded
      (halfHeightBall_subset_upper hx hz)).differentiableAt
  have hlapI : laplacian (n := n) I x = (2 * (n : ℝ)) * J := by
    refine (laplacian_halfSpaceIntegral_div_distance_pow hg hg_bounded hx).trans ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by ring)
  have hpartialI : (∂[last] I) x = (-(n : ℝ) * x last) * J := by
    refine (partialDeriv_last_halfSpaceIntegral_div_distance_pow hg hg_bounded hx).trans ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by ring)
  have heq : poissonHalfSpaceExtension (n := n) g =
      fun z ↦ 2 / ((n : ℝ) * unitBallVolume n) * (z last * I z) := by
    funext z
    rw [poissonHalfSpaceExtension_eq_integral (n := n) g hg z]
    simp only [I, last]
    ring
  rw [heq, PDE.laplacian_const_smul, PDE.laplacian_coordinate_mul_of_eventually_differentiableAt
    last I x hI fun i ↦
      differentiableAt_partialDeriv_halfSpaceIntegral_div_distance_pow hg hg_bounded i hx,
    hlapI, hpartialI]
  ring

end GreenFunction
