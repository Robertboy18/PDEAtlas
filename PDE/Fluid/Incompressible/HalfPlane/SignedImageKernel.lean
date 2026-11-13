/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.OriginTaylor
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarKernelDerivatives
import PDE.FDeriv.PartialDeriv.Energy

/-!
# Signed image sums of planar kernels

Let `F` be a density on the plane with the parities `F(R₀ y) = ε₀ F(y)` and `F(R₁ y) = ε₁ F(y)`
under the coordinate reflections `R₀ y = (-y₀, y₁)` and `R₁ y = (y₀, -y₁)`, `εᵢ = ±1`. Folding a
convolution `∫ k(x - y) F(y) dy` onto the open quadrant groups the four images of `y`:

`∫ k(x - y) F(y) dy = ∫_{ℝ²₊₊} B(x, y) F(y) dy`,
`B(x, y) = k(x - y) + ε₀ k(x - R₀ y) + ε₁ k(x - R₁ y) + ε₀ ε₁ k(x + y)`

(`signedImageKernel`, `integral_mul_eq_setIntegral_quadrant_signedImageKernel`). For
`ε₀ = ε₁ = -1` this is the odd-odd symmetrized kernel of Chen and Hou, Part I, (3.2).

If `k` has the parities `k(Rᵢ z) = σᵢ k(z)`, then `B(0, y) = (σ₀ + ε₀)(σ₁ + ε₁) k(y)` and
`B(x, 0) = (1 + ε₀)(1 + ε₁) k(x)`. When the first product vanishes and `|Dk(z)| ≤ A / |z|^q`, we
have the far-field bound `|B(x, y)| ≤ 4 A 2^q |x| / |y|^q` for `2|x| ≤ |y|`
(`abs_signedImageKernel_le_of_far`); when the second vanishes, the near-field bound
`|B(x, y)| ≤ 4 A 2^q |y| / |x|^q` for `2|y| ≤ |x|` (`abs_signedImageKernel_le_of_near`). These are
the symmetrization estimates of Chen and Hou, Part I, proofs of Lemma 6.5 and of Proposition 6.6,
written for all four images at once. Integrated, a density supported in `|y| ≥ 2|x|` gives
`|∫ k(x - y) F(y) dy| ≤ A 2^q |x| ∫ |F(y)| / |y|^q dy`, and a density supported in `|y| ≤ |x|/2`
gives `|∫ k(x - y) F(y) dy| ≤ A 2^q |x|^(-q) ∫ |y| |F(y)| dy`.

The gradient kernels `gⱼ` (`σ = (-1, 1)` for `j = 0`, `(1, -1)` for `j = 1`, `|Dgⱼ(z)| ≤ π⁻¹|z|⁻²`)
and the Hessian kernels `kᵢⱼ` (`σ = (1, 1)` for `i = j`, `(-1, -1)` otherwise,
`|Dkᵢⱼ(z)| ≤ 2|z|⁻³`) satisfy the hypotheses.

## Main definitions

* `signedImageKernel`: the signed image sum
  `k(x - y) + ε₀ k(x - R₀ y) + ε₁ k(x - R₁ y) + ε₀ ε₁ k(x + y)`.

## Main results

* `integral_mul_eq_setIntegral_quadrant_signedImageKernel`: the fold
  `∫ k(x - y) F(y) dy = ∫_{ℝ²₊₊} B(x, y) F(y) dy`; on an invariant set it is
  `setIntegral_mul_eq_setIntegral_quadrant_signedImageKernel`.
* `signedImageKernel_zero_left`: `B(0, y) = (σ₀ + ε₀)(σ₁ + ε₁) k(y)` for a kernel with the
  parities `σ₀`, `σ₁`; `signedImageKernel_zero_right` is `B(x, 0) = (1 + ε₀)(1 + ε₁) k(x)`.
* `abs_signedImageKernel_le_of_far`: if `B(0, ·)` vanishes, `|B(x, y)| ≤ 4 A 2^q |x| / |y|^q` for
  `y ≠ 0` and `2|x| ≤ |y|`.
* `abs_signedImageKernel_le_of_near`: if `(1 + ε₀)(1 + ε₁) = 0`,
  `|B(x, y)| ≤ 4 A 2^q |y| / |x|^q` for `x ≠ 0` and `2|y| ≤ |x|`.
* `abs_integral_mul_le_of_far`: for `F` vanishing off `{2|x| ≤ |y|}`,
  `|∫ k(x - y) F(y) dy| ≤ A 2^q |x| ∫ |F(y)| / |y|^q dy`.
* `abs_integral_mul_le_of_near`: for `F` vanishing off `{2|y| ≤ |x|}`,
  `|∫ k(x - y) F(y) dy| ≤ A 2^q |x|^(-q) ∫ |y| |F(y)| dy`.
* `norm_fderiv_gradientKernel_le`: `|Dgⱼ(z)| ≤ π⁻¹ |z|⁻²` away from the pole, and
  `|Dkᵢⱼ(z)| ≤ 2 |z|⁻³` (`norm_fderiv_hessianKernel_le`).

## How it works

In the far case `B(0, y) = 0`, so `B(x, y)` is a signed sum of the four increments
`k(x - y') - k(-y')` over the images `y'` of `y`, all of norm `|y|`. The ball of radius `|x|` around
`-y'` stays outside `B(0, |y|/2)`, so the mean value theorem bounds each increment by
`A 2^q |x| / |y|^q` (`abs_sub_le_of_two_mul_norm_le`); the near case uses `B(x, 0) = 0` in the same
way. For the integrated bounds we fold the integral onto the quadrant, where the pointwise bound
costs the factor 4. Since `|F|` and the support conditions are invariant under the reflections, the
quadrant integral of the bound is a quarter of the integral over the plane, which removes that
factor (`abs_setIntegral_mul_le_of_far`, `abs_setIntegral_mul_le_of_near`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.2), p. 27, for the
  symmetrized kernel, and Section 6.2, the proofs of Lemma 6.5, pp. 98-99, and of Proposition 6.6,
  pp. 99-100, for the symmetrization estimates.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open GreenFunction PotentialTheory.Planar

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

/-- The signed sum of a kernel over the four images of `y` under the coordinate reflections,
`k(x - y) + ε₀ k(x - R₀ y) + ε₁ k(x - R₁ y) + ε₀ ε₁ k(x + y)`. -/
def signedImageKernel (k : ℝ^2 → ℝ) (ε₀ ε₁ : ℝ) (x y : ℝ^2) : ℝ :=
  k (x - y) + ε₀ * k (x - 𝐑 0 y) + ε₁ * k (x - 𝐑 1 y) + ε₀ * ε₁ * k (x + y)

/-- The odd-odd symmetrized kernel is the signed image sum with `ε₀ = ε₁ = -1`. -/
theorem symmetrizedKernel_eq_signedImageKernel (k : ℝ^2 → ℝ) (x y : ℝ^2) :
    symmetrizedKernel k x y = signedImageKernel k (-1) (-1) x y := by
  simp only [symmetrizedKernel, signedImageKernel]
  ring

/-- In the plane `-R₀ y = R₁ y`. -/
private theorem neg_coordinateReflection_zero (y : ℝ^2) : -𝐑 0 y = 𝐑 1 y := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne]

/-- In the plane `-R₁ y = R₀ y`. -/
private theorem neg_coordinateReflection_one (y : ℝ^2) : -𝐑 1 y = 𝐑 0 y := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne]

/-- The reflection `R₀` fixes the origin. -/
private theorem coordinateReflection_zero_zero : 𝐑 0 (0 : ℝ^2) = 0 := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same]

/-- The reflection `R₁` fixes the origin. -/
private theorem coordinateReflection_one_zero : 𝐑 1 (0 : ℝ^2) = 0 := by
  ext k
  fin_cases k <;> simp [PDE.Common.coordinateReflection_apply_same]

/-! ### The fold -/

section Fold

variable {k F : ℝ^2 → ℝ} {ε₀ ε₁ : ℝ}

/-- The parity of a density under `y ↦ -y`. -/
theorem apply_neg_of_coordinateReflection (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y)
    (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y) (y : ℝ^2) : F (-y) = ε₀ * ε₁ * F y := by
  rw [← coordinateReflection_zero_one, hF₀, hF₁]
  ring

/-- **The fold on an invariant set.** For a density with the parities `ε₀`, `ε₁` and a set
invariant under both reflections, `∫_S k(x - y) F(y) dy = ∫_{S ∩ ℝ²₊₊} B(x, y) F(y) dy`. -/
theorem setIntegral_mul_eq_setIntegral_quadrant_signedImageKernel
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y)
    {S : Set (ℝ^2)} (hS : MeasurableSet S) (hS₀ : ∀ y, 𝐑 0 y ∈ S ↔ y ∈ S)
    (hS₁ : ∀ y, 𝐑 1 y ∈ S ↔ y ∈ S) (x : ℝ^2)
    (hint : IntegrableOn (fun y ↦ k (x - y) * F y) S) :
    ∫ y in S, k (x - y) * F y =
      ∫ y in S ∩ quadrant, signedImageKernel k ε₀ ε₁ x y * F y := by
  rw [setIntegral_eq_setIntegral_inter_quadrant hS hS₀ hS₁ hint]
  refine setIntegral_congr_fun (hS.inter measurableSet_quadrant) fun y _ ↦ ?_
  simp only [signedImageKernel, hF₀, hF₁, apply_neg_of_coordinateReflection hF₀ hF₁, sub_neg_eq_add]
  ring

/-- **The fold on the plane.** `∫ k(x - y) F(y) dy = ∫_{ℝ²₊₊} B(x, y) F(y) dy`. -/
theorem integral_mul_eq_setIntegral_quadrant_signedImageKernel
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y) (x : ℝ^2)
    (hint : Integrable fun y ↦ k (x - y) * F y) :
    ∫ y, k (x - y) * F y = ∫ y in quadrant, signedImageKernel k ε₀ ε₁ x y * F y := by
  have h := setIntegral_mul_eq_setIntegral_quadrant_signedImageKernel hF₀ hF₁
    MeasurableSet.univ (by simp) (by simp) x hint.integrableOn
  rwa [setIntegral_univ, univ_inter] at h

end Fold

/-! ### Values at the origin -/

/-- At `x = 0`, `B(0, y) = (σ₀ + ε₀)(σ₁ + ε₁) k(y)` for a kernel with the parities `σ₀`, `σ₁`. -/
theorem signedImageKernel_zero_left {k : ℝ^2 → ℝ} {σ₀ σ₁ : ℝ}
    (hk₀ : ∀ z, k (𝐑 0 z) = σ₀ * k z) (hk₁ : ∀ z, k (𝐑 1 z) = σ₁ * k z) (ε₀ ε₁ : ℝ)
    (y : ℝ^2) : signedImageKernel k ε₀ ε₁ 0 y = (σ₀ + ε₀) * (σ₁ + ε₁) * k y := by
  simp only [signedImageKernel, zero_sub, zero_add, neg_coordinateReflection_zero,
    neg_coordinateReflection_one]
  rw [← coordinateReflection_zero_one]
  simp only [hk₀, hk₁]
  ring

/-- At `y = 0`, `B(x, 0) = (1 + ε₀)(1 + ε₁) k(x)`. -/
theorem signedImageKernel_zero_right (k : ℝ^2 → ℝ) (ε₀ ε₁ : ℝ) (x : ℝ^2) :
    signedImageKernel k ε₀ ε₁ x 0 = (1 + ε₀) * (1 + ε₁) * k x := by
  simp only [signedImageKernel, sub_zero, add_zero, coordinateReflection_zero_zero,
    coordinateReflection_one_zero]
  ring

/-! ### Mean value bounds -/

section MeanValue

variable {k : ℝ^2 → ℝ} {A : ℝ} {q : ℕ}

/-- The increment of a kernel with `|Dk(z)| ≤ A / |z|^q` over a step `h` with `2|h| ≤ |u|`:
`|k(u + h) - k(u)| ≤ A 2^q |h| / |u|^q`. -/
theorem abs_sub_le_of_two_mul_norm_le (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q) {u h : ℝ^2}
    (hu : u ≠ 0) (hh : 2 * ‖h‖ ≤ ‖u‖) :
    |k (u + h) - k u| ≤ A * 2 ^ q * ‖h‖ / ‖u‖ ^ q := by
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hA : 0 ≤ A := (div_nonneg_iff.mp ((norm_nonneg _).trans (hDk u hu))).elim And.left
    fun h ↦ absurd h.2 (not_le.mpr (pow_pos hu' q))
  set s : Set (ℝ^2) := Metric.closedBall u ‖h‖
  have hmem : ∀ z ∈ s, ‖u‖ / 2 ≤ ‖z‖ := by
    intro z hz
    have hz' : ‖z - u‖ ≤ ‖h‖ := by simpa [s, dist_eq_norm] using hz
    have := norm_sub_norm_le u z
    rw [norm_sub_rev] at this
    linarith
  have hne : ∀ z ∈ s, z ≠ 0 := fun z hz ↦ by
    have := hmem z hz
    intro h0; rw [h0, norm_zero] at this; linarith
  have hbound : ∀ z ∈ s, ‖fderiv ℝ k z‖ ≤ A * 2 ^ q / ‖u‖ ^ q := by
    intro z hz
    refine (hDk z (hne z hz)).trans ?_
    have hz2 := hmem z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (hne z hz)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (‖u‖ / 2) ^ q ≤ ‖z‖ ^ q := pow_le_pow_left₀ (by positivity) hz2 q
    calc A * ‖u‖ ^ q = A * (2 ^ q * (‖u‖ / 2) ^ q) := by rw [div_pow]; field_simp
      _ ≤ A * (2 ^ q * ‖z‖ ^ q) := by gcongr
      _ = A * 2 ^ q * ‖z‖ ^ q := by ring
  have hmv := (convex_closedBall u ‖h‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ hk z (hne z hz)) hbound (Metric.mem_closedBall_self (norm_nonneg h))
    (by simp [s, dist_eq_norm] : u + h ∈ s)
  rw [Real.norm_eq_abs, add_sub_cancel_left] at hmv
  calc |k (u + h) - k u| ≤ A * 2 ^ q / ‖u‖ ^ q * ‖h‖ := hmv
    _ = A * 2 ^ q * ‖h‖ / ‖u‖ ^ q := by ring

/-- `|a + b + c + d| ≤ |a| + |b| + |c| + |d|`. -/
private theorem abs_add_add_add_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- For a sign `|ε| = 1`, `|ε a| = |a|`. -/
private theorem abs_mul_of_abs_eq_one {ε a : ℝ} (hε : |ε| = 1) : |ε * a| = |a| := by
  rw [abs_mul, hε, one_mul]

/-- **The far-field bound.** If the kernel parities make `B(0, y)` vanish, then for `y ≠ 0` and
`2|x| ≤ |y|`, `|B(x, y)| ≤ 4 A 2^q |x| / |y|^q`. -/
theorem abs_signedImageKernel_le_of_far (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q) {σ₀ σ₁ ε₀ ε₁ : ℝ}
    (hk₀ : ∀ z, k (𝐑 0 z) = σ₀ * k z) (hk₁ : ∀ z, k (𝐑 1 z) = σ₁ * k z)
    (hvan : (σ₀ + ε₀) * (σ₁ + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1) {x y : ℝ^2}
    (hy : y ≠ 0) (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |signedImageKernel k ε₀ ε₁ x y| ≤ 4 * A * 2 ^ q * ‖x‖ / ‖y‖ ^ q := by
  have h0 := signedImageKernel_zero_left hk₀ hk₁ ε₀ ε₁ y
  rw [hvan, zero_mul] at h0
  have hstep (v : ℝ^2) (hv : ‖v‖ = ‖y‖) :
      |k (x - v) - k (0 - v)| ≤ A * 2 ^ q * ‖x‖ / ‖y‖ ^ q := by
    have hv0 : -v ≠ 0 := by
      rw [neg_ne_zero]; intro h; rw [h, norm_zero] at hv; exact hy (norm_eq_zero.mp hv.symm)
    have h := abs_sub_le_of_two_mul_norm_le hk hDk hv0 (h := x)
      (by rw [norm_neg, hv]; exact hxy)
    rw [norm_neg, hv] at h
    rwa [show x - v = -v + x by abel, zero_sub]
  have h1 := hstep y rfl
  have h2 := hstep (𝐑 0 y) (PDE.Common.norm_coordinateReflection 0 y)
  have h3 := hstep (𝐑 1 y) (PDE.Common.norm_coordinateReflection 1 y)
  have h4 := hstep (-y) (norm_neg y)
  have heq : signedImageKernel k ε₀ ε₁ x y = signedImageKernel k ε₀ ε₁ x y -
      signedImageKernel k ε₀ ε₁ 0 y := by rw [h0, sub_zero]
  rw [heq]
  have hdiff : signedImageKernel k ε₀ ε₁ x y - signedImageKernel k ε₀ ε₁ 0 y =
      (k (x - y) - k (0 - y)) + ε₀ * (k (x - 𝐑 0 y) - k (0 - 𝐑 0 y)) +
        ε₁ * (k (x - 𝐑 1 y) - k (0 - 𝐑 1 y)) +
        ε₀ * ε₁ * (k (x - -y) - k (0 - -y)) := by
    simp only [signedImageKernel, sub_neg_eq_add]
    ring
  rw [hdiff]
  have hε : |ε₀ * ε₁| = 1 := by rw [abs_mul, hε₀, hε₁, one_mul]
  calc _ ≤ |k (x - y) - k (0 - y)| + |ε₀ * (k (x - 𝐑 0 y) - k (0 - 𝐑 0 y))| +
        |ε₁ * (k (x - 𝐑 1 y) - k (0 - 𝐑 1 y))| +
        |ε₀ * ε₁ * (k (x - -y) - k (0 - -y))| := abs_add_add_add_le _ _ _ _
    _ ≤ _ := by
      rw [abs_mul_of_abs_eq_one hε₀, abs_mul_of_abs_eq_one hε₁, abs_mul_of_abs_eq_one hε,
        show 4 * A * 2 ^ q * ‖x‖ / ‖y‖ ^ q = 4 * (A * 2 ^ q * ‖x‖ / ‖y‖ ^ q) by ring]
      linarith

/-- **The near-field bound.** If `(1 + ε₀)(1 + ε₁) = 0`, then for `x ≠ 0` and `2|y| ≤ |x|`,
`|B(x, y)| ≤ 4 A 2^q |y| / |x|^q`. -/
theorem abs_signedImageKernel_le_of_near (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q) {ε₀ ε₁ : ℝ}
    (hvan : (1 + ε₀) * (1 + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1) {x y : ℝ^2}
    (hx : x ≠ 0) (hxy : 2 * ‖y‖ ≤ ‖x‖) :
    |signedImageKernel k ε₀ ε₁ x y| ≤ 4 * A * 2 ^ q * ‖y‖ / ‖x‖ ^ q := by
  have h0 := signedImageKernel_zero_right k ε₀ ε₁ x
  rw [hvan, zero_mul] at h0
  have hstep (v : ℝ^2) (hv : ‖v‖ = ‖y‖) :
      |k (x - v) - k (x - 0)| ≤ A * 2 ^ q * ‖y‖ / ‖x‖ ^ q := by
    have h := abs_sub_le_of_two_mul_norm_le hk hDk hx (h := -v)
      (by rw [norm_neg, hv]; exact hxy)
    rw [norm_neg, hv] at h
    rw [sub_zero, sub_eq_add_neg]
    exact h
  have h1 := hstep y rfl
  have h2 := hstep (𝐑 0 y) (PDE.Common.norm_coordinateReflection 0 y)
  have h3 := hstep (𝐑 1 y) (PDE.Common.norm_coordinateReflection 1 y)
  have h4 := hstep (-y) (norm_neg y)
  have hdiff : signedImageKernel k ε₀ ε₁ x y - signedImageKernel k ε₀ ε₁ x 0 =
      (k (x - y) - k (x - 0)) + ε₀ * (k (x - 𝐑 0 y) - k (x - 0)) +
        ε₁ * (k (x - 𝐑 1 y) - k (x - 0)) + ε₀ * ε₁ * (k (x - -y) - k (x - 0)) := by
    simp only [signedImageKernel, sub_neg_eq_add, coordinateReflection_zero_zero,
      coordinateReflection_one_zero, sub_zero, add_zero]
    ring
  have heq : signedImageKernel k ε₀ ε₁ x y = signedImageKernel k ε₀ ε₁ x y -
      signedImageKernel k ε₀ ε₁ x 0 := by rw [h0, sub_zero]
  rw [heq, hdiff]
  have hε : |ε₀ * ε₁| = 1 := by rw [abs_mul, hε₀, hε₁, one_mul]
  calc _ ≤ |k (x - y) - k (x - 0)| + |ε₀ * (k (x - 𝐑 0 y) - k (x - 0))| +
        |ε₁ * (k (x - 𝐑 1 y) - k (x - 0))| + |ε₀ * ε₁ * (k (x - -y) - k (x - 0))| :=
        abs_add_add_add_le _ _ _ _
    _ ≤ _ := by
      rw [abs_mul_of_abs_eq_one hε₀, abs_mul_of_abs_eq_one hε₁, abs_mul_of_abs_eq_one hε,
        show 4 * A * 2 ^ q * ‖y‖ / ‖x‖ ^ q = 4 * (A * 2 ^ q * ‖y‖ / ‖x‖ ^ q) by ring]
      linarith

end MeanValue

/-! ### Integrated bounds -/

section Integrated

variable {k F : ℝ^2 → ℝ} {A : ℝ} {q : ℕ} {ε₀ ε₁ : ℝ}

/-- If `F ∘ R₀ = ε₀ F` and `F ∘ R₁ = ε₁ F` with signs `|ε₀| = |ε₁| = 1`, then `|F|` is invariant
under both reflections. -/
private theorem abs_apply_coordinateReflection (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y)
    (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1) :
    (∀ y, |F (𝐑 0 y)| = |F y|) ∧ ∀ y, |F (𝐑 1 y)| = |F y| :=
  ⟨fun y ↦ by rw [hF₀, abs_mul_of_abs_eq_one hε₀], fun y ↦ by
    rw [hF₁, abs_mul_of_abs_eq_one hε₁]⟩

/-- An even-even integrand on an invariant set: `∫_S h = 4 ∫_{S ∩ ℝ²₊₊} h`. -/
private theorem setIntegral_eq_four_mul_inter_quadrant {h : ℝ^2 → ℝ} {S : Set (ℝ^2)}
    (hS : MeasurableSet S) (hS₀ : ∀ y, 𝐑 0 y ∈ S ↔ y ∈ S) (hS₁ : ∀ y, 𝐑 1 y ∈ S ↔ y ∈ S)
    (hh : IntegrableOn h S) (h₀ : ∀ y, h (𝐑 0 y) = h y) (h₁ : ∀ y, h (𝐑 1 y) = h y) :
    ∫ y in S, h y = 4 * ∫ y in S ∩ quadrant, h y := by
  rw [setIntegral_eq_setIntegral_inter_quadrant hS hS₀ hS₁ hh, ← integral_const_mul]
  refine setIntegral_congr_fun (hS.inter measurableSet_quadrant) fun y _ ↦ ?_
  have hneg : h (-y) = h y := by rw [← coordinateReflection_zero_one, h₀, h₁]
  simp only [h₀, h₁, hneg]
  ring

/-- The set `{a ≤ |y|}` is invariant under the reflections `R₀` and `R₁`. -/
private theorem invariant_norm_le (a : ℝ) :
    (∀ y : ℝ^2, 𝐑 0 y ∈ {y : ℝ^2 | a ≤ ‖y‖} ↔ y ∈ {y : ℝ^2 | a ≤ ‖y‖}) ∧
      ∀ y : ℝ^2, 𝐑 1 y ∈ {y : ℝ^2 | a ≤ ‖y‖} ↔ y ∈ {y : ℝ^2 | a ≤ ‖y‖} :=
  ⟨fun y ↦ by simp [PDE.Common.norm_coordinateReflection],
    fun y ↦ by simp [PDE.Common.norm_coordinateReflection]⟩

/-- The set `{|y| ≤ a}` is invariant under the reflections `R₀` and `R₁`. -/
private theorem invariant_le_norm (a : ℝ) :
    (∀ y : ℝ^2, 𝐑 0 y ∈ {y : ℝ^2 | ‖y‖ ≤ a} ↔ y ∈ {y : ℝ^2 | ‖y‖ ≤ a}) ∧
      ∀ y : ℝ^2, 𝐑 1 y ∈ {y : ℝ^2 | ‖y‖ ≤ a} ↔ y ∈ {y : ℝ^2 | ‖y‖ ≤ a} :=
  ⟨fun y ↦ by simp [PDE.Common.norm_coordinateReflection],
    fun y ↦ by simp [PDE.Common.norm_coordinateReflection]⟩

/-- **The integrated far-field bound on an invariant set.** If the kernel parities make
`B(0, ·)` vanish and every point of `S` satisfies `2|x| ≤ |y|`, then
`|∫_S k(x - y) F(y) dy| ≤ A 2^q |x| ∫_S |F(y)| / |y|^q dy`. -/
theorem abs_setIntegral_mul_le_of_far (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q) {σ₀ σ₁ : ℝ}
    (hk₀ : ∀ z, k (𝐑 0 z) = σ₀ * k z) (hk₁ : ∀ z, k (𝐑 1 z) = σ₁ * k z)
    (hvan : (σ₀ + ε₀) * (σ₁ + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1)
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y)
    {S : Set (ℝ^2)} (hS : MeasurableSet S) (hS₀ : ∀ y, 𝐑 0 y ∈ S ↔ y ∈ S)
    (hS₁ : ∀ y, 𝐑 1 y ∈ S ↔ y ∈ S) (hF : IntegrableOn F S) {x : ℝ^2}
    (hxS : ∀ y ∈ S, 2 * ‖x‖ ≤ ‖y‖) (hint : IntegrableOn (fun y ↦ k (x - y) * F y) S) :
    |∫ y in S, k (x - y) * F y| ≤ A * 2 ^ q * ‖x‖ * ∫ y in S, |F y| / ‖y‖ ^ q := by
  rw [setIntegral_mul_eq_setIntegral_quadrant_signedImageKernel hF₀ hF₁ hS hS₀ hS₁ x hint]
  by_cases hx : x = 0
  · subst hx
    have h0 : ∀ y, signedImageKernel k ε₀ ε₁ 0 y * F y = 0 := fun y ↦ by
      rw [signedImageKernel_zero_left hk₀ hk₁, hvan, zero_mul, zero_mul]
    simp only [h0, integral_zero, abs_zero, norm_zero, mul_zero, zero_mul, le_refl]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hSI := hS.inter measurableSet_quadrant
  set h : ℝ^2 → ℝ := fun y ↦ |F y| / ‖y‖ ^ q
  have hmeas : AEStronglyMeasurable h (volume.restrict S) := by
    have h1 : AEMeasurable (fun y ↦ |F y|) (volume.restrict S) :=
      continuous_abs.measurable.comp_aemeasurable hF.aestronglyMeasurable.aemeasurable
    exact (h1.div (continuous_norm.pow q).measurable.aemeasurable).aestronglyMeasurable
  have hhS : IntegrableOn h S := by
    refine Integrable.mono' (hF.norm.div_const ((2 * ‖x‖) ^ q)) hmeas ?_
    filter_upwards [ae_restrict_mem hS] with y hy
    have hy2 := hxS y hy
    have hypos : 0 < ‖y‖ := by linarith
    simp only [h, Real.norm_eq_abs, abs_div, abs_abs, abs_pow, abs_norm]
    gcongr
  have hpar := abs_apply_coordinateReflection hF₀ hF₁ hε₀ hε₁
  have hquarter := setIntegral_eq_four_mul_inter_quadrant hS hS₀ hS₁ hhS
    (fun y ↦ by simp only [h, hpar.1, PDE.Common.norm_coordinateReflection])
    (fun y ↦ by simp only [h, hpar.2, PDE.Common.norm_coordinateReflection])
  have hGint : IntegrableOn (fun y ↦ 4 * A * 2 ^ q * ‖x‖ * h y) (S ∩ quadrant) :=
    (hhS.mono_set inter_subset_left).const_mul _
  calc |∫ y in S ∩ quadrant, signedImageKernel k ε₀ ε₁ x y * F y|
      ≤ ∫ y in S ∩ quadrant, 4 * A * 2 ^ q * ‖x‖ * h y := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hGint ?_
        filter_upwards [ae_restrict_mem hSI] with y hy
        have hy2 := hxS y hy.1
        have hy0 : y ≠ 0 := by
          intro h0; rw [h0, norm_zero] at hy2; linarith
        rw [Real.norm_eq_abs, abs_mul]
        have hB := abs_signedImageKernel_le_of_far hk hDk hk₀ hk₁ hvan hε₀ hε₁ hy0 hy2
        calc |signedImageKernel k ε₀ ε₁ x y| * |F y|
            ≤ 4 * A * 2 ^ q * ‖x‖ / ‖y‖ ^ q * |F y| := by gcongr
          _ = 4 * A * 2 ^ q * ‖x‖ * h y := by simp only [h]; ring
    _ = A * 2 ^ q * ‖x‖ * ∫ y in S, h y := by
        rw [integral_const_mul, hquarter]
        ring

/-- **The integrated far-field bound.** If the kernel parities make `B(0, ·)` vanish and `F`
vanishes off `{2|x| ≤ |y|}`, then `|∫ k(x - y) F(y) dy| ≤ A 2^q |x| ∫ |F(y)| / |y|^q dy`. -/
theorem abs_integral_mul_le_of_far (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q) {σ₀ σ₁ : ℝ}
    (hk₀ : ∀ z, k (𝐑 0 z) = σ₀ * k z) (hk₁ : ∀ z, k (𝐑 1 z) = σ₁ * k z)
    (hvan : (σ₀ + ε₀) * (σ₁ + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1)
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y)
    (hF : Integrable F) {x : ℝ^2} (hsupp : ∀ y, F y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖)
    (hint : Integrable fun y ↦ k (x - y) * F y) :
    |∫ y, k (x - y) * F y| ≤ A * 2 ^ q * ‖x‖ * ∫ y, |F y| / ‖y‖ ^ q := by
  set S : Set (ℝ^2) := {y | 2 * ‖x‖ ≤ ‖y‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hoff : ∀ y ∉ S, F y = 0 := fun y hy ↦ by
    by_contra h; exact hy (hsupp y h)
  have h1 : ∫ y in S, k (x - y) * F y = ∫ y, k (x - y) * F y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hoff y hy, mul_zero]
  have h2 : ∫ y in S, |F y| / ‖y‖ ^ q = ∫ y, |F y| / ‖y‖ ^ q :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [hoff y hy, abs_zero, zero_div]
  rw [← h1, ← h2]
  exact abs_setIntegral_mul_le_of_far hk hDk hk₀ hk₁ hvan hε₀ hε₁ hF₀ hF₁ hS
    (invariant_norm_le _).1 (invariant_norm_le _).2 hF.integrableOn (fun y hy ↦ hy)
    hint.integrableOn

/-- **The integrated near-field bound on an invariant set.** If `(1 + ε₀)(1 + ε₁) = 0`,
`x ≠ 0` and every point of `S` satisfies `2|y| ≤ |x|`, then
`|∫_S k(x - y) F(y) dy| ≤ A 2^q |x|^(-q) ∫_S |y| |F(y)| dy`. -/
theorem abs_setIntegral_mul_le_of_near (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q)
    (hvan : (1 + ε₀) * (1 + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1)
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y)
    {S : Set (ℝ^2)} (hS : MeasurableSet S) (hS₀ : ∀ y, 𝐑 0 y ∈ S ↔ y ∈ S)
    (hS₁ : ∀ y, 𝐑 1 y ∈ S ↔ y ∈ S) (hF : IntegrableOn F S) {x : ℝ^2} (hx : x ≠ 0)
    (hxS : ∀ y ∈ S, 2 * ‖y‖ ≤ ‖x‖) (hint : IntegrableOn (fun y ↦ k (x - y) * F y) S) :
    |∫ y in S, k (x - y) * F y| ≤ A * 2 ^ q / ‖x‖ ^ q * ∫ y in S, ‖y‖ * |F y| := by
  rw [setIntegral_mul_eq_setIntegral_quadrant_signedImageKernel hF₀ hF₁ hS hS₀ hS₁ x hint]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hSI := hS.inter measurableSet_quadrant
  set h : ℝ^2 → ℝ := fun y ↦ ‖y‖ * |F y|
  have hmeas : AEStronglyMeasurable h (volume.restrict S) :=
    (continuous_norm.aestronglyMeasurable).mul hF.aestronglyMeasurable.norm
  have hhS : IntegrableOn h S := by
    refine Integrable.mono' (hF.norm.const_mul (‖x‖ / 2)) hmeas ?_
    filter_upwards [ae_restrict_mem hS] with y hy
    have hy2 := hxS y hy
    simp only [h, Real.norm_eq_abs, abs_mul, abs_abs, abs_norm]
    gcongr
    linarith
  have hpar := abs_apply_coordinateReflection hF₀ hF₁ hε₀ hε₁
  have hquarter := setIntegral_eq_four_mul_inter_quadrant hS hS₀ hS₁ hhS
    (fun y ↦ by simp only [h, hpar.1, PDE.Common.norm_coordinateReflection])
    (fun y ↦ by simp only [h, hpar.2, PDE.Common.norm_coordinateReflection])
  have hGint : IntegrableOn (fun y ↦ 4 * A * 2 ^ q / ‖x‖ ^ q * h y) (S ∩ quadrant) :=
    (hhS.mono_set inter_subset_left).const_mul _
  calc |∫ y in S ∩ quadrant, signedImageKernel k ε₀ ε₁ x y * F y|
      ≤ ∫ y in S ∩ quadrant, 4 * A * 2 ^ q / ‖x‖ ^ q * h y := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hGint ?_
        filter_upwards [ae_restrict_mem hSI] with y hy
        rw [Real.norm_eq_abs, abs_mul]
        have hB := abs_signedImageKernel_le_of_near hk hDk hvan hε₀ hε₁ hx (hxS y hy.1)
        calc |signedImageKernel k ε₀ ε₁ x y| * |F y|
            ≤ 4 * A * 2 ^ q * ‖y‖ / ‖x‖ ^ q * |F y| := by gcongr
          _ = 4 * A * 2 ^ q / ‖x‖ ^ q * h y := by simp only [h]; ring
    _ = A * 2 ^ q / ‖x‖ ^ q * ∫ y in S, h y := by
        rw [integral_const_mul, hquarter]
        ring

/-- **The integrated near-field bound.** If `(1 + ε₀)(1 + ε₁) = 0`, `x ≠ 0` and `F` vanishes off
`{2|y| ≤ |x|}`, then `|∫ k(x - y) F(y) dy| ≤ A 2^q |x|^(-q) ∫ |y| |F(y)| dy`. -/
theorem abs_integral_mul_le_of_near (hk : ∀ z, z ≠ 0 → DifferentiableAt ℝ k z)
    (hDk : ∀ z, z ≠ 0 → ‖fderiv ℝ k z‖ ≤ A / ‖z‖ ^ q)
    (hvan : (1 + ε₀) * (1 + ε₁) = 0) (hε₀ : |ε₀| = 1) (hε₁ : |ε₁| = 1)
    (hF₀ : ∀ y, F (𝐑 0 y) = ε₀ * F y) (hF₁ : ∀ y, F (𝐑 1 y) = ε₁ * F y)
    (hF : Integrable F) {x : ℝ^2} (hx : x ≠ 0) (hsupp : ∀ y, F y ≠ 0 → 2 * ‖y‖ ≤ ‖x‖)
    (hint : Integrable fun y ↦ k (x - y) * F y) :
    |∫ y, k (x - y) * F y| ≤ A * 2 ^ q / ‖x‖ ^ q * ∫ y, ‖y‖ * |F y| := by
  set S : Set (ℝ^2) := {y | ‖y‖ ≤ ‖x‖ / 2}
  have hS : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have hoff : ∀ y ∉ S, F y = 0 := fun y hy ↦ by
    by_contra h; exact hy (by have := hsupp y h; change ‖y‖ ≤ ‖x‖ / 2; linarith)
  have h1 : ∫ y in S, k (x - y) * F y = ∫ y, k (x - y) * F y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hoff y hy, mul_zero]
  have h2 : ∫ y in S, ‖y‖ * |F y| = ∫ y, ‖y‖ * |F y| :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      rw [hoff y hy, abs_zero, mul_zero]
  rw [← h1, ← h2]
  exact abs_setIntegral_mul_le_of_near hk hDk hvan hε₀ hε₁ hF₀ hF₁ hS
    (invariant_le_norm _).1 (invariant_le_norm _).2 hF.integrableOn hx
    (fun y hy ↦ by have : ‖y‖ ≤ ‖x‖ / 2 := hy; linarith) hint.integrableOn

end Integrated

/-! ### The gradient and Hessian kernels -/

section Kernels

/-- The parities of the gradient kernels: `gⱼ(Rᵢ z) = -gⱼ(z)` for `i = j` and `gⱼ(z)` for
`i ≠ j`. -/
theorem gradientKernel_coordinateReflection (i j : Fin 2) (z : ℝ^2) :
    gradientKernel j (𝐑 i z) = (if i = j then -1 else 1) * gradientKernel j z := by
  rw [gradientKernel_eq_div, gradientKernel_eq_div, PDE.Common.norm_coordinateReflection]
  fin_cases i <;> fin_cases j <;>
    simp [PDE.Common.coordinateReflection_apply_same,
      PDE.Common.coordinateReflection_apply_of_ne] <;> ring

/-- The parities of the Hessian kernels: `kᵢⱼ(Rₗ z) = kᵢⱼ(z)` for `i = j` and `-kᵢⱼ(z)` for
`i ≠ j`. -/
theorem hessianKernel_coordinateReflection (i j l : Fin 2) (z : ℝ^2) :
    hessianKernel i j (𝐑 l z) = (if i = j then 1 else -1) * hessianKernel i j z := by
  fin_cases i <;> fin_cases j
  · simp [hessianKernel_zero_zero_coordinateReflection]
  · simp [hessianKernel_zero_one_coordinateReflection]
  · simp [hessianKernel_one_zero, hessianKernel_zero_one_coordinateReflection]
  · simp [hessianKernel_one_one, hessianKernel_zero_zero_coordinateReflection]

/-- The gradient kernels are differentiable away from the pole. -/
theorem differentiableAt_gradientKernel (j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    DifferentiableAt ℝ (gradientKernel j) z :=
  (contDiffAt_gradientKernel j hz (n := 1)).differentiableAt (by norm_num)

/-- The Hessian kernels are differentiable away from the pole. -/
theorem differentiableAt_hessianKernel (i j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    DifferentiableAt ℝ (hessianKernel i j) z :=
  (contDiffAt_hessianKernel i j hz (n := 1)).differentiableAt (by norm_num)

/-- `|Dgⱼ(z)| ≤ π⁻¹ |z|⁻²` away from the pole. -/
theorem norm_fderiv_gradientKernel_le (j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    ‖fderiv ℝ (gradientKernel j) z‖ ≤ 1 / Real.pi / ‖z‖ ^ 2 := by
  refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ z).trans ?_
  rw [Fin.sum_univ_two]
  change |(∂[(0 : Fin 2)] (gradientKernel j)) z| + |(∂[(1 : Fin 2)] (gradientKernel j)) z| ≤ _
  rw [partialDeriv_gradientKernel 0 j hz, partialDeriv_gradientKernel 1 j hz, abs_div,
    abs_div, abs_of_pos Real.pi_pos]
  have h0 := abs_hessianKernel_le 0 j z
  have h1 := abs_hessianKernel_le 1 j z
  have hpi := Real.pi_pos
  have hz2 : 0 < ‖z‖ ^ 2 := by have := norm_pos_iff.mpr hz; positivity
  calc |hessianKernel 0 j z| / Real.pi + |hessianKernel 1 j z| / Real.pi
      ≤ 1 / (2 * ‖z‖ ^ 2) / Real.pi + 1 / (2 * ‖z‖ ^ 2) / Real.pi := by gcongr
    _ = 1 / Real.pi / ‖z‖ ^ 2 := by field_simp; ring

/-- `|Dk₀ₗ(z)| ≤ 2 |z|⁻³` away from the pole. -/
private theorem norm_fderiv_hessianKernel_zero_le (l : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    ‖fderiv ℝ (hessianKernel 0 l) z‖ ≤ 2 / ‖z‖ ^ 3 := by
  refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ z).trans ?_
  rw [Fin.sum_univ_two]
  change |(∂[(0 : Fin 2)] (hessianKernel 0 l)) z| + |(∂[(1 : Fin 2)] (hessianKernel 0 l)) z| ≤ _
  have h0 := abs_iterate_partialDeriv_hessianKernel_le l 1 0 hz
  have h1 := abs_iterate_partialDeriv_hessianKernel_le l 0 1 hz
  simp only [Function.iterate_one, Function.iterate_zero, id] at h0 h1
  norm_num at h0 h1
  calc _ ≤ (‖z‖ ^ 3)⁻¹ + (‖z‖ ^ 3)⁻¹ := add_le_add h0 h1
    _ = 2 / ‖z‖ ^ 3 := by ring

/-- `|Dkᵢⱼ(z)| ≤ 2 |z|⁻³` away from the pole. -/
theorem norm_fderiv_hessianKernel_le (i j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    ‖fderiv ℝ (hessianKernel i j) z‖ ≤ 2 / ‖z‖ ^ 3 := by
  fin_cases i
  · exact norm_fderiv_hessianKernel_zero_le j hz
  · fin_cases j
    · have h : hessianKernel 1 0 = hessianKernel 0 1 := funext hessianKernel_one_zero
      simpa [h] using norm_fderiv_hessianKernel_zero_le 1 hz
    · have h : hessianKernel 1 1 = fun y ↦ -hessianKernel 0 0 y := funext hessianKernel_one_one
      simpa [h, fderiv_neg] using norm_fderiv_hessianKernel_zero_le 0 hz

end Kernels

end IncompressibleFlow
