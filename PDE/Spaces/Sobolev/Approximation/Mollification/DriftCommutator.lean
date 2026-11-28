/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
public import PDE.Analysis.Integration.ConvolutionDrift
public import PDE.Analysis.Integration.ConvolutionL2
import Mathlib.Algebra.Order.Chebyshev
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.Spaces.Sobolev.Approximation.Mollification.L2Operator

/-!
# The commutator of mollification and the drift `x·∇`, through weak derivatives

For a locally integrable `g` the commutator of the mollification `ρ ∗` with the drift `x·∇` is
`-(g ∗ K)` with the kernel `K = div (z ρ(z))` (`PDE.Analysis.driftCommutator`). When `g` has weak
derivatives, we move the derivatives of `K` onto `g` and bound the commutator and its
derivatives in `L²` by the weak derivatives of one order higher: for a mollifier that vanishes
outside the ball of radius `R`, `∫ (g ∗ ∂^β K_ε)² ≤ n (ε R)² Σⱼ ∫ (∂ⱼ∂^β g)²`. With `β` of length
`k - 1` this is the commutator bound (2.10) of Hou, Wang and Yang,
`‖ρ_ε(y) y‖_{L¹} ‖∇ᵏU‖_{L²} ≲ ε ‖U‖_{Hᵏ}`. Together with
`PDE.Analysis.driftCommutator_iteratedPartialDeriv`, which writes the commutator for the kernel
`∂^α ρ` with `g ∗ ∂^α K`, it controls the commutator in each step of a regularity induction.

## Main results

* `convolution_iteratedPartialDeriv_driftKernel`: in every dimension, for every smooth compactly
  supported `ρ`, if `g` has the weak derivative `∂^β g` and this has first weak derivatives
  `∂ⱼ∂^β g`, then `g ∗ ∂^β K = Σⱼ (∂ⱼ∂^β g) ∗ (zⱼ ρ)`. With `β` empty this is the formula
  `-∫ ρ(y) y·∇g(x - y) dy` of the commutator.
* `integral_norm_coord_mul_scaled_le`: `∫ |zⱼ| ρ_ε(z) dz ≤ ε R` for every `ε > 0` and every
  mollifier that vanishes outside the ball of radius `R`.
* `integral_sq_convolution_iteratedPartialDeriv_driftKernel_le`: the `L²` bound above, when the
  `∂ⱼ∂^β g` are square integrable.

## How it works

`K = Σⱼ ∂ⱼ(zⱼ ρ)` (`PDE.Analysis.driftKernel_eq_sum`), so each derivative of the kernel moves to
`g` as a weak derivative (`convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn`). The
kernel `zⱼ ρ_ε(z)` has `L¹` norm at most `ε R`, Young's inequality
(`PDE.Analysis.integral_sq_convolution_le`) bounds each of the `n` terms, and the square of a sum
of `n` terms is at most `n` times the sum of their squares.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2, the commutator bound
  (2.10). <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open ContinuousLinearMap (mul)
open PDE (iteratedPartialDeriv)
open PDE.Analysis
open scoped Convolution

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- **The commutator through weak derivatives.** If `gβ` is the weak derivative `∂^β g` and
`h j` is the weak derivative `∂ⱼ gβ`, then `g ∗ ∂^β K = Σⱼ (h j) ∗ (zⱼ ρ)` at every point, for
the kernel `K = div (z ρ(z))` of the commutator. With `β` empty this is the formula
`-∫ ρ(y) y·∇g(x - y) dy` of the commutator. -/
theorem convolution_iteratedPartialDeriv_driftKernel {g gβ : ℝ^n → ℝ} {h : Fin n → ℝ^n → ℝ}
    {β : List (Fin n)} (hβ : HasWeakDerivativeOn univ β g gβ)
    (hh : ∀ j, HasWeakDerivativeOn univ [j] gβ (h j))
    {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (x : ℝ^n) :
    (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv β (driftKernel ρ)) x =
      ∑ j, (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * ρ z) x := by
  have hkj : ∀ j : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ^n ↦ z j * ρ z) := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.mul hρ
  have hkjc : ∀ j : Fin n, HasCompactSupport (fun z : ℝ^n ↦ z j * ρ z) := fun j ↦
    hρc.mul_left
  have h1 := convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn hβ
    (contDiff_driftKernel hρ) (hasCompactSupport_driftKernel hρc) x (subset_univ _)
  rw [indicator_univ, indicator_univ] at h1
  have h2 : ∀ j : Fin n, (gβ ⋆[mul ℝ ℝ, volume] ∂[j] (fun z ↦ z j * ρ z)) x =
      (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * ρ z) x := fun j ↦ by
    have h := convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn (hh j) (hkj j) (hkjc j)
      x (subset_univ _)
    rw [indicator_univ, indicator_univ] at h
    exact h
  have hgβ : LocallyIntegrable gβ volume := locallyIntegrableOn_univ.mp hβ.locallyIntegrable_g
  have hkj1 : ∀ j : Fin n, ContDiff ℝ 1 (fun z : ℝ^n ↦ z j * ρ z) := fun j ↦
    (hkj j).of_le (by simp)
  have hint : ∀ j : Fin n, Integrable fun y ↦ gβ y * ∂[j] (fun z ↦ z j * ρ z) (x - y) :=
    fun j ↦ integrable_mul_comp_const_sub hgβ ((hkj1 j).continuous_partialDeriv j)
      ((hkjc j).partialDeriv j) x
  rw [h1]
  simp only [← h2]
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_finsetSum _ fun j _ ↦ hint j]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  beta_reduce
  rw [driftKernel_eq_sum (hρ.differentiable (by simp) _), Finset.mul_sum]

/-- The first moment of a scaled mollifier: `zⱼ ρ_ε(z)` is integrable and
`∫ |zⱼ| ρ_ε(z) dz ≤ ε R` when `ρ` vanishes outside the ball of radius `R`, since `ρ_ε` has mass
one and vanishes outside the ball of radius `ε R`. -/
theorem integral_norm_coord_mul_scaled_le (μ : Mollifier n) {ε R : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R) (j : Fin n) :
    Integrable (fun z : ℝ^n ↦ z j * scaled μ ε z) ∧
      ∫ z : ℝ^n, ‖z j * scaled μ ε z‖ ≤ ε * R := by
  have hint : Integrable (fun z : ℝ^n ↦ z j * scaled μ ε z) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.mul
      (scaled_contDiff μ).continuous).integrable_of_hasCompactSupport
      (scaled_hasCompactSupport μ hε).mul_left
  refine ⟨hint, ?_⟩
  have hpt : ∀ z : ℝ^n, ‖z j * scaled μ ε z‖ ≤ ε * R * scaled μ ε z := fun z ↦ by
    have h0 := scaled_nonneg μ hε z
    rw [norm_mul, Real.norm_of_nonneg h0]
    by_cases hz : scaled μ ε z = 0
    · rw [hz, mul_zero, mul_zero]
    · have hmem := support_scaled_subset_closedBall μ hε hR (Function.mem_support.mpr hz)
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le z j).trans hmem) h0
  calc ∫ z : ℝ^n, ‖z j * scaled μ ε z‖ ≤ ∫ z : ℝ^n, ε * R * scaled μ ε z :=
        integral_mono hint.norm ((integrable_scaled μ hε).const_mul _) hpt
    _ = ε * R := by rw [integral_const_mul, scaled_integral_one μ hε, mul_one]

/-- **The commutator bound (2.10) of Hou, Wang and Yang**, in squares: if `gβ` is the weak
derivative `∂^β g` and its first weak derivatives `h j` are square integrable, then for a
mollifier that vanishes outside the ball of radius `R`

`∫ (g ∗ ∂^β K_ε)² ≤ n (ε R)² Σⱼ ∫ (h j)²`,

with `K_ε` the kernel of the commutator for `ρ_ε`. The function `g ∗ ∂^β K_ε` is `-∂^β` of the
commutator. -/
theorem integral_sq_convolution_iteratedPartialDeriv_driftKernel_le (μ : Mollifier n)
    {ε R : ℝ} (hε : 0 < ε) (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    {g gβ : ℝ^n → ℝ} {h : Fin n → ℝ^n → ℝ} {β : List (Fin n)}
    (hβ : HasWeakDerivativeOn univ β g gβ) (hh : ∀ j, HasWeakDerivativeOn univ [j] gβ (h j))
    (hh2 : ∀ j, MemLp (h j) 2 volume) :
    MemLp (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv β (driftKernel (scaled μ ε))) 2 volume ∧
      ∫ x, (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv β (driftKernel (scaled μ ε))) x ^ 2 ≤
        n * (ε * R) ^ 2 * ∑ j, ∫ x, h j x ^ 2 := by
  have hfun : (g ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv β (driftKernel (scaled μ ε))) =
      fun x ↦ ∑ j, (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x :=
    funext fun x ↦ convolution_iteratedPartialDeriv_driftKernel hβ hh (scaled_contDiff μ)
      (scaled_hasCompactSupport μ hε) x
  have hY := fun j ↦ integral_sq_convolution_le (hh2 j)
    (integral_norm_coord_mul_scaled_le μ hε hR j).1
  rw [hfun]
  refine ⟨memLp_finsetSum _ fun j _ ↦ (hY j).1, ?_⟩
  have hsq : ∀ j, Integrable fun x ↦
      (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x ^ 2 := fun j ↦ (hY j).1.integrable_sq
  calc ∫ x, (∑ j, (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x) ^ 2
      ≤ ∫ x, (n : ℝ) * ∑ j, (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x ^ 2 := by
        refine integral_mono_of_nonneg (.of_forall fun x ↦ sq_nonneg _)
          ((integrable_finsetSum _ fun j _ ↦ hsq j).const_mul _) (.of_forall fun x ↦ ?_)
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j ↦ (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x)
        simpa only [Finset.card_univ, Fintype.card_fin] using this
    _ = n * ∑ j, ∫ x, (h j ⋆[mul ℝ ℝ, volume] fun z ↦ z j * scaled μ ε z) x ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hsq j]
    _ ≤ n * ∑ j, (ε * R) ^ 2 * ∫ x, h j x ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ (hY j).2.trans ?_)
          (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (integral_nonneg fun z ↦ norm_nonneg _)
            (integral_norm_coord_mul_scaled_le μ hε hR j).2 2)
          (integral_nonneg fun x ↦ sq_nonneg _)
    _ = n * (ε * R) ^ 2 * ∑ j, ∫ x, h j x ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

end SobolevSpace.Approximation
