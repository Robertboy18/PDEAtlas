/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.KernelLaplacian.ScalarDerivatives
import PDE.Elliptic.PotentialTheory.FundamentalSolution -- shake: keep

/-!
# Laplacian of the singular sphere integral

We sum the repeated coordinate derivatives of

`B(x) = ∫_{∂B(0,r)} g(y) / ‖x - y‖ⁿ dS(y)`

computed in `KernelLaplacian.ScalarDerivatives`. With `d = ‖x - y‖` and `t = (x - y)ᵢ`, each
`∂ᵢ∂ᵢ` contributes `-n / dⁿ⁺² + n (n + 2) tᵢ² / dⁿ⁺⁴` to the integrand; summing over `i` and using
`∑ᵢ tᵢ² = d²` gives `-n² / dⁿ⁺² + n (n + 2) / dⁿ⁺² = 2n / dⁿ⁺²`. So `ΔB(x)` is the sphere integral
of `g(y) · 2n / ‖x - y‖ⁿ⁺²`, by the identity `Δ(‖x‖⁻ⁿ) = 2n ‖x‖⁻ⁿ⁻²` for the inverse `n`-th
power of the distance in `ℝ^n`.

Each first coordinate derivative `∂ᵢ B` is itself differentiable at interior points, as the
product-rule computation of `KernelLaplacian` requires.

## Main results

* `laplacian_sphereIntegral_div_distance_pow_scalar`: the closed form of `ΔB(x)` for `x ∈ B(0, r)`.
* `differentiableAt_partialDeriv_sphereIntegral_div_distance_pow`: differentiability of
  `x ↦ ∂ᵢ B(x)` at interior points.
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open scoped BigOperators

open MeasureTheory
open PDE.Analysis
open PotentialTheory

variable {n : ℕ}

namespace KernelLaplacian

section PoissonKernelLaplacian

/-- The Laplacian of the singular sphere integral after summing its coordinate derivatives. -/
theorem laplacian_sphereIntegral_div_distance_pow_scalar {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    laplacian (n := n)
        (fun w : ℝ^n ↦
          PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist w y ^ n) 0 r) x =
      (|r| ^ (n - 1) : ℝ) *
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          g (r • (ω : ℝ^n)) * ((2 * (n : ℝ)) / dist x (r • (ω : ℝ^n)) ^ (n + 2))
          ∂((volume : Measure ℝ^n).toSphere) := by
  classical
  unfold laplacian
  have hxy (ω : ↑(Metric.sphere (0 : ℝ^n) 1)) : dist x (r • (ω : ℝ^n)) ≠ 0 :=
    distance_ne_zero_of_mem_ball_mem_sphere hx (smul_unitSphere_mem_sphere hr.le ω)
  have hgc : Continuous fun ω : ↑(Metric.sphere (0 : ℝ^n) 1) ↦ g (r • (ω : ℝ^n)) :=
    hg.comp_continuous (continuous_sphere_smul r) (smul_unitSphere_mem_sphere hr.le)
  simp_rw [secondPartial_sphereIntegral_div_distance_pow_scalar hr hg _ hx, ← Finset.mul_sum]
  rw [← integral_finsetSum]
  · congr 1
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    have hsq : ∑ i, (x - r • (ω : ℝ^n)) i ^ 2 = dist x (r • (ω : ℝ^n)) ^ 2 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    have := hxy ω
    dsimp only
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum, hsq,
      show dist x (r • (ω : ℝ^n)) ^ (n + 4) = dist x (r • (ω : ℝ^n)) ^ (n + 2) *
        dist x (r • (ω : ℝ^n)) ^ 2 by ring]
    field_simp
    push_cast
    ring
  · intro i _
    apply integrableOn_univ.1
    refine (hgc.mul ?_).continuousOn.integrableOn_compact isCompact_univ
    fun_prop (disch := exact fun ω ↦ pow_ne_zero _ (hxy ω))

/-- Each first coordinate derivative of the singular sphere integral is differentiable inside the
ball. -/
theorem differentiableAt_partialDeriv_sphereIntegral_div_distance_pow {r : ℝ} (hr : 0 < r)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : ℝ^n) r))
    (i : Fin n) {x : ℝ^n} (hx : x ∈ Metric.ball (0 : ℝ^n) r) :
    DifferentiableAt ℝ
      (fun z : ℝ^n ↦
        (∂[i]
          (fun w : ℝ^n ↦
            PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist w y ^ n) 0 r)) z)
      x := by
  classical
  let B : ℝ^n → ℝ :=
    fun w : ℝ^n ↦
      PDE.Analysis.sphereIntegral n (fun y ↦ g y / dist w y ^ n) 0 r
  let Φ : ℝ^n → ℝ :=
    fun z : ℝ^n ↦
      (|r| ^ (n - 1) : ℝ) *
        ∫ ω : ↑(Metric.sphere (0 : ℝ^n) (1 : ℝ)),
          g (r • (ω : ℝ^n)) *
            EuclideanDistance.invDistPowFDerivFormula n z (r • (ω : ℝ^n))
              (EuclideanSpace.single i (1 : ℝ))
          ∂((volume : Measure ℝ^n).toSphere)
  have hopen : IsOpen (Metric.ball (0 : ℝ^n) r) := Metric.isOpen_ball
  have hxnhds : Metric.ball (0 : ℝ^n) r ∈ nhds x := hopen.mem_nhds hx
  have hEq : (fun z : ℝ^n ↦ (∂[i] B) z) =ᶠ[nhds x] Φ := by
    filter_upwards [hxnhds] with z hz
    simpa [B, Φ] using
      (partialDeriv_sphereIntegral_div_distance_pow_scalar (n := n) (r := r) hr hg i (x := z) hz)
  have hΦ : DifferentiableAt ℝ Φ x := by
    -- `Φ` is exactly the scalar integral differentiated by
    -- `hasFDerivAt_sphereIntegral_invDistPowFDeriv_apply`.
    have h :=
      (hasFDerivAt_sphereIntegral_invDistPowFDeriv_apply (n := n) (r := r) hr hg (x₀ := x) hx
          (EuclideanSpace.single i (1 : ℝ)))
    exact h.differentiableAt
  -- Transfer differentiability back to `z ↦ ∂i B z` using the local equality.
  have hB' : DifferentiableAt ℝ (fun z : ℝ^n ↦ (∂[i] B) z) x :=
    hΦ.congr_of_eventuallyEq hEq
  simpa [B] using hB'

end PoissonKernelLaplacian

end KernelLaplacian

end GreenFunction
