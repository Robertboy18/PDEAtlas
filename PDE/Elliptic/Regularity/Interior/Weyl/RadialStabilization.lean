/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Radial
public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
import PDE.Analysis.Integration.RadialMean
import PDE.Analysis.Convolution.CompactKernels

/-!
# Stabilization of radial harmonic mollifications

A radial mollifier fixes a harmonic function wherever its support fits inside the harmonicity
domain. Applying this to two harmonic mollifications and interchanging their kernels proves
that the two mollifications agree. The kernel is the explicit radial witness, rather than an
arbitrary smooth bump.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace SobolevSpace.Approximation

/-- Scaling a radial mollifier preserves its radial profile. -/
theorem scaled_eq_radial {n : ℕ} {μ : Mollifier n} {w : ℝ → ℝ}
    (hrad : ∀ x, μ.ρ x = w ‖x‖) {ε : ℝ} (hε : 0 < ε) :
    scaled μ ε = fun x ↦ (ε⁻¹) ^ n * w (ε⁻¹ * ‖x‖) := by
  ext x
  rw [scaled_of_pos μ hε]
  change ε⁻¹ ^ n * μ.ρ (ε⁻¹ • x) = ε⁻¹ ^ n * w (ε⁻¹ * ‖x‖)
  rw [hrad]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]

/-- A radial profile vanishing from radius two has scaled topological support in radius `2ε`. -/
theorem tsupport_scaled_subset_of_radial {n : ℕ} {μ : Mollifier n} {w : ℝ → ℝ}
    (hrad : ∀ x, μ.ρ x = w ‖x‖) (hz : ∀ r, 2 ≤ r → w r = 0)
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaled μ ε) ⊆ Metric.closedBall (0 : ℝ^n) (2 * ε) := by
  have hs : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) 2 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hx (by rw [hrad, hz _ (le_of_lt (lt_of_not_ge h))])
  apply closure_minimal _ Metric.isClosed_closedBall
  simpa only [mul_comm ε 2] using support_scaled_subset_closedBall μ hε hs

/-- A scaled radial mollifier fixes a harmonic function at the center of an admissible ball.
Only continuity on that closed ball is used to justify the weighted integral. -/
theorem mollify_eq_of_isHarmonicPDE {n : ℕ} [Fact (0 < n)]
    {μ : Mollifier n} {w : ℝ → ℝ} (hw : Continuous w)
    (hrad : ∀ x, μ.ρ x = w ‖x‖) (hz : ∀ r, 2 ≤ r → w r = 0)
    {v : ℝ^n → ℝ} {U : Set (ℝ^n)} (hv : LaplacianEquation.IsHarmonicPDE n v U)
    {x : ℝ^n} {ε : ℝ} (hε : 0 < ε)
    (hball : Metric.closedBall x (2 * ε) ⊆ U) :
    mollify μ ε v x = v x := by
  let q : ℝ → ℝ := fun r ↦ (ε⁻¹) ^ n * w (ε⁻¹ * r)
  have hq : Continuous q := continuous_const.mul (hw.comp (continuous_const.mul continuous_id))
  have hkernel : scaled μ ε = fun y : ℝ^n ↦ q ‖y‖ := scaled_eq_radial hrad hε
  have hqi : Integrable (fun y : ℝ^n ↦ q ‖y‖) := by
    rw [← hkernel]
    exact (scaled_contDiff μ).continuous.integrable_of_hasCompactSupport
      (scaled_hasCompactSupport μ hε)
  have hprod : IntegrableOn (fun y ↦ q (dist y x) * v y) (Metric.ball x (2 * ε)) := by
    apply IntegrableOn.mono_set _ Metric.ball_subset_closedBall
    exact ((hq.comp (continuous_id.dist continuous_const)).continuousOn.mul
      (hv.contDiffOn.continuousOn.mono hball)).integrableOn_compact
        (isCompact_closedBall x (2 * ε))
  unfold mollify
  rw [convolution_lsmul_eq_mul, hkernel]
  refine PDE.Analysis.convolution_radial_eq_of_sphereAverage_eq
      (r := 2 * ε) ?_ ?_ hqi hprod ?_
  · intro s hs hse
    exact hv.hasSphereMeanValueProperty x
      (hball (Metric.mem_closedBall_self (by positivity))) s hs
      ((Metric.closedBall_subset_closedBall hse).trans hball)
  · intro s hs
    have hwzero : w (ε⁻¹ * s) = 0 := by
      apply hz
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hε).mpr hs
    simp only [q, hwzero, mul_zero]
  · rw [← hkernel]
    exact scaled_integral_one μ hε

/-- Two harmonic mollifications coincide wherever both averaging balls fit inside their common
harmonicity domain. The original function is only locally integrable. -/
theorem mollify_eq_mollify_of_isHarmonicPDE {n : ℕ} [Fact (0 < n)]
    {μ : Mollifier n} {w : ℝ → ℝ} (hw : Continuous w)
    (hrad : ∀ x, μ.ρ x = w ‖x‖) (hz : ∀ r, 2 ≤ r → w r = 0)
    {f : ℝ^n → ℝ} (hf : LocallyIntegrable f volume)
    {U : Set (ℝ^n)} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (huε : LaplacianEquation.IsHarmonicPDE n (mollify μ ε f) U)
    (huδ : LaplacianEquation.IsHarmonicPDE n (mollify μ δ f) U)
    {x : ℝ^n} (hballε : Metric.closedBall x (2 * ε) ⊆ U)
    (hballδ : Metric.closedBall x (2 * δ) ⊆ U) :
    mollify μ ε f x = mollify μ δ f x := by
  have hswap : mollify μ δ (mollify μ ε f) = mollify μ ε (mollify μ δ f) := by
    simp only [mollify, convolution_lsmul_eq_mul]
    rw [convolution_symm _ ContinuousLinearMap.flip_mul (f := scaled μ ε) (f' := f),
      convolution_symm _ ContinuousLinearMap.flip_mul (f := scaled μ δ) (f' := f),
      convolution_symm _ ContinuousLinearMap.flip_mul (f := scaled μ δ),
      convolution_symm _ ContinuousLinearMap.flip_mul (f := scaled μ ε)]
    exact PDE.Analysis.convolution_compact_kernels_interchange hf
      (scaled_contDiff μ).continuous (scaled_contDiff μ).continuous
      (scaled_hasCompactSupport μ hε) (scaled_hasCompactSupport μ hδ)
  calc
    mollify μ ε f x = mollify μ δ (mollify μ ε f) x :=
      (mollify_eq_of_isHarmonicPDE hw hrad hz huε hδ hballδ).symm
    _ = mollify μ ε (mollify μ δ f) x := congrFun hswap x
    _ = mollify μ δ f x := mollify_eq_of_isHarmonicPDE hw hrad hz huδ hε hballε

end SobolevSpace.Approximation
