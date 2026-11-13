/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.NonlinearApproximation
public import PDE.Hyperbolic.Models.Wave.Regularization.Spatial

/-!
# The nonlinear residual after spatial smoothing

Spatial smoothing commutes with the tested linear wave operator. The remaining
error is the commutator of convolution and the continuous reaction. Its locally
uniform convergence to zero lets energy identities pass to the original field.
-/

public section

open Filter Set MeasureTheory
open scoped Topology Convolution

namespace WaveEquation

/-- The equation residual of spatially smoothed tested solutions converges
locally uniformly to zero. The reaction is only continuous. -/
theorem tendstoLocallyUniformlyOn_convolution_wave_residual {n : ℕ} {u : ℝ × ℝ^n → ℝ} {I : Set ℝ}
    {g : ℝ → ℝ} (hu : ContinuousOn u (I ×ˢ univ)) (hg : Continuous g)
    (hw : ∀ t ∈ I, ∀ ψ : ℝ^n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      HasDerivAt (deriv (fun s ↦ ∫ y, u (s, y) * ψ y))
      ((∫ y, u (t, y) * PDE.laplacian ψ y) - ∫ y, g (u (t, y)) * ψ y) t)
    {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ^n)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    let U := fun i (p : ℝ × ℝ^n) ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y ↦ u (p.1, y))) p.2
    TendstoLocallyUniformlyOn
      (fun i p ↦ deriv (deriv (fun s ↦ U i (s, p.2))) p.1 -
        PDE.laplacian (fun y ↦ U i (p.1, y)) p.2 + g (U i p))
      (fun _ ↦ 0) l (I ×ˢ univ) := by
  dsimp only
  refine (ContDiffBump.tendstoLocallyUniformlyOn_comp_convolution_sub_convolution_comp
    (μ := volume) hu hg hφ).congr ?_
  intro i p hp
  let κ := (φ i).normed volume
  have hswap (f : ℝ^n → ℝ) :
      f ⋆[ContinuousLinearMap.mul ℝ ℝ] κ = κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f := by
    funext x
    rw [convolution_mul_swap, convolution_lsmul]
    simp only [smul_eq_mul, mul_comm]
  have hneg : (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y ↦ -g (u (p.1, y)))) p.2 =
        -((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y ↦ g (u (p.1, y)))) p.2) := by
    simp only [convolution_lsmul, smul_eq_mul, mul_neg, integral_neg]
  have huloc : LocallyIntegrable (fun y ↦ u (p.1, y)) volume :=
    (hu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hp.1, mem_univ _⟩)).locallyIntegrable
  have hd := hasDerivAt_deriv_convolution_of_tested_wave
    (u := fun t y ↦ u (t, y)) (t := p.1) (κ := κ) (F := fun t y ↦ -g (u (t, y))) huloc
    (fun ψ hψ hψs ↦ by
      simpa only [neg_mul, integral_neg, sub_eq_add_neg] using hw p.1 hp.1 ψ hψ hψs)
    ((φ i).contDiff_normed (μ := volume)) ((φ i).hasCompactSupport_normed (μ := volume)) p.2
  have heq := hd.deriv
  simp_rw [hswap] at heq
  rw [hneg] at heq
  change _ = _ - _ + _
  rw [heq]
  dsimp only [κ]
  abel

end WaveEquation
