/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.FDeriv.Calculus.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.FDeriv.Laplacian.Congruence

/-!
# Smooth potentials away from a kernel singularity

When the source measure stays away from an evaluation point and within bounded
distance of it, an annular cutoff replaces a singular kernel by a compactly
supported smooth function. Mathlib's convolution theorem then gives the same
regularity for the potential. The measure need not be translation invariant;
surface measures are one application.

For a scalar kernel, the same cutoff transfers the coordinate Laplacian under
the integral. In particular, a kernel harmonic away from zero gives a harmonic
potential wherever the source measure stays away from the evaluation point.
-/

@[expose] public section

open Filter Function Metric Set
open scoped Topology Convolution

namespace MeasureTheory

/-- A potential with a kernel smooth away from zero is smooth at a point separated
from its source measure. The upper distance bound lets a compact cutoff preserve
the kernel on all relevant differences. No translation invariance of the measure
is needed, so the theorem also applies to boundary measures. -/
theorem contDiffAt_integral_smul_sub_of_annulus
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {m : ℕ∞} {K : E → F} (hK : ContDiffOn ℝ m K ({0}ᶜ : Set E))
    {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {x : E} {a b : ℝ} (ha : 0 < a)
    (hsource : ∀ᵐ y ∂μ, a ≤ dist x y ∧ dist x y ≤ b) :
    ContDiffAt ℝ m (fun z ↦ ∫ y, f y • K (z - y) ∂μ) x := by
  obtain ⟨G, hG, hGc, hGeq⟩ :=
    hK.exists_contDiff_compactSupport_eqOn_annulus (half_pos ha)
      (add_pos_of_nonneg_of_pos (le_max_right b 0) ha)
  have hconv : ContDiff ℝ m (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) :=
    hGc.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hG
  apply hconv.contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds x (half_pos ha)] with z hz
  apply integral_congr_ae
  filter_upwards [hsource] with y hy
  have hzx : dist z x < a / 2 := hz
  have hlower : a / 2 ≤ ‖z - y‖ := by
    have htriangle := dist_triangle x z y
    rw [dist_comm x z] at htriangle
    rw [← dist_eq_norm]
    linarith [hy.1]
  have hupper : ‖z - y‖ ≤ max b 0 + a := by
    rw [← dist_eq_norm]
    exact (dist_triangle z x y).trans
      (by linarith [hy.2, le_max_left b 0])
  rw [hGeq (z - y) hlower hupper]
  rfl

/-- Away from a kernel singularity, the Laplacian passes under the potential integral.
The source measure may be restricted volume or a boundary measure. This only uses
the kernel on an annulus around the evaluation point. -/
theorem laplacian_integral_mul_sub_of_annulus
    {n : ℕ} {μ : Measure (ℝ^n)} {K : ℝ^n → ℝ}
    (hK : ContDiffOn ℝ 2 K ({0}ᶜ : Set (ℝ^n)))
    {f : ℝ^n → ℝ} (hf : LocallyIntegrable f μ)
    {x : ℝ^n} {a b : ℝ} (ha : 0 < a)
    (hsource : ∀ᵐ y ∂μ, a ≤ dist x y ∧ dist x y ≤ b) :
    PDE.laplacian (fun z ↦ ∫ y, f y * K (z - y) ∂μ) x =
      ∫ y, f y * PDE.laplacian K (x - y) ∂μ := by
  obtain ⟨G, hG, hGc, hGeq⟩ :=
    hK.exists_contDiff_compactSupport_eqOn_annulus (half_pos ha)
      (add_pos_of_nonneg_of_pos (le_max_right b 0) ha)
  have hpotential : (fun z ↦ ∫ y, f y * K (z - y) ∂μ) =ᶠ[𝓝 x]
      f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] G := by
    filter_upwards [ball_mem_nhds x (half_pos ha)] with z hz
    apply integral_congr_ae
    filter_upwards [hsource] with y hy
    have hzx : dist z x < a / 2 := hz
    have hlower : a / 2 ≤ ‖z - y‖ := by
      have htriangle := dist_triangle x z y
      rw [dist_comm x z] at htriangle
      rw [← dist_eq_norm]
      linarith [hy.1]
    have hupper : ‖z - y‖ ≤ max b 0 + a := by
      rw [← dist_eq_norm]
      exact (dist_triangle z x y).trans
        (by linarith [hy.2, le_max_left b 0])
    rw [hGeq (z - y) hlower hupper]
    rfl
  rw [EuclideanLaplacian.laplacian_congr_nhds hpotential,
    PDE.laplacian_convolution_right hf hGc hG]
  apply integral_congr_ae
  filter_upwards [hsource] with y hy
  have hlower : a / 2 < ‖x - y‖ := by
    rw [← dist_eq_norm]
    linarith [hy.1]
  have hupper : ‖x - y‖ < max b 0 + a := by
    rw [← dist_eq_norm]
    linarith [hy.2, le_max_left b 0]
  have hkernel : G =ᶠ[𝓝 (x - y)] K := by
    filter_upwards [continuous_norm.continuousAt.eventually
      (Ioo_mem_nhds hlower hupper)] with z hz
    exact hGeq z hz.1.le hz.2.le
  rw [EuclideanLaplacian.laplacian_congr_nhds hkernel]
  rfl

end MeasureTheory
