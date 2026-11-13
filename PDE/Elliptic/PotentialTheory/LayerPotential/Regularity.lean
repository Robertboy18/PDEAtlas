/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.LayerPotential.SingleLayer
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Analysis.Calculus.LocalExtension
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of the single-layer potential

Away from the compact boundary, an annular cutoff replaces the fundamental
solution by a smooth compact kernel with the same local values and
derivatives. Mathlib's convolution regularity and dominated differentiation
then apply to the surface measure and its L² density.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Convolution ENNReal Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

private theorem exists_compact_kernel_germ {x : ℝ^(m + 1)} (hx : x ∉ frontier Ω) :
    ∃ G : ℝ^(m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧
      ∀ᶠ z in 𝓝 x, ∀ y ∈ frontier Ω,
        G =ᶠ[𝓝 (z - y)] fundamentalSolution (m + 1) := by
  let : Fact (0 < m + 1) := ⟨by omega⟩
  obtain ⟨r, hr, hball⟩ := isOpen_iff.mp isClosed_frontier.isOpen_compl x hx
  have hc : IsCompact (frontier Ω) :=
    H.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (continuous_const.sub continuous_id : Continuous (fun y : ℝ^(m + 1) ↦ x - y)).continuousOn
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (fundamentalSolution (m + 1)) {0}ᶜ := by
    intro z hz
    exact (contDiffAt_fundamentalSolution (m + 1) z (by simpa using hz)).contDiffWithinAt
  obtain ⟨G, hG, hGc, heq⟩ := hΦ.exists_contDiff_compactSupport_eqOn_annulus
    (by positivity : 0 < r / 4) (by positivity : 0 < |C| + r + 1)
  refine ⟨G, hG, hGc, ?_⟩
  filter_upwards [ball_mem_nhds x (half_pos hr)] with z hz y hy
  have hfar : r ≤ dist x y := by
    by_contra! hnear
    exact hball (by simpa only [mem_ball, dist_comm] using hnear) hy
  have hz' : dist x z < r / 2 := by simpa only [mem_ball, dist_comm] using hz
  have hlo : r / 4 < ‖z - y‖ := by
    have htri := dist_triangle x z y
    rw [dist_eq_norm z y] at htri
    linarith
  have hhi : ‖z - y‖ < |C| + r + 1 := by
    have htri := dist_triangle z x y
    have hbound : dist x y ≤ |C| := by
      simpa only [dist_eq_norm, Pi.sub_apply] using (hC y hy).trans (le_abs_self C)
    rw [dist_eq_norm z y] at htri
    have hz'' : dist z x < r / 2 := hz
    linarith
  filter_upwards [(isOpen_Ioo.preimage continuous_norm).mem_nhds ⟨hlo, hhi⟩] with v hv
  exact heq v hv.1.le hv.2.le

/-- A surface single-layer potential is smooth on both sides of the boundary. -/
theorem contDiffOn_singleLayerPotential (q : BoundaryL2 (Ω := Ω)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (singleLayerPotential q) (frontier Ω)ᶜ := by
  intro x hx
  obtain ⟨G, hG, hGc, heq⟩ := exists_compact_kernel_germ (Ω := Ω) hx
  have hq := (Lp.memLp q).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc := hGc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hq hG
  have hlocal : (fun z ↦ convolution (q : ℝ^(m + 1) → ℝ) G
      (ContinuousLinearMap.mul ℝ ℝ) (surfaceMeasure Ω) z) =ᶠ[𝓝 x]
      singleLayerPotential q := by
    filter_upwards [heq] with z hz
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
      isClosed_frontier.measurableSet] with y hy
    change q y * G (z - y) = fundamentalSolution (m + 1) (z - y) * q y
    rw [(hz y hy).eq_of_nhds, mul_comm]
  exact (hc.contDiffAt.congr_of_eventuallyEq hlocal.symm).contDiffWithinAt

private theorem integral_compact_kernel_hasFDerivAt
    (q : BoundaryL2 (Ω := Ω)) {G : ℝ^(m + 1) → ℝ}
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (x : ℝ^(m + 1)) :
    Integrable (fun y ↦ q y • fderiv ℝ G (x - y)) (surfaceMeasure Ω) ∧
      HasFDerivAt (fun z ↦ ∫ y, q y * G (z - y) ∂surfaceMeasure Ω)
        (∫ y, q y • fderiv ℝ G (x - y) ∂surfaceMeasure Ω) x := by
  have hq : Integrable (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) :=
    (Lp.memLp q).integrable (by norm_num)
  have hD := hG.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (hGc.fderiv ℝ).exists_bound_of_continuous hD
  have hmeas (z : ℝ^(m + 1)) : AEStronglyMeasurable
      (fun y ↦ fderiv ℝ G (z - y)) (surfaceMeasure Ω) :=
    (hD.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  refine ⟨hq.smul_bdd C (hmeas x) (ae_of_all _ fun y ↦ hC (x - y)), ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun z y ↦ q y • fderiv ℝ G (z - y))
    (bound := fun y ↦ ‖q y‖ * C) (Filter.univ_mem)
  · exact Filter.Eventually.of_forall fun z ↦ hq.aestronglyMeasurable.mul
      (hG.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · obtain ⟨B, hB⟩ := hGc.exists_bound_of_continuous hG.continuous
    exact hq.mul_bdd
      (hG.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y ↦ hB (x - y))
  · exact hq.aestronglyMeasurable.smul (hmeas x)
  · exact ae_of_all _ fun y z _ ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC (z - y)) (norm_nonneg _)
  · exact hq.norm.mul_const C
  · exact ae_of_all _ fun y z _ ↦ by
      have hd := ((hG.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const y)).const_mul (q y)
      simpa using hd

private theorem integrable_hasFDerivAt_singleLayerPotential
    (q : BoundaryL2 (Ω := Ω)) {x : ℝ^(m + 1)} (hx : x ∉ frontier Ω) :
    Integrable (fun y ↦ q y • fderiv ℝ (fundamentalSolution (m + 1)) (x - y))
        (surfaceMeasure Ω) ∧
      HasFDerivAt (singleLayerPotential q)
        (∫ y, q y • fderiv ℝ (fundamentalSolution (m + 1)) (x - y)
          ∂surfaceMeasure Ω) x := by
  obtain ⟨G, hG, hGc, heq⟩ := exists_compact_kernel_germ (Ω := Ω) hx
  have hi := integral_compact_kernel_hasFDerivAt q (hG.of_le (by simp)) hGc x
  have hderiv : (fun y ↦ q y • fderiv ℝ G (x - y)) =ᵐ[surfaceMeasure Ω]
      (fun y ↦ q y • fderiv ℝ (fundamentalSolution (m + 1)) (x - y)) := by
    filter_upwards [ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
      isClosed_frontier.measurableSet] with y hy
    rw [(heq.self_of_nhds y hy).fderiv_eq]
  refine ⟨hi.1.congr hderiv, ?_⟩
  rw [← integral_congr_ae hderiv]
  apply (show (fun z ↦ ∫ y, q y * G (z - y) ∂surfaceMeasure Ω) =ᶠ[𝓝 x]
      singleLayerPotential q from ?_).hasFDerivAt_iff.mp hi.2
  filter_upwards [heq] with z hz
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
    isClosed_frontier.measurableSet] with y hy
  rw [(hz y hy).eq_of_nhds, mul_comm]

/-- The gradient kernel is integrable against the surface density
at every point away from the boundary. -/
theorem integrable_smul_gradient_fundamentalSolution_sub
    (q : BoundaryL2 (Ω := Ω)) {x : ℝ^(m + 1)} (hx : x ∉ frontier Ω) :
    Integrable (fun y ↦ q y • gradient (fundamentalSolution (m + 1)) (x - y))
      (surfaceMeasure Ω) := by
  have hi := (integrable_hasFDerivAt_singleLayerPotential q hx).1
  have hmap := (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.integrable_comp_iff.mpr hi
  simpa only [Function.comp_def, map_smul, gradient] using hmap

/-- Differentiation under the surface integral gives the gradient
of the single-layer potential away from the boundary. -/
theorem hasGradientAt_singleLayerPotential
    (q : BoundaryL2 (Ω := Ω)) {x : ℝ^(m + 1)} (hx : x ∉ frontier Ω) :
    HasGradientAt (singleLayerPotential q)
      (∫ y, q y • gradient (fundamentalSolution (m + 1)) (x - y) ∂surfaceMeasure Ω) x := by
  have hd := (integrable_hasFDerivAt_singleLayerPotential q hx).2.hasGradientAt
  have hcomm :=
    (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := surfaceMeasure Ω)
      (fun y ↦ q y • fderiv ℝ (fundamentalSolution (m + 1)) (x - y))
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul] at hcomm
  simpa only [← hcomm, gradient] using hd

end PotentialTheory
