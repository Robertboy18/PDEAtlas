/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GreenIdentity
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.FDeriv.Laplacian.Congruence

/-!
# Green's identity away from a pole

If the classical weight vanishes near an interior pole, an annular smooth
representative of the fundamental solution gives the singular Green identity
directly. Its boundary derivative is the gradient near the boundary.
This localization uses the general C¹ graph-domain flux theorem.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Boundary.Flux SobolevSpace.Trace.C1 Geometry.SurfaceMeasure
open scoped Topology Gradient

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- The singular Green identity when its scalar weight vanishes near the pole.
Both the volume integral and the signed Hausdorff boundary integral are
integrable functions. -/
theorem integral_kernel_mul_laplacian_of_zero_near
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    {x : ℝ^(m + 1)} (hx : x ∈ Ω) (hzero : u =ᶠ[𝓝 x] fun _ ↦ 0) :
    let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
    IntegrableOn (fun y ↦ K y * laplacian u y) Ω ∧
      Integrable (fun y ↦ K y * normalFlux (Ω := Ω)
        (hu.of_le (show 1 ≤ 2 by omega)).completedGradient y -
        u y * normalFlux (Ω := Ω) (∇ K) y) (surfaceMeasure Ω) ∧
      (∫ y in Ω, K y * laplacian u y) =
        ∫ y, K y * normalFlux (Ω := Ω)
          (hu.of_le (show 1 ≤ 2 by omega)).completedGradient y -
          u y * normalFlux (Ω := Ω) (∇ K) y ∂surfaceMeasure Ω := by
  let K := fun y ↦ fundamentalSolution (m + 1) (y - x)
  let Du := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hΩ.isOpen.mem_nhds hx) hzero)
  have hballΩ : Metric.ball x r ⊆ Ω := fun y hy ↦ (hball hy).1
  have huzero : EqOn u (fun _ ↦ 0) (Metric.ball x r) := fun y hy ↦ (hball hy).2
  obtain ⟨M, hM, hbound⟩ := hΩ.bounded.isCompact_closure.isBounded.subset_ball_lt 0 x
  have hkernel : ContDiffOn ℝ 2 (fundamentalSolution (m + 1)) ({0}ᶜ) := by
    intro y hy
    exact ((contDiffAt_fundamentalSolution (m + 1) y hy).of_le (by simp)).contDiffWithinAt
  obtain ⟨A, hA, _, heqA⟩ :=
    hkernel.exists_contDiff_compactSupport_eqOn_annulus (half_pos hr) (by linarith : 0 < M + 1)
  let V := fun y ↦ A (y - x)
  have hV : ContDiff ℝ 2 V := hA.comp (contDiff_id.sub contDiff_const)
  have hVc : ContDiffUpToBoundary 2 V Ω :=
    ContDiffUpToBoundary.of_contDiff hV hΩ.bounded
  have hgerm {y : ℝ^(m + 1)} (hlo : r / 2 < ‖y - x‖)
      (hhi : ‖y - x‖ < M + 1) : V =ᶠ[𝓝 y] K := by
    have hopen : IsOpen {z : ℝ^(m + 1) | r / 2 < ‖z - x‖ ∧ ‖z - x‖ < M + 1} :=
      isOpen_Ioo.preimage ((continuous_id.sub continuous_const).norm)
    filter_upwards [hopen.mem_nhds ⟨hlo, hhi⟩] with z hz
    exact heqA (z - x) hz.1.le hz.2.le
  have hlapK {y : ℝ^(m + 1)} (hy : y ≠ x) : laplacian K y = 0 := by
    rw [PDE.laplacian_comp_sub_right _ x y
      ((contDiffAt_fundamentalSolution (m + 1) _ (sub_ne_zero.mpr hy)).of_le (by simp))]
    exact laplacian_fundamentalSolution_eq_zero (m + 1) _ (sub_ne_zero.mpr hy)
  have hupper {y : ℝ^(m + 1)} (hy : y ∈ closure Ω) : ‖y - x‖ < M + 1 :=
    (mem_ball_iff_norm.1 (hbound hy)).trans (lt_add_one M)
  have hlower {y : ℝ^(m + 1)} (hy : y ∈ frontier Ω) : r ≤ ‖y - x‖ := by
    by_contra! h
    have hyΩ := hballΩ (show y ∈ Metric.ball x r by simpa [Metric.mem_ball, dist_eq_norm])
    exact (mem_interior_iff_notMem_frontier hyΩ).mp
      (by simpa only [hΩ.isOpen.interior_eq] using hyΩ) hy
  have hboundary {y : ℝ^(m + 1)} (hy : y ∈ frontier Ω) :
      V y = K y ∧
      (hVc.of_le (show 1 ≤ 2 by omega)).completedGradient y = ∇ K y := by
    have hg := hgerm (lt_of_lt_of_le (half_lt_self hr) (hlower hy))
      (hupper (frontier_subset_closure hy))
    refine ⟨hg.eq_of_nhds, ?_⟩
    rw [(hVc.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient_extension
      hΩ.isOpen (hV.of_le (by norm_num)) (fun _ _ ↦ rfl) (frontier_subset_closure hy)]
    exact hg.gradient_eq
  have hvolume : EqOn (fun y ↦ u y * laplacian V y - V y * laplacian u y)
      (fun y ↦ -(K y * laplacian u y)) Ω := by
    intro y hy
    change u y * laplacian V y - V y * laplacian u y = -(K y * laplacian u y)
    by_cases hray : ‖y - x‖ < r
    · have hyb : y ∈ Metric.ball x r := by simpa [Metric.mem_ball, dist_eq_norm]
      have hg := huzero.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hyb)
      rw [huzero hyb, EuclideanLaplacian.laplacian_congr_nhds hg, PDE.laplacian_const]
      ring
    · have hg := hgerm (by linarith : r / 2 < ‖y - x‖)
        (hupper (subset_closure hy))
      have hyx : y ≠ x := by
        rintro rfl
        simp only [sub_self, norm_zero, not_lt] at hray
        linarith
      rw [EuclideanLaplacian.laplacian_congr_nhds hg, hlapK hyx, hg.eq_of_nhds]
      ring
  have hsurface : (fun y ↦ u y *
      normalFlux (Ω := Ω) (hVc.of_le (show 1 ≤ 2 by omega)).completedGradient y -
        V y * normalFlux (Ω := Ω) Du y) =ᵐ[surfaceMeasure Ω]
      fun y ↦ -(K y * normalFlux (Ω := Ω) Du y -
        u y * normalFlux (Ω := Ω) (∇ K) y) := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    rw [normalFlux_eq_inner _ hy, normalFlux_eq_inner _ hy, normalFlux_eq_inner _ hy,
      (hboundary hy).1, (hboundary hy).2]
    ring
  obtain ⟨hvi, hbi, heq⟩ :=
    green_second_identity_of_contDiffUpToBoundary hgraph hu hc hVc hV.continuous.continuousOn
  have hvneg : IntegrableOn (fun y ↦ -(K y * laplacian u y)) Ω :=
    hvi.congr_fun hvolume hΩ.isOpen.measurableSet
  have hbneg : Integrable (fun y ↦ -(K y * normalFlux (Ω := Ω) Du y -
      u y * normalFlux (Ω := Ω) (∇ K) y)) (surfaceMeasure Ω) :=
    hbi.congr hsurface
  refine ⟨integrable_neg_iff.mp hvneg, integrable_neg_iff.mp hbneg, ?_⟩
  rw [setIntegral_congr_fun hΩ.isOpen.measurableSet (fun y hy ↦ hvolume hy),
    integral_congr_ae hsurface, integral_neg, integral_neg] at heq
  exact neg_injective heq

end PotentialTheory.GreenFunction.Domain
