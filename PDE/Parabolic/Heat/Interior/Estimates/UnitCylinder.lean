/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.KernelPairing
import PDE.Analysis.Convolution.WeightedBounds
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Uniform interior estimates on the unit heat cylinder

The cutoff representation is a finite sum of weighted smoothing convolutions.
The cutoffs and kernels depend only on the dimension; their derivative bounds
therefore give constants chosen before the field and its spatial domain.
The resulting smooth extension agrees with the field up to the top time.
-/

@[expose] public section

open PDE (laplacian)

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace HeatEquation

/-- Every local heat field has a smooth extension near the half cylinder
whose derivatives are bounded by its spacetime L1 norm on the unit cylinder.
The constant does not depend on the domain, the field or its jets. The
extension comes from the cutoff representation. -/
theorem exists_unit_extension_norm_iteratedFDeriv_le (n j : ℕ) :
    ∃ C > 0, ∀ (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Dt : ℝ^n × ℝ → ℝ),
      IsOpen Ω → closedBall 0 1 ⊆ Ω →
      ContinuousOn u.uncurry (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dx (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dxx (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dt (Ω ×ˢ Icc (-1) 0) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasDerivWithinAt (u p.1) (Dt p) (Icc (-1) 0) p.2) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) →
      ∃ v : ℝ^n × ℝ → ℝ, ContDiff ℝ ∞ v ∧
        (∀ (x : ℝ^n) (t : ℝ), ‖x‖ < 5 / 8 → -3 / 8 < t → t ≤ 0 →
          u x t = v (x, t)) ∧
        ∀ p, ‖iteratedFDeriv ℝ j v p‖ ≤
          C * ∫ q in closedBall (0 : ℝ^n) 1 ×ˢ Icc (-1 : ℝ) 0, ‖u q.1 q.2‖ := by
  let : (volume : Measure (ℝ^n × ℝ)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  obtain ⟨G, hG, hc, hmatch⟩ := exists_compact_heatKernel_on_unitCutoff n
  let χ := unitSpatialCutoff n
  let η := unitTimeCutoff
  let Q := tsupport χ ×ˢ Icc (-1 : ℝ) 0
  let a : Option (Fin n) → ℝ^n × ℝ → ℝ
    | none => fun q ↦ deriv η q.2 * χ q.1 + η q.2 * laplacian χ q.1
    | some i => fun q ↦ -2 * η q.2 * (∂[i] (χ : ℝ^n → ℝ)) q.1
  let K : Option (Fin n) → ℝ^n × ℝ → ℝ
    | none => G
    | some i => fun q ↦ fderiv ℝ G q (EuclideanSpace.single i 1, 0)
  have hQ : IsCompact Q := χ.hasCompactSupport.prod isCompact_Icc
  have hη : ContDiff ℝ 1 η := contDiff_unitTimeCutoff
  have ha (i : Option (Fin n)) : ContinuousOn (a i) Q := by
    have h1 := hη.continuous_deriv_one
    have h2 := hη.continuous
    have h3 := χ.continuous
    have h4 := (χ.contDiff (n := 2)).continuous_coordinate_laplacian
    rcases i with _ | i
    · exact Continuous.continuousOn (by dsimp only [a]; fun_prop)
    · have h5 : Continuous (∂[i] (χ : ℝ^n → ℝ)) :=
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (χ.contDiff (n := 2))).continuous
      exact Continuous.continuousOn (by dsimp only [a]; fun_prop)
  have hK (i : Option (Fin n)) : ContDiff ℝ ∞ (K i) := by
    rcases i with _ | i
    exacts [hG, (hG.fderiv_right (by simp)).clm_apply contDiff_const]
  have hKc (i : Option (Fin n)) : HasCompactSupport (K i) := by
    rcases i with _ | i
    exacts [hc, hc.fderiv_apply ℝ (EuclideanSpace.single i 1, 0)]
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_iteratedFDeriv_sum_weighted_convolution (μ := volume) hQ ha hK hKc j
  refine ⟨C, hC, fun Ω u Dx Dxx Dt hΩ hball hu hDx hDxx hDt hspace hhessian htime hheat ↦ ?_⟩
  have hχball : tsupport χ ⊆ closedBall 0 1 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall (by norm_num [χ, unitSpatialCutoff])
  have huQ : IntegrableOn u.uncurry Q :=
    (hu.mono (prod_mono_left (hχball.trans hball))).integrableOn_compact hQ
  let v : ℝ^n × ℝ → ℝ := fun p ↦ ∑ i, ∫ q in Q, (a i q * u q.1 q.2) * K i (p - q)
  obtain ⟨hv, hjet⟩ := hbound u.uncurry huQ
  refine ⟨v, hv, ?_, fun p ↦ (hjet p).trans ?_⟩
  · intro x t hx ht ht0
    simpa only [v, Fintype.sum_option, a, K] using
      unitCutoff_eq_weighted_kernel_integrals hG hmatch hΩ hball
        hu hDx hDxx hDt hspace hhessian htime hheat hx ht ht0
  · exact mul_le_mul_of_nonneg_left (setIntegral_mono_set
      ((hu.mono (prod_mono_left hball)).norm.integrableOn_compact
        ((isCompact_closedBall (0 : ℝ^n) 1).prod isCompact_Icc))
      (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Eventually.of_forall (prod_mono_left hχball))) hC.le

/-- The iterated derivatives within the original closed cylinder obey
the same L1 bound on its compact half cylinder, including the top time. -/
theorem exists_unit_norm_iteratedFDerivWithin_le (n j : ℕ) :
    ∃ C > 0, ∀ (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ)
      (Dt : ℝ^n × ℝ → ℝ),
      IsOpen Ω → closedBall 0 1 ⊆ Ω →
      ContinuousOn u.uncurry (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dx (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dxx (Ω ×ˢ Icc (-1) 0) →
      ContinuousOn Dt (Ω ×ˢ Icc (-1) 0) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        HasDerivWithinAt (u p.1) (Dt p) (Icc (-1) 0) p.2) →
      (∀ p ∈ Ω ×ˢ Icc (-1) 0,
        Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0) →
      ∀ p ∈ closedBall (0 : ℝ^n) (1 / 2) ×ˢ Icc (-1 / 4 : ℝ) 0,
        ‖iteratedFDerivWithin ℝ j u.uncurry (Ω ×ˢ Icc (-1) 0) p‖ ≤
          C * ∫ q in closedBall (0 : ℝ^n) 1 ×ˢ Icc (-1 : ℝ) 0, ‖u q.1 q.2‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_unit_extension_norm_iteratedFDeriv_le n j
  refine ⟨C, hC, fun Ω u Dx Dxx Dt hΩ hball hu hDx hDxx hDt
    hspace hhessian htime hheat p hp ↦ ?_⟩
  obtain ⟨v, hv, heq, hjet⟩ :=
    hbound Ω u Dx Dxx Dt hΩ hball hu hDx hDxx hDt hspace hhessian htime hheat
  have hx : ‖p.1‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hp.1
  have hpQ : p ∈ Ω ×ˢ Icc (-1) 0 :=
    ⟨hball ((closedBall_subset_closedBall (by norm_num)) hp.1), by linarith [hp.2.1],
      hp.2.2⟩
  have hnear : ball (0 : ℝ^n) (5 / 8) ×ˢ Ioi (-3 / 8 : ℝ) ∈ 𝓝 p :=
    (isOpen_ball.prod isOpen_Ioi).mem_nhds
      ⟨by simpa only [mem_ball, dist_zero_right] using (show ‖p.1‖ < 5 / 8 by linarith),
        by change -3 / 8 < p.2; linarith [hp.2.1]⟩
  have hgerm : u.uncurry =ᶠ[𝓝[Ω ×ˢ Icc (-1) 0] p] v := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with q hq hqQ
    exact heq q.1 q.2 (by simpa only [mem_ball, dist_zero_right] using hq.1)
      hq.2 hqQ.2.2
  rw [hgerm.iteratedFDerivWithin_eq
    (heq p.1 p.2 (by linarith) (by linarith [hp.2.1]) hp.2.2) j]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (hΩ.uniqueDiffOn.prod (uniqueDiffOn_Icc (by norm_num)))
    ((hv.of_le (by simp)).contDiffAt) hpQ]
  exact hjet p

end HeatEquation
