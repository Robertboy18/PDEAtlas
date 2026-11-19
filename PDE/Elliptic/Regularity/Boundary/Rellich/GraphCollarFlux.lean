/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.CutoffLimit
public import PDE.Elliptic.Regularity.Boundary.Rellich.GraphSurfaceEstimate
public import PDE.Elliptic.Regularity.Boundary.Rellich.StripEnergy
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero.Gradient

/-!
# Graph collar flux for localized weak Poisson states

The zero-extension gradient pairs with the same collar test as the
original domain gradient. The strip energy estimate and the computed collar
limit therefore give a physical surface bound for the weak Green pairing.
Only C¹ graph geometry and the distributional equation Δz=f are used.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Sobolev Gradient Topology

namespace SobolevSpace.GraphSpace.Rellich

open Approximation.UpToBoundary Boundary.Flux.Graph Boundary.Geometry.SurfaceMeasure
open Trace.HalfSpace ZeroTrace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}

/-- A continuously differentiable cutoff constant on a closed ray has zero
derivative on that ray, including its endpoint. -/
theorem deriv_eq_zero_on_ray {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    {a : ℝ} (hzero : ∀ s, a ≤ s → χ s = 0) {s : ℝ} (hs : a ≤ s) :
    deriv χ s = 0 := by
  have hclosed : IsClosed {s : ℝ | deriv χ s = 0} :=
    isClosed_eq hχ.continuous_deriv_one continuous_const
  have hsub : Ioi a ⊆ {s : ℝ | deriv χ s = 0} := by
    intro r hr
    have heq : χ =ᶠ[𝓝 r] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with q hq
      exact hzero q hq.le
    change deriv χ r = 0
    simpa only [deriv_const] using heq.deriv_eq
  exact (closure_minimal hsub hclosed) (by simpa only [closure_Ioi, mem_Ici] using hs)

/-- The positive-strip flux of the zero extension equals the domain flux.
The cutoff derivative vanishes once the rescaled height reaches one. -/
theorem integral_zeroExtend_graphStrip_eq
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω))
    {K : Set ℝ^(m + 1)} (hK : MeasurableSet K)
    {φ d : ℝ^(m + 1) → ℝ} {ψ : ℝ → ℝ}
    (hd : Measurable d) (hsupp : tsupport φ ⊆ K)
    (hpos : ∀ x ∈ Ω, x ∈ tsupport φ → 0 < d x)
    (hzero : ∀ s, 1 ≤ s → ψ s = 0) {t : ℝ} (ht : 0 < t) :
    (∫ x in K ∩ {x | d x ∈ Ioo 0 t},
      φ x * ψ (d x / t) * inner ℝ
        ((wkpGradientCLM (zeroExtendH10 hΩ z) : ℝ^(m + 1) → ℝ^(m + 1)) x) (∇ d x)) =
    ∫ x, φ x * ψ (d x / t) * inner ℝ
      ((wkpGradientCLM (z : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1)) x) (∇ d x)
        ∂domainMeasure (m + 1) Ω := by
  have hz : (wkpGradientCLM (zeroExtendH10 hΩ z) : ℝ^(m + 1) → ℝ^(m + 1))
      =ᵐ[volume] Ω.indicator
        (wkpGradientCLM (z : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1)) :=
    wkpGradientCLM_zeroExtendWkp0_ae hΩ z
  have hS : MeasurableSet (K ∩ {x | d x ∈ Ioo 0 t}) :=
    hK.inter (hd measurableSet_Ioo)
  simp only [domainMeasure]
  rw [← integral_indicator hS, ← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  by_cases hxΩ : x ∈ Ω
  · by_cases hφx : φ x = 0
    · simp [hxΩ, hφx]
    · have hxs : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hφx)
      have hxd : 0 < d x := hpos x hxΩ hxs
      by_cases hxt : d x < t
      · have hxS : x ∈ K ∩ {x | d x ∈ Ioo 0 t} := ⟨hsupp hxs, hxd, hxt⟩
        simp only [indicator_of_mem hxS, indicator_of_mem hxΩ]
        rw [hx, indicator_of_mem hxΩ]
      · have hψ : ψ (d x / t) = 0 := hzero _ ((le_div_iff₀ ht).mpr (by
          simpa only [one_mul] using le_of_not_gt hxt))
        simp [hxΩ, hψ]
  · simp [hxΩ, hx]

variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The localized weak Green pairing is bounded by its physical weighted surface
L² integral. The graph window and energy constant are independent of the test. -/
theorem greenPairing_sq_le_weighted_surfaceIntegral
    (P : InwardPartition Ω) (cover : Boundary.C1GraphBoundaryCover m Ω)
    (i : Fin cover.N) (z : H¹₀(Ω)) (u : ℝ^(m + 1) → ℝ)
    (hu : (baseCoordCLM z : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] u)
    (hpatch : tsupport (Ω.indicator u) ⊆ cover.boundaryPatch i)
    (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ v : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian v.1.toFun x
        ∂domainMeasure (m + 1) Ω) =
      ∫ x, (f : ℝ^(m + 1) → ℝ) x * v.1.toFun x ∂domainMeasure (m + 1) Ω)
    {K : Set ℝ^(m + 1)} (hK : IsCompact K) (hKP : K ⊆ cover.boundaryPatch i)
    {φ : ℝ^(m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ K)
    {χ : ℝ → ℝ} {C : ℝ} (hχ : ContDiff ℝ 1 χ) (hχ0 : χ 0 = 1)
    (hbound : ∀ s, ‖χ s‖ ≤ C) (hzero : ∀ s, 1 ≤ s → χ s = 0) :
    ((∫ x, (f : ℝ^(m + 1) → ℝ) x * φ x ∂domainMeasure (m + 1) Ω) +
      ∫ x, inner ℝ ((wkpGradientCLM (z : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1)) x)
        (∇ φ x) ∂domainMeasure (m + 1) Ω) ^ 2 ≤
    (2 * (m + 1 : ℕ) * ‖(cover.coordinates i).symm (0, 1)‖ * ‖f‖ * ‖z‖) *
      ((∫ s : ℝ in (0 : ℝ)..1, deriv χ s ^ 2) *
        ∫ x, φ x ^ 2 * ‖fderiv ℝ
          (fun y ↦ (cover.coordinates i y).2 - cover.height i (cover.coordinates i y).1) x‖
            ∂surfaceMeasure Ω) := by
  let A := (cover.coordinates i).trans tangentialNormalContinuousLinearEquiv.symm
  let g := cover.height i
  let d := linearGraphHeight A g
  have heqd : d = fun x ↦ (cover.coordinates i x).2 - g (cover.coordinates i x).1 := by
    funext x
    simp [d, linearGraphHeight, A, tangentialNormalContinuousLinearEquiv_symm_apply]
  have hside : ∀ x ∈ cover.boundaryPatch i, x ∈ Ω ↔ x ∈ linearEpigraph A g := fun x hx ↦ by
    simpa [linearEpigraph, A, g, tangentialNormalContinuousLinearEquiv_symm_apply] using
      cover.mem_iff_epigraph i x hx
  have hd : ContDiff ℝ 1 d := heqd ▸ (cover.coordinates i).contDiff.snd.sub
    ((cover.height_contDiff i).comp (cover.coordinates i).contDiff.fst)
  have hboundary : ∀ x ∈ frontier Ω, φ x ≠ 0 → d x = 0 := fun x hx hφx ↦
    (mem_frontier_iff_graphHeight_eq_zero (cover.boundaryPatch_open i) A g
      (cover.height_contDiff i).continuous hside
      (hKP (hsupp (subset_tsupport φ (Function.mem_support.mpr hφx))))).mp hx
  have hpos : ∀ x ∈ Ω, x ∈ tsupport φ → 0 < d x := fun x hx hs ↦ by
    rw [heqd]
    exact sub_pos.mpr ((cover.mem_iff_epigraph i x (hKP (hsupp hs))).mp hx)
  have hlim := tendsto_collar_flux P (z : H¹(Ω)) f hweak hφ hd hχ hχ0 hbound
    hzero hboundary hpos
  have hψzero : ∀ s, 1 ≤ s → deriv χ s = 0 := fun _ hs ↦ deriv_eq_zero_on_ray hχ hzero hs
  have hpair : Tendsto (fun t : ℝ ↦ t⁻¹ *
      ∫ x in K ∩ {x | d x ∈ Ioo 0 t}, φ x * deriv χ (d x / t) * inner ℝ
        ((wkpGradientCLM (zeroExtendH10 cover.isOpen.measurableSet z) :
          ℝ^(m + 1) → ℝ^(m + 1)) x) (∇ d x)) (𝓝[>] 0)
      (𝓝 ((∫ x, (f : ℝ^(m + 1) → ℝ) x * φ x ∂domainMeasure (m + 1) Ω) +
        ∫ x, inner ℝ ((wkpGradientCLM (z : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1)) x)
          (∇ φ x) ∂domainMeasure (m + 1) Ω)) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [integral_zeroExtend_graphStrip_eq cover.isOpen.measurableSet z hK.measurableSet
      hd.continuous.measurable hsupp hpos hψzero ht]
  obtain ⟨δ, hδ, he⟩ := exists_integral_gradient_sq_graph_strip_le cover i z u hu
    hpatch f hweak hK hKP
  have henergy : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∫ x in K ∩ {x | d x ∈ Ioo 0 t},
        ‖(wkpGradientCLM (zeroExtendH10 cover.isOpen.measurableSet z) :
          ℝ^(m + 1) → ℝ^(m + 1)) x‖ ^ 2) ≤
      t * (2 * (m + 1 : ℕ) * ‖(cover.coordinates i).symm (0, 1)‖ * ‖f‖ * ‖z‖) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with t ht htδ
    rw [heqd]
    exact (he t ⟨ht, htδ⟩).trans_eq (by ring)
  have hZ : MemLp (wkpGradientCLM (zeroExtendH10 cover.isOpen.measurableSet z) :
      ℝ^(m + 1) → ℝ^(m + 1)) 2 volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      Lp.memLp (wkpGradientCLM (zeroExtendH10 cover.isOpen.measurableSet z))
  have hestimate := sq_le_graphSurfaceIntegral_of_collar_energy A
    (cover.height_contDiff i) hK hφ.continuous hsupp hχ.continuous_deriv_one hZ henergy hpair
  have hsurface : (∫ x in frontier (linearEpigraph A g), φ x ^ 2 * ‖fderiv ℝ d x‖
      ∂Measure.euclideanHausdorffMeasure m) =
      ∫ x, φ x ^ 2 * ‖fderiv ℝ d x‖ ∂surfaceMeasure Ω := by
    simp only [surfaceMeasure, Nat.add_sub_cancel]
    rw [← integral_indicator isClosed_frontier.measurableSet,
      ← integral_indicator isClosed_frontier.measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    classical
    by_cases hx : x ∈ tsupport φ
    · simp only [Set.indicator_apply,
        (cover.boundaryPatch_open i).mem_frontier_iff_of_local_eq hside (hKP (hsupp hx))]
    · simp [Set.indicator_apply, image_eq_zero_of_notMem_tsupport hx]
  change _ ≤ _ * (_ * ∫ x in frontier (linearEpigraph A g), φ x ^ 2 * ‖fderiv ℝ d x‖
    ∂Measure.euclideanHausdorffMeasure m) at hestimate
  rwa [hsurface, heqd] at hestimate

end SobolevSpace.GraphSpace.Rellich
