/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.LayerPotential.PairedRepresentation
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.PoissonLoad
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.WeakRepresentation
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Approach

/-!
# Paired surface gradients of the Green kernel

Regularize the pole and retain the resulting zero-trace field and its explicit
Poisson load. Its outward weak normal density supplies the single-layer term.
Near the boundary this field is the negative of the Green kernel. Subtracting
its exterior gradient therefore expresses the inward Green gradient by a
paired surface integral and the gradient difference of a C² remainder.
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Gradient Sobolev Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : C1ExtensionAtlas (m + 1) Ω]

/-- One surface density and one C² remainder give the paired-gradient identity
for the Green kernel along every sufficiently short inward normal ray.
Neither a boundary gradient nor a jump limit is assumed. -/
theorem exists_paired_gradient_greenKernel_of_corrector
    (hm : 1 ≤ m) (hgraph : HasC1GraphBoundary Ω)
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hrep : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hcφ : ContinuousOn φ (closure Ω))
    (hbφ : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hweak : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) U)
        (derivCoordCLM i t)) = 0) :
    ∃ q : BoundaryL2 (Ω := Ω), ∃ R : ℝ^(m + 1) → ℝ, ContDiff ℝ 2 R ∧
      (∀ (u : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        Integrable (fun y ↦ q y * u y) (surfaceMeasure Ω) ∧
        IntegrableOn (fun y ↦ greenKernel x φ y * PDE.laplacian u y) Ω ∧
        u x = (∫ y, q y * u y ∂surfaceMeasure Ω) -
          ∫ y in Ω, greenKernel x φ y * PDE.laplacian u y) ∧
      ∀ y : frontier Ω, ∀ᶠ t : ℝ in 𝓝[>] 0,
        DifferentiableAt ℝ (greenKernel x φ)
          ((y : ℝ^(m + 1)) - t • outwardUnitNormal y) ∧
        gradient (greenKernel x φ) ((y : ℝ^(m + 1)) - t • outwardUnitNormal y) =
          -((∫ z, q z •
              (gradient (fundamentalSolution (m + 1))
                  ((y : ℝ^(m + 1)) - t • outwardUnitNormal y - z) -
                gradient (fundamentalSolution (m + 1))
                  ((y : ℝ^(m + 1)) + t • outwardUnitNormal y - z))
                ∂surfaceMeasure Ω) +
            gradient R ((y : ℝ^(m + 1)) - t • outwardUnitNormal y) -
            gradient R ((y : ℝ^(m + 1)) + t • outwardUnitNormal y)) := by
  let : Fact (0 < m + 1) := ⟨by omega⟩
  obtain ⟨P⟩ := SobolevSpace.Approximation.UpToBoundary.exists_inwardPartition
    H.isOpen H.bounded (hasC1Boundary_of_local_graph hgraph)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp H.isOpen x hx
  obtain ⟨A, hA, hAc, w, hw, hwrep, hreg⟩ :=
    exists_regularized_corrector P H.bounded hr hball U hcφ hrep hbφ
  have hboundary (y : frontier Ω) :
      A =ᶠ[𝓝 (y : ℝ^(m + 1))] fun z ↦ fundamentalSolution (m + 1) (z - x) := by
    apply hreg y (frontier_subset_closure y.property)
    by_contra! hnear
    have hyΩ : (y : ℝ^(m + 1)) ∈ Ω :=
      hball (by simpa only [mem_ball, dist_eq_norm] using hnear)
    exact (mem_interior_iff_notMem_frontier hyΩ).mp
      (by simpa only [H.isOpen.interior_eq] using hyΩ) y.property
  obtain ⟨hF, hFc, hFs, f, hfF, huf⟩ :=
    exists_interior_load_of_regularized_corrector H.isOpen H.bounded hx
      U A hA hAc w hw hweak (fun y hy ↦ hboundary ⟨y, hy⟩)
  obtain ⟨q, hq⟩ := exists_surfaceDensity_weakNormalTrace_of_H10 hgraph w f huf
  have hformula := green_representation_of_regularized_corrector
    (by omega) hgraph hx U hrep hweak A hA hAc w hw
      (fun y hy ↦ hboundary ⟨y, hy⟩) f huf hfF
  obtain ⟨R, hR, hinside, _, hpair⟩ :=
    exists_paired_gradient_representation_zeroTrace hm w f huf q hq
      (hF.of_le (by norm_num)) hFc hFs hfF
      ((hcφ.mono subset_closure).sub hA.continuous.continuousOn) hwrep
  have hdiff (a : ℝ^(m + 1)) (ha : a ∈ Ω) :
      DifferentiableAt ℝ (fun z ↦ φ z - A z) a := by
    have ha' : a ∉ frontier Ω :=
      (mem_interior_iff_notMem_frontier ha).mp (by rwa [H.isOpen.interior_eq])
    have heq : (fun z ↦ φ z - A z) =ᶠ[𝓝 a]
        fun z ↦ singleLayerPotential q z + R z := by
      filter_upwards [H.isOpen.mem_nhds ha] with z hz
      exact (hinside hz).symm
    exact ((hasGradientAt_singleLayerPotential q ha').differentiableAt.add
      (hR.differentiable (by norm_num)).differentiableAt).congr_of_eventuallyEq heq
  refine ⟨q, R, hR, ?_, ?_⟩
  · intro u hu hcu
    let hu₁ := hu.of_le (show 1 ≤ 2 by omega)
    let V : H¹(Ω) := hu₁.toWkpSpaceOn H.isOpen H.bounded 2
    have htrace : (boundaryValue (traceClass V) : ℝ^(m + 1) → ℝ)
        =ᵐ[surfaceMeasure Ω] u := by
      change (trace V : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] u
      exact trace_eq_ae_of_continuousOn P V hcu
        (hu₁.toWkpSpaceOn_base_ae H.isOpen H.bounded 2)
    have hprod : (fun y ↦ q y * (boundaryValue (traceClass V)) y)
        =ᵐ[surfaceMeasure Ω] fun y ↦ q y * u y :=
      htrace.mono fun y hy ↦ congrArg (q y * ·) hy
    refine ⟨((Lp.memLp q).integrable_mul
      (Lp.memLp (boundaryValue (traceClass V)))).congr hprod, (hformula u hu hcu).1, ?_⟩
    exact (hformula u hu hcu).2.trans (by rw [hq, integral_congr_ae hprod])
  · intro y
    let ν := outwardUnitNormal (Ω := Ω) y
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hin : Tendsto (fun t : ℝ ↦ (y : ℝ^(m + 1)) - t • ν)
        (𝓝[>] 0) (𝓝 (y : ℝ^(m + 1))) := by
      simpa using (tendsto_const_nhds (x := (y : ℝ^(m + 1)))).sub (hid.smul_const ν)
    have heq : (fun z ↦ φ z - A z) =ᶠ[𝓝 (y : ℝ^(m + 1))]
        fun z ↦ -greenKernel x φ z := by
      filter_upwards [hboundary y] with z hz
      simp only [hz, greenKernel, neg_sub]
    have hgradient : ∀ᶠ z in 𝓝 (y : ℝ^(m + 1)),
        gradient (fun z ↦ φ z - A z) z = -gradient (greenKernel x φ) z := by
      filter_upwards [heq.gradient] with z hz
      simpa only [gradient, fderiv_fun_neg, map_neg] using hz
    filter_upwards [hin.eventually hgradient, eventually_normal_approach_mem y,
      hin.eventually heq.eventuallyEq_nhds] with t hgrad ht hlocal
    refine ⟨?_, ?_⟩
    · exact differentiableAt_fun_neg_iff.mp
        (hlocal.differentiableAt_iff.mp (hdiff _ ht.1))
    calc
      _ = -gradient (fun z ↦ φ z - A z) ((y : ℝ^(m + 1)) - t • ν) := by
        rw [hgrad, neg_neg]
      _ = _ := congrArg Neg.neg (hpair _ ht.1 _ ht.2)

end PotentialTheory.GreenFunction.Domain
