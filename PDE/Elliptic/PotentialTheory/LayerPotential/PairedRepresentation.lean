/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.LayerPotential.ZeroTraceRepresentation
public import PDE.Elliptic.PotentialTheory.LayerPotential.Regularity

/-!
# Paired gradients of a zero-trace Poisson field

The whole-space representation agrees with the retained continuous field
inside the domain and vanishes outside its closure. Differentiating these
open-set identities subtracts the exterior single-layer gradient from the
interior one. The remaining whole-space C² term has continuous gradient.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open Filter MeasureTheory Set SobolevSpace SobolevSpace.Trace.C1
open GraphSpace GraphSpace.ZeroTrace
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Gradient Sobolev Topology

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The gradient of the continuous zero-trace Poisson field is the
paired surface-gradient integral plus the difference of a C² remainder's
gradients, at an interior and an exterior point. -/
theorem exists_paired_gradient_representation_zeroTrace
    (hm : 1 ≤ m) (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i t)) = -inner ℝ f (baseCoordCLM t))
    (q : BoundaryL2 (Ω := Ω))
    (hq : ∀ z : HilbertTraceSpace (Ω := Ω),
      weakNormalTrace (w : H¹(Ω)) f huf z =
        ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω)
    {F : ℝ^(m + 1) → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ω)
    (hfF : (f : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] F)
    {v : ℝ^(m + 1) → ℝ} (hv : ContinuousOn v Ω)
    (hwv : baseRepresentative (w : H¹(Ω)) =ᵐ[domainMeasure (m + 1) Ω] v) :
    ∃ R : ℝ^(m + 1) → ℝ, ContDiff ℝ 2 R ∧
      EqOn (fun x ↦ singleLayerPotential q x + R x) v Ω ∧
      EqOn (fun x ↦ singleLayerPotential q x + R x) 0 (closure Ω)ᶜ ∧
      ∀ a ∈ Ω, ∀ b ∉ closure Ω,
        gradient v a =
          (∫ y, q y • (gradient (fundamentalSolution (m + 1)) (a - y) -
            gradient (fundamentalSolution (m + 1)) (b - y)) ∂surfaceMeasure Ω) +
            gradient R a - gradient R b := by
  obtain ⟨R, hR, hWR⟩ :=
    exists_contDiff_remainder_singleLayer_zeroExtendH10 hm w f huf q hq hF hFc hFs hfF
  have hzero : baseRepresentative (zeroExtendH10 H.isOpen.measurableSet w) =ᵐ[volume]
      Ω.indicator (baseRepresentative (w : H¹(Ω))) :=
    zeroExtendH10_coordinate_apply_ae H.isOpen.measurableSet w (baseIndex (m + 1) 1)
  have hΩs : Ω ⊆ (frontier Ω)ᶜ := fun x hx ↦
    (mem_interior_iff_notMem_frontier hx).mp (by rwa [H.isOpen.interior_eq])
  have houts : (closure Ω)ᶜ ⊆ (frontier Ω)ᶜ :=
    fun _ hx hy ↦ hx (frontier_subset_closure hy)
  have hcont : ContinuousOn (fun x ↦ singleLayerPotential q x + R x) (frontier Ω)ᶜ :=
    (contDiffOn_singleLayerPotential q).continuousOn.add hR.continuous.continuousOn
  have hin : EqOn (fun x ↦ singleLayerPotential q x + R x) v Ω := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ H.isOpen (hcont.mono hΩs) hv
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_of_ae hWR, hwv,
      ae_restrict_mem (μ := volume) H.isOpen.measurableSet] with x hzero hWR hwv hx
    rw [indicator_of_mem hx] at hzero
    exact hWR.symm.trans (hzero.trans hwv)
  have hout : EqOn (fun x ↦ singleLayerPotential q x + R x) 0 (closure Ω)ᶜ := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isClosed_closure.isOpen_compl
      (hcont.mono houts) continuousOn_const
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_of_ae hWR,
      ae_restrict_mem (μ := volume) isClosed_closure.measurableSet.compl] with x hzero hWR hx
    rw [indicator_of_notMem (fun hxΩ ↦ hx (subset_closure hxΩ))] at hzero
    exact hWR.symm.trans hzero
  have hgrad (z : ℝ^(m + 1)) (hz : z ∉ frontier Ω) :
      gradient (fun x ↦ singleLayerPotential q x + R x) z =
        (∫ y, q y • gradient (fundamentalSolution (m + 1)) (z - y) ∂surfaceMeasure Ω) +
          gradient R z := by
    have hS := hasGradientAt_singleLayerPotential q hz
    change (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm
      (fderiv ℝ (fun x ↦ singleLayerPotential q x + R x) z) = _
    rw [fderiv_fun_add hS.differentiableAt
      ((hR.differentiable (by norm_num)).differentiableAt), map_add]
    exact congrArg (fun g ↦ g + gradient R z) hS.gradient
  refine ⟨R, hR, hin, hout, fun a ha b hb ↦ ?_⟩
  have ha' := hΩs ha
  have hb' := houts hb
  have hga : gradient v a =
      (∫ y, q y • gradient (fundamentalSolution (m + 1)) (a - y) ∂surfaceMeasure Ω) +
        gradient R a := by
    rw [(eventuallyEq_of_mem (H.isOpen.mem_nhds ha) fun x hx ↦ (hin hx).symm).gradient_eq,
      hgrad a ha']
  have hgb :
      (∫ y, q y • gradient (fundamentalSolution (m + 1)) (b - y) ∂surfaceMeasure Ω) +
        gradient R b = 0 := by
    have heq : (fun x ↦ singleLayerPotential q x + R x) =ᶠ[𝓝 b] fun _ ↦ (0 : ℝ) :=
      eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hb) hout
    simpa only [hgrad b hb', gradient_fun_const] using heq.gradient_eq
  have hint :
      (∫ y, q y • (gradient (fundamentalSolution (m + 1)) (a - y) -
        gradient (fundamentalSolution (m + 1)) (b - y)) ∂surfaceMeasure Ω) =
      (∫ y, q y • gradient (fundamentalSolution (m + 1)) (a - y) ∂surfaceMeasure Ω) -
        ∫ y, q y • gradient (fundamentalSolution (m + 1)) (b - y) ∂surfaceMeasure Ω := by
    simp_rw [smul_sub]
    exact integral_sub (integrable_smul_gradient_fundamentalSolution_sub q ha')
      (integrable_smul_gradient_fundamentalSolution_sub q hb')
  rw [hga, hint, eq_neg_of_add_eq_zero_left hgb]
  abel

end PotentialTheory
