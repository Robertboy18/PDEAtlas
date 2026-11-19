/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry

/-!
# Single-layer potentials of surface L² densities

The canonical Laplace kernel integrated against a surface density gives a
locally integrable field. Its distributional Laplacian is the negative
surface source. Compactness of the boundary lets each compact test region
use an integrable truncation of the kernel.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open MeasureTheory Set TopologicalSpace SobolevSpace SobolevSpace.Trace.C1
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Distributions ENNReal Laplacian Pointwise

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The single-layer potential formed from the canonical fundamental solution
and a surface L² density. -/
def singleLayerPotential (q : BoundaryL2 (Ω := Ω)) (x : ℝ^(m + 1)) : ℝ :=
  ∫ y, fundamentalSolution (m + 1) (x - y) * q y ∂surfaceMeasure Ω

private theorem exists_integrable_kernel_eq_on_compact
    {K : Set ℝ^(m + 1)} (hK : IsCompact K) :
    ∃ k : ℝ^(m + 1) → ℝ, Integrable k volume ∧
      ∀ x ∈ K, ∀ y ∈ frontier Ω, k (x - y) = fundamentalSolution (m + 1) (x - y) := by
  let : Fact (0 < m + 1) := ⟨by omega⟩
  have hfrontier : IsCompact (frontier Ω) :=
    H.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcompact : IsCompact (K - frontier Ω) := by
    rw [← sub_image_prod]
    exact (hK.prod hfrontier).image continuous_sub
  refine ⟨(K - frontier Ω).indicator (fundamentalSolution (m + 1)), ?_, ?_⟩
  · exact ((locallyIntegrable_fundamentalSolution (m + 1)).integrableOn_isCompact
      hcompact).integrable_indicator hcompact.measurableSet
  · intro x hx y hy
    exact indicator_of_mem (sub_mem_sub hx hy) _

/-- The single-layer field is locally integrable across the boundary,
including the singular support of its source. -/
theorem locallyIntegrable_singleLayerPotential (q : BoundaryL2 (Ω := Ω)) :
    LocallyIntegrable (singleLayerPotential q) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨k, hk, heq⟩ := exists_integrable_kernel_eq_on_compact (Ω := Ω) hK
  have hq : Integrable (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) :=
    (Lp.memLp q).integrable (by norm_num)
  have hprod : Integrable (fun p : ℝ^(m + 1) × ℝ^(m + 1) ↦ q p.2 * k (p.1 - p.2))
      (volume.prod (surfaceMeasure Ω)) :=
    hq.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
  apply hprod.integral_prod_left.integrableOn.congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m)
    isClosed_frontier.measurableSet] with y hy
  rw [heq x hx y hy, mul_comm]

private theorem integrable_singleLayerKernel_mul_test
    (q : BoundaryL2 (Ω := Ω)) {ψ : ℝ^(m + 1) → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p : ℝ^(m + 1) × ℝ^(m + 1) ↦
      ψ p.1 * (fundamentalSolution (m + 1) (p.1 - p.2) * q p.2))
      (volume.prod (surfaceMeasure Ω)) := by
  obtain ⟨k, hk, heq⟩ := exists_integrable_kernel_eq_on_compact (Ω := Ω) hc
  have hq : Integrable (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) :=
    (Lp.memLp q).integrable (by norm_num)
  have hprod : Integrable (fun p : ℝ^(m + 1) × ℝ^(m + 1) ↦ q p.2 * k (p.1 - p.2))
      (volume.prod (surfaceMeasure Ω)) :=
    hq.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  have hi : Integrable (fun p : ℝ^(m + 1) × ℝ^(m + 1) ↦
      ψ p.1 * (q p.2 * k (p.1 - p.2))) (volume.prod (surfaceMeasure Ω)) :=
    hprod.bdd_mul (hψ.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun p ↦ hC p.1)
  apply hi.congr
  have hboundary : ∀ᵐ y ∂surfaceMeasure Ω, y ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [Measure.quasiMeasurePreserving_snd.tendsto_ae hboundary] with p hp
  by_cases hx : p.1 ∈ tsupport ψ
  · rw [heq p.1 hx p.2 hp, mul_comm (q p.2)]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- Integrating the single-layer field against a test Laplacian recovers
the negative surface pairing with the same density. -/
theorem integral_singleLayerPotential_mul_laplacian
    (hm : 1 ≤ m) (q : BoundaryL2 (Ω := Ω))
    {φ : ℝ^(m + 1) → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, singleLayerPotential q x * PDE.laplacian φ x) =
      -(∫ y, φ y * q y ∂surfaceMeasure Ω) := by
  let ψ := PDE.laplacian φ
  let φ₂ : 𝓓^{2}((⊤ : Opens ℝ^(m + 1)), ℝ) := ⟨φ, hφ, hc, subset_univ _⟩
  have hψ : Continuous ψ := φ₂.continuous_laplacian_two
  have hψc : HasCompactSupport ψ := φ₂.hasCompactSupport_laplacian
  have hi := integrable_singleLayerKernel_mul_test q hψ hψc
  calc
    _ = ∫ x, ∫ y, ψ x * (fundamentalSolution (m + 1) (x - y) * q y)
        ∂surfaceMeasure Ω := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_const_mul]
      exact mul_comm _ _
    _ = ∫ y, ∫ x, ψ x * (fundamentalSolution (m + 1) (x - y) * q y)
        ∂volume ∂surfaceMeasure Ω := integral_integral_swap hi
    _ = ∫ y, -φ y * q y ∂surfaceMeasure Ω := by
      apply integral_congr_ae
      filter_upwards with y
      simp_rw [← mul_assoc, mul_comm (ψ _)]
      rw [integral_mul_const,
        integral_fundamentalSolution_sub_mul_laplacian (by omega) hφ hc y]
    _ = _ := by simp only [neg_mul, integral_neg]

/-- The Laplacian of the single-layer field is its negative surface
source, with the sign fixed by the canonical fundamental solution. -/
theorem laplacian_singleLayerPotential_eq_neg_surface
    (hm : 1 ≤ m) (q : BoundaryL2 (Ω := Ω)) :
    Δ (Distribution.ofFun ⊤ (singleLayerPotential q) volume ⊤) =
      -Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ := by
  ext φ
  change LineDeriv.laplacianCLM ℝ (ℝ^(m + 1))
      𝓓'((⊤ : Opens ℝ^(m + 1)), ℝ)
      (Distribution.ofFun ⊤ (singleLayerPotential q) volume ⊤) φ =
    -(Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ φ)
  rw [Distribution.laplacianCLM_apply_apply,
    Distribution.ofFun_apply ((locallyIntegrable_singleLayerPotential q).locallyIntegrableOn univ),
    Distribution.ofFun_apply
      ((Lp.memLp q).locallyIntegrable (by norm_num) |>.locallyIntegrableOn univ)]
  simp only [smul_eq_mul, TestFunction.laplacianCLM_apply_eq_laplacian]
  rw [show (fun x ↦ PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x * singleLayerPotential q x) =
    (fun x ↦ singleLayerPotential q x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x) from
      funext fun x ↦ mul_comm _ _]
  exact integral_singleLayerPotential_mul_laplacian hm q
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

end PotentialTheory
