/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.LayerPotential.SingleLayer
public import PDE.Spaces.Sobolev.Boundary.Flux.ZeroExtension
import PDE.Elliptic.Classical.Poisson.FundamentalSolution
import PDE.Elliptic.Regularity.Interior.Weyl

/-!
# A single-layer representation of a zero-trace Poisson field

For a smooth load supported inside the domain, the zero extension differs
from the single-layer potential of its weak normal density by a
whole-space C² function. Poisson inversion removes the volume source, and
Weyl's lemma supplies the harmonic remainder. No boundary gradient value
or limit is assumed.
-/

@[expose] public noncomputable section

namespace PotentialTheory

open MeasureTheory Set TopologicalSpace SobolevSpace SobolevSpace.Trace.C1
open GraphSpace GraphSpace.ZeroTrace
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped Distributions ENNReal Laplacian Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [H : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The zero extension of a zero-trace Poisson field is its
single-layer potential plus a globally C² remainder. The volume load is
represented by a compactly supported C² function inside the domain. -/
theorem exists_contDiff_remainder_singleLayer_zeroExtendH10
    (hm : 1 ≤ m) (w : H¹₀(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (huf : ∀ v : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) (w : H¹(Ω)))
        (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))
    (q : BoundaryL2 (Ω := Ω))
    (hq : ∀ z : HilbertTraceSpace (Ω := Ω),
      weakNormalTrace (w : H¹(Ω)) f huf z =
        ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω)
    {F : ℝ^(m + 1) → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ω)
    (hfF : (f : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] F) :
    ∃ R : ℝ^(m + 1) → ℝ, ContDiff ℝ 2 R ∧
      baseRepresentative (zeroExtendH10 H.isOpen.measurableSet w) =ᵐ[volume]
        (fun x ↦ singleLayerPotential q x + R x) := by
  let : Fact (0 < m + 1) := ⟨by omega⟩
  let W := zeroExtendH10 H.isOpen.measurableSet w
  let F₂ : 𝓓^{2}((⊤ : Opens ℝ^(m + 1)), ℝ) :=
    ⟨F, hF, hFc, subset_univ _⟩
  let N := PoissonEquation.fundamentalSolutionConvolution (m + 1) F₂
  have hN : ContDiff ℝ 2 N :=
    PoissonEquation.contDiff_two_fundamentalSolutionConvolution (m + 1) F₂
  have hΔN (x : ℝ^(m + 1)) : PDE.laplacian N x = -F x := by
    have h : -PDE.laplacian N x = F x :=
      PoissonEquation.negative_laplacian_fundamentalSolutionConvolution (by omega) F₂ x
    linarith
  have hW : LocallyIntegrable (baseRepresentative W) volume :=
    locallyIntegrableOn_univ.mp (W.property (baseIndex (m + 1) 1)).locallyIntegrable_f
  have hS := locallyIntegrable_singleLayerPotential q
  have hNi := hN.continuous.locallyIntegrable (μ := volume)
  let u : ℝ^(m + 1) → ℝ := fun x ↦
    baseRepresentative W x - singleLayerPotential q x + N x
  have hu : LocallyIntegrable u volume := (hW.sub hS).add hNi
  have hweak : ∀ φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ),
      (∫ x, u x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x) = 0 := by
    intro φ
    have hWφ : (∫ x, baseRepresentative W x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x) =
        (∫ x, φ x * f x ∂domainMeasure (m + 1) Ω) -
          ∫ y, φ y * q y ∂surfaceMeasure Ω := by
      have heq := congrArg (fun T : 𝓓'((⊤ : Opens ℝ^(m + 1)), ℝ) ↦ T φ)
        (laplacian_zeroExtendH10_eq_volume_sub_surface w f huf q hq)
      change LineDeriv.laplacianCLM ℝ (ℝ^(m + 1))
          𝓓'((⊤ : Opens ℝ^(m + 1)), ℝ)
          (Distribution.ofFun ⊤ (baseRepresentative W) volume ⊤) φ =
        Distribution.ofFun ⊤ (f : ℝ^(m + 1) → ℝ) (domainMeasure (m + 1) Ω) ⊤ φ -
          Distribution.ofFun ⊤ (q : ℝ^(m + 1) → ℝ) (surfaceMeasure Ω) ⊤ φ at heq
      rw [Distribution.laplacianCLM_apply_apply,
        Distribution.ofFun_apply (hW.locallyIntegrableOn univ),
        Distribution.ofFun_apply
          ((Lp.memLp f).locallyIntegrable (by norm_num) |>.locallyIntegrableOn univ),
        Distribution.ofFun_apply
          ((Lp.memLp q).locallyIntegrable (by norm_num) |>.locallyIntegrableOn univ)] at heq
      simp only [smul_eq_mul, TestFunction.laplacianCLM_apply_eq_laplacian] at heq
      exact (integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)).trans heq
    have hload : (∫ x, φ x * f x ∂domainMeasure (m + 1) Ω) = ∫ x, φ x * F x :=
      (integral_congr_ae (hfF.mono fun x hx ↦ congrArg (φ x * ·) hx)).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hFs hs)), mul_zero])
    have hSφ := integral_singleLayerPotential_mul_laplacian hm q
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    have hNφ : (∫ x, N x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x) = -(∫ x, φ x * F x) := by
      rw [integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _),
        ← PDE.DistributionTheory.integral_mul_laplacian_eq N (φ.contDiff.of_le (by simp)) hN
          φ.hasCompactSupport]
      simp only [hΔN, mul_neg, integral_neg]
    have hint {g : ℝ^(m + 1) → ℝ} (hg : LocallyIntegrable g volume) :
        Integrable fun x ↦ g x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x :=
      hg.integrable_smul_right_of_hasCompactSupport φ.contDiff_laplacian.continuous
        φ.hasCompactSupport_laplacian
    have hWSi : Integrable (fun x ↦
        baseRepresentative W x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x -
          singleLayerPotential q x * PDE.laplacian (φ : ℝ^(m + 1) → ℝ) x) :=
      ((hint hW).sub (hint hS)).congr (ae_of_all _ fun x ↦ Pi.sub_apply _ _ x)
    simp only [u, add_mul, sub_mul]
    rw [integral_add hWSi (hint hNi), integral_sub (hint hW) (hint hS), hWφ, hload, hSφ, hNφ]
    ring
  obtain ⟨h, hh, huh⟩ :=
    LaplacianEquation.exists_isHarmonicPDE_ae_eq_of_integral_laplacian_eq_zero
      (hu.locallyIntegrableOn univ) hweak
  have hhc : ContDiff ℝ 2 h := contDiffOn_univ.mp hh.contDiffOn
  refine ⟨fun x ↦ h x - N x, hhc.sub hN, ?_⟩
  filter_upwards [show u =ᵐ[volume] h by simpa using huh] with x hx
  dsimp only [u] at hx ⊢
  linarith

end PotentialTheory
