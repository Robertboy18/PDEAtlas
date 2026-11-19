/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.FundamentalSolutionConvolution
public import PDE.Elliptic.Classical.Poisson.Equation
import PDE.Analysis.Convolution.LocalRegularity
import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarDistribution
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Calculus

/-!
# Classical planar Poisson inversion

For every compactly supported `C²` datum `f` on `ℝ^2`, the convolution `Φ ⋆ f` with the
logarithmic fundamental solution is a classical solution of `-Δu = f`
(`fundamentalSolutionConvolution_two_isSolution`). The proof combines the planar pole identity
`Planar.integral_fundamentalSolution_mul_laplacian` with differentiation under convolution. This
is the case `n = 2` of Evans's §2.2.1, Theorem 1.

The local theorem `fundamentalSolution_convolution_local_poisson` requires `C²` regularity only
near the evaluation point, and local integrability with compact support elsewhere. It therefore
also applies to compact sources with jumps across a boundary: a cutoff splits off the part of the
source away from the point, which contributes a smooth harmonic potential there. Evans remarks
after the proof of Theorem 1 that the theorem holds under much weaker smoothness hypotheses on `f`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), Theorem 1 (Solving Poisson's equation) and its
  proof, pp. 23-25, and the remark on weaker smoothness hypotheses, p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace PoissonEquation

open MeasureTheory PotentialTheory TopologicalSpace
open Filter Set
open scoped Distributions Topology Convolution

/-- Translation of a compactly supported `C²` function, bundled again as a
test function. -/
private noncomputable def translatedTestFunction
    (f : 𝓓^{2}((⊤ : Opens (ℝ^2)), ℝ)) (x : ℝ^2) :
    𝓓^{2}((⊤ : Opens (ℝ^2)), ℝ) where
  toFun y := f (x + y)
  contDiff' := f.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' := by
    simpa [Function.comp_def] using
      f.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
  tsupport_subset' := Set.subset_univ _

@[simp]
private theorem translatedTestFunction_apply
    (f : 𝓓^{2}((⊤ : Opens (ℝ^2)), ℝ)) (x y : ℝ^2) :
    translatedTestFunction f x y = f (x + y) :=
  rfl

/-- Convolution of the planar fundamental solution with a compactly
supported `C²` datum satisfies the Poisson equation pointwise. -/
theorem negative_laplacian_fundamentalSolutionConvolution_two
    (f : 𝓓^{2}((⊤ : Opens (ℝ^2)), ℝ)) (x : ℝ^2) :
    -laplacian (fundamentalSolutionConvolution 2 f) x = f x := by
  let φ := translatedTestFunction f x
  have hφLaplacian (y : ℝ^2) :
      laplacian (φ : ℝ^2 → ℝ) y = laplacian f (x + y) := by
    change laplacian (fun z : ℝ^2 ↦ f (x + z)) y = laplacian f (x + y)
    exact PDE.laplacian_comp_add_left f x y f.contDiff.contDiffAt
  have hpole :=
    Planar.integral_fundamentalSolution_mul_laplacian φ
  have hconvolution :
      convolution (fundamentalSolution 2) (fun y ↦ laplacian f y)
          (ContinuousLinearMap.mul ℝ ℝ) volume x = -f x := by
    rw [MeasureTheory.convolution_mul]
    calc
      (∫ y : ℝ^2, fundamentalSolution 2 y * laplacian f (x - y)) =
          ∫ y : ℝ^2,
            fundamentalSolution 2 (-y) * laplacian f (x - (-y)) := by
        symm
        exact MeasureTheory.integral_neg_eq_self
          (fun y : ℝ^2 ↦
            fundamentalSolution 2 y * laplacian f (x - y)) volume
      _ = ∫ y : ℝ^2,
          fundamentalSolution 2 y * laplacian (φ : ℝ^2 → ℝ) y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          change fundamentalSolution 2 (-y) * laplacian f (x - (-y)) =
            fundamentalSolution 2 y * laplacian (φ : ℝ^2 → ℝ) y
          rw [fundamentalSolution_neg, sub_neg_eq_add, hφLaplacian]
      _ = -φ 0 := hpole
      _ = -f x := by simp [φ]
  rw [laplacian_fundamentalSolutionConvolution]
  linarith

/-- The planar fundamental-solution convolution is a classical `C²` solution of the
Poisson equation on all of `ℝ^2`. -/
theorem fundamentalSolutionConvolution_two_isSolution
    (f : 𝓓^{2}((⊤ : Opens (ℝ^2)), ℝ)) :
    ContDiff ℝ 2 (fundamentalSolutionConvolution 2 f) ∧
      ∀ x ∈ (poissonEquation 2 f).domain,
        (poissonEquation 2 f).residual
          (fundamentalSolutionConvolution 2 f) x = 0 := by
  refine ⟨contDiff_two_fundamentalSolutionConvolution 2 f, ?_⟩
  exact (poissonEquation_residual_zero_iff 2 f
      (fundamentalSolutionConvolution 2 f)).2
    (negative_laplacian_fundamentalSolutionConvolution_two f)

private theorem fundamentalSolution_convolution_away_support
    {f : ℝ^2 → ℝ} (hf : LocallyIntegrable f volume)
    (hc : HasCompactSupport f) {x : ℝ^2} (hx : x ∉ tsupport f) :
    ContDiffAt ℝ 2 (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x ∧
      laplacian (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x = 0 ∧
      Integrable (fun y ↦ fundamentalSolution 2 (x - y) * f y) := by
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport f).isOpen_compl.mem_nhds hx)
  obtain ⟨b, _, hbound⟩ := hc.isCompact.isBounded.subset_ball_lt 0 x
  let μ := volume.restrict (tsupport f)
  have hsource : ∀ᵐ y ∂μ, a ≤ dist x y ∧ dist x y ≤ b := by
    filter_upwards [ae_restrict_mem (isClosed_tsupport f).measurableSet] with y hy
    refine ⟨le_of_not_gt (fun h ↦ hball (by simpa [Metric.mem_ball, dist_comm] using h) hy), ?_⟩
    have hupper : dist y x < b := hbound hy
    exact (by simpa only [dist_comm] using hupper.le)
  have hK : ContDiffOn ℝ 2 (fundamentalSolution 2) ({0}ᶜ : Set (ℝ^2)) := by
    intro y hy
    exact ((contDiffAt_fundamentalSolution 2 y hy).of_le (by simp)).contDiffWithinAt
  have hμ : LocallyIntegrable f μ := hf.mono_measure Measure.restrict_le_self
  have hpotential : (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) =
      fun z ↦ ∫ y, f y * fundamentalSolution 2 (z - y) ∂μ := by
    funext z
    rw [convolution_mul_swap]
    symm
    calc
      (∫ y in tsupport f, f y * fundamentalSolution 2 (z - y)) =
          ∫ y, f y * fundamentalSolution 2 (z - y) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy ↦ by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
      _ = ∫ y, fundamentalSolution 2 (z - y) * f y := by simp_rw [mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpotential]
    simpa [smul_eq_mul] using
      contDiffAt_integral_smul_sub_of_annulus hK hμ ha hsource
  · rw [hpotential, laplacian_integral_mul_sub_of_annulus hK hμ ha hsource]
    apply integral_eq_zero_of_ae
    filter_upwards [hsource] with y hy
    have hxy : x - y ≠ 0 := by
      intro h
      have : dist x y = 0 := by rw [dist_eq_norm, h, norm_zero]
      linarith [hy.1]
    rw [laplacian_fundamentalSolution_eq_zero 2 _ hxy, mul_zero]
    rfl
  · have hcontinuous : ContinuousOn
        (fun y ↦ fundamentalSolution 2 (x - y)) (tsupport f) := by
      intro y hy
      have hxy : x - y ≠ 0 := sub_ne_zero.mpr (fun h ↦ hx (h ▸ hy))
      exact ((contDiffAt_fundamentalSolution 2 (x - y) hxy).continuousAt.comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
    have hsupport : Function.support (fun y ↦ fundamentalSolution 2 (x - y) * f y) ⊆
        tsupport f := by
      intro y hy
      by_contra hys
      exact hy (by simp only [image_eq_zero_of_notMem_tsupport hys, mul_zero])
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp
      (IntegrableOn.continuousOn_mul hcontinuous
        (hf.integrableOn_isCompact hc.isCompact) hc.isCompact)

/-- A compact, locally integrable planar source gives a classical Poisson potential
at each point where the source is `C²`. The source need not be smooth across a
boundary elsewhere; a cutoff isolates the singular part of the integral. -/
theorem fundamentalSolution_convolution_local_poisson
    {f : ℝ^2 → ℝ} (hf : LocallyIntegrable f volume)
    (hc : HasCompactSupport f) {x : ℝ^2} (hlocal : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x ∧
      -laplacian (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x = f x := by
  obtain ⟨g, hg, hgc, heq⟩ := hlocal.exists_contDiff_compactSupport_eventuallyEq
  let φ : TestFunction (⊤ : Opens (ℝ^2)) ℝ 2 :=
    { toFun := g
      contDiff' := hg
      hasCompactSupport' := hgc
      tsupport_subset' := subset_univ _ }
  let r := f - g
  have hr : LocallyIntegrable r volume := hf.sub hg.continuous.locallyIntegrable
  have hrc : HasCompactSupport r := hc.sub hgc
  have hrzero : r =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [heq] with y hy
    simp [r, hy]
  have hx : x ∉ tsupport r := notMem_tsupport_iff_eventuallyEq.mpr hrzero
  obtain ⟨hregular, hlap, _⟩ := fundamentalSolution_convolution_away_support hr hrc hx
  have hφ : ContDiff ℝ 2 (fundamentalSolutionConvolution 2 φ) :=
    contDiff_two_fundamentalSolutionConvolution 2 φ
  have hpotential : (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) =ᶠ[𝓝 x]
      fun z ↦ fundamentalSolutionConvolution 2 φ z +
        (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] r) z := by
    filter_upwards [(isClosed_tsupport r).isOpen_compl.mem_nhds hx] with z hz
    have hgint : Integrable (fun y ↦ fundamentalSolution 2 (z - y) * g y) := by
      simpa using (hgc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        (locallyIntegrable_fundamentalSolution 2) hg.continuous z).integrable_swap
    have hrint := (fundamentalSolution_convolution_away_support hr hrc hz).2.2
    change (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z =
      (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] g) z +
        (fundamentalSolution 2 ⋆[ContinuousLinearMap.mul ℝ ℝ] r) z
    simp only [convolution_mul_swap]
    rw [← integral_add hgint hrint]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [r]
    ring
  refine ⟨(hφ.contDiffAt.add hregular).congr_of_eventuallyEq hpotential, ?_⟩
  rw [EuclideanLaplacian.laplacian_congr_nhds hpotential,
    PDE.laplacian_add _ _ x hφ.contDiffAt hregular, hlap, add_zero,
    negative_laplacian_fundamentalSolutionConvolution_two]
  exact heq.eq_of_nhds.symm

end PoissonEquation
