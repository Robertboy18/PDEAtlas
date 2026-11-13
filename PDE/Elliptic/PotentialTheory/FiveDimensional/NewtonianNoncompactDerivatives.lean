/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactGradient
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Source derivatives of noncompact Newtonian potentials

A coordinate derivative moves onto a C¹ source when the Newtonian pairings of
the source and that derivative converge absolutely at one anchor. A compact
cutoff handles the pole. On its complement, the gradient formula of
`NewtonianNoncompactGradient` and
the two anchor pairings supply all three integrability inputs to global
integration by parts. No boundary-flux limit is assumed separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Distributions Topology


namespace PotentialTheory

private theorem fundamentalSolution_five_tail_source_derivative
    (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g) (X : ℝ^5) (i : Fin 5)
    (R : ℝ) (hR : 0 < R) (hzero : ∀ Y ∈ Metric.ball X R, g Y = 0)
    (hpot : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y))
    (hsource : Integrable (fun Y : ℝ^5 ↦
      fundamentalSolution 5 (X - Y) * (∂[i] g) Y))
    (hgrad : Integrable (fun Y : ℝ^5 ↦
      fiveDimensionalGammaGradientKernel i (X - Y) * g Y)) :
    (∫ Y : ℝ^5, fundamentalSolution 5 (X - Y) * (∂[i] g) Y) =
      ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * g Y := by
  let K : ℝ^5 → ℝ := fun Y ↦ fundamentalSolution 5 (X - Y)
  have hK (Y : ℝ^5) (hYX : Y ≠ X) :
      HasFDerivAt K
        ((fiveDimensionalGammaFDerivKernel (X - Y)).comp
          (-ContinuousLinearMap.id ℝ (ℝ^5))) Y :=
    (hasFDerivAt_fiveDimensionalGamma (X - Y) (sub_ne_zero.mpr hYX.symm)).comp Y
      ((hasFDerivAt_id Y).const_sub X)
  have hsupport : tsupport g ⊆ (Metric.ball X R)ᶜ :=
    closure_minimal (fun Y hY hball ↦ hY (hzero Y hball)) Metric.isOpen_ball.isClosed_compl
  have hKG :
      (fun Y : ℝ^5 ↦ fderiv ℝ K Y (EuclideanSpace.single i 1) * g Y) =
        (fun Y : ℝ^5 ↦ -(fiveDimensionalGammaGradientKernel i (X - Y) * g Y)) := by
    funext Y
    by_cases hYX : Y = X
    · subst Y
      simp only [hzero X (Metric.mem_ball_self hR), mul_zero, neg_zero]
    · have hk : fderiv ℝ K Y (EuclideanSpace.single i 1) =
          -fiveDimensionalGammaGradientKernel i (X - Y) := by
        rw [(hK Y hYX).fderiv]
        change fiveDimensionalGammaFDerivKernel (X - Y)
          (-EuclideanSpace.single i 1) = _
        rw [map_neg, fiveDimensionalGammaFDerivKernel_apply_single]
      rw [hk, neg_mul]
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (ℝ^5))) (f := K) (g := g)
    (v := EuclideanSpace.single i (1 : ℝ)) (by rw [hKG]; exact hgrad.neg) hsource hpot
    (fun Y hY ↦ (hK Y (by rintro rfl; exact hsupport hY (Metric.mem_ball_self hR)))
      |>.differentiableAt)
    (fun _ _ ↦ (hg.differentiable (by norm_num)).differentiableAt)
  rw [hKG, integral_neg, neg_neg] at hparts
  exact hparts

/-- A first derivative of the noncompact Newtonian convolution moves
onto the source. C¹ regularity and absolute convergence of the two Newtonian
pairings at one anchor supply the required integrability and integration by
parts; neither compact support nor a separate boundary-flux hypothesis is used. -/
theorem fundamentalSolution_five_convolution_partialDeriv_right_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5) (i : Fin 5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (hdInt : Integrable (fun Y : ℝ^5 ↦
      fundamentalSolution 5 (A - Y) * (∂[i] f) Y)) :
    (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) X =
      convolution (fundamentalSolution 5) (∂[i] f)
        (ContinuousLinearMap.mul ℝ ℝ) volume X := by
  have hdf : Continuous (∂[i] f) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hf).continuous
  have hfull :=
    fundamentalSolution_five_convolution_partialDeriv_eq_integral_of_integrable_at_anchor
      f hf A X i hInt
  have hfIntX := integrable_fundamentalSolution_five_mul_of_integrable_at_anchor
    f hf.continuous A X hInt
  have hdfIntX := integrable_fundamentalSolution_five_mul_of_integrable_at_anchor
    (∂[i] f) hdf A X hdInt
  let χ : ContDiffBump X := default
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ f Y - fnear Y
  have hfnear : ContDiff ℝ 1 fnear := χ.contDiff.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hg : ContDiff ℝ 1 g := hf.sub hfnear
  have hnear := fundamentalSolution_five_convolution_partialDeriv_eq_integral
    fnear hfnear hfnearc i X
  have hnearInt :
      Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * fnear Y) :=
    (hfnearc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hfnear.continuous X).integrable_swap
  have hdnearInt : Integrable (fun Y : ℝ^5 ↦
      fundamentalSolution 5 (X - Y) * (∂[i] fnear) Y) :=
    ((hfnearc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_fundamentalSolution 5)
      (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hfnear).continuous X).integrable_swap
  have hDg (Y : ℝ^5) :
      (∂[i] g) Y = (∂[i] f) Y - (∂[i] fnear) Y :=
    PDE.partialDeriv_sub (hf.differentiable (by norm_num)).differentiableAt
      (hfnear.differentiable (by norm_num)).differentiableAt
  have hzero : ∀ Y ∈ Metric.ball X χ.rIn, g Y = 0 := fun Y hY ↦ by
    simp only [g, fnear, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hY), one_mul,
      sub_self]
  have htail := fundamentalSolution_five_tail_source_derivative g hg X i χ.rIn χ.rIn_pos hzero
    (by simpa only [g, mul_sub] using! hfIntX.sub' hnearInt)
    (by simpa only [hDg, mul_sub] using hdfIntX.sub' hdnearInt)
    (by simpa only [g, mul_sub] using! hfull.1.sub' hnear.1)
  have hDsplit :
      (∫ Y : ℝ^5, fundamentalSolution 5 (X - Y) * (∂[i] g) Y) =
        (∫ Y : ℝ^5, fundamentalSolution 5 (X - Y) * (∂[i] f) Y) -
          ∫ Y : ℝ^5, fundamentalSolution 5 (X - Y) * (∂[i] fnear) Y := by
    simp_rw [hDg, mul_sub]
    exact integral_sub hdfIntX hdnearInt
  have hGsplit :
      (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * g Y) =
        (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * f Y) -
          ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * fnear Y := by
    simp only [g, mul_sub]
    exact integral_sub hfull.1 hnear.1
  have hnearTransfer :
      (∫ Y : ℝ^5, fundamentalSolution 5 (X - Y) * (∂[i] fnear) Y) =
        ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * fnear Y := by
    have hn := hnear.2
    rw [PDE.Analysis.convolution_partialDeriv_right _ _
      (locallyIntegrable_fundamentalSolution 5) hfnearc hfnear i X] at hn
    simpa only [convolution_mul_swap] using hn
  rw [hDsplit, hGsplit, hnearTransfer] at htail
  rw [hfull.2, convolution_mul_swap]
  exact (sub_left_inj.mp htail).symm

end PotentialTheory
