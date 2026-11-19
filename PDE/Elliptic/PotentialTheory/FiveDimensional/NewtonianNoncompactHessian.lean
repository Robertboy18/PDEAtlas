/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianCompact
public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianNear
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Hessians of noncompact C¹ Newtonian sources

The first-gradient kernel is locally integrable. For a compact C¹ source,
its convolution is C¹, so the first derivative of the potential can
be differentiated once more. A smooth cutoff combines this compact near
calculation with the classical Hessian of the separated tail.

The source needs one derivative and absolute convergence of its Newtonian
pairing at one anchor. No second source derivative or Hessian representation
is assumed. Spherical cancellation then identifies the Hessian with a centered
near integral and the classical exterior integral, with the exact diagonal
correction. Both terms are proved integrable for every positive radius.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

private theorem fundamentalSolution_five_compact_partialDeriv_eq_gradientConvolution
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (j : Fin 5) :
    ∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) =
      convolution (fiveDimensionalGammaGradientKernel j) f
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext X
  exact (fundamentalSolution_five_convolution_partialDeriv_eq_integral f hf hfc j X).2.trans
    convolution_mul_swap.symm

/-- A compact C¹ source gives a C¹ first derivative of its Newtonian potential.
The extra derivative comes from the locally integrable first-gradient kernel:
after identifying the gradient, one derivative falls on the source. -/
theorem contDiff_one_partialDeriv_fundamentalSolution_five_convolution
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (j : Fin 5) :
    ContDiff ℝ 1
      (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) := by
  rw [fundamentalSolution_five_compact_partialDeriv_eq_gradientConvolution f hf hfc j]
  exact hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_fiveDimensionalGammaGradientKernel j) hf

/-- The Hessian of a compact C¹ Newtonian source is an absolutely
convergent pairing of the first-gradient kernel with one source derivative.
This step needs only one derivative of the source, including at the axis. -/
theorem fundamentalSolution_five_convolution_hessian_eq_gradientKernel_sourceDerivative
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (i j : Fin 5) (X : ℝ^5) :
    Integrable (fun Y : ℝ^5 ↦
      fiveDimensionalGammaGradientKernel j (X - Y) * (∂[i] f) Y) ∧
      iteratedPartialDeriv [i, j]
          (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X =
        ∫ Y : ℝ^5,
          fiveDimensionalGammaGradientKernel j (X - Y) * (∂[i] f) Y := by
  have hd : Continuous (∂[i] f) := by
    change Continuous (fun Y : ℝ^5 ↦ fderiv ℝ f Y (EuclideanSpace.single i (1 : ℝ)))
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (∂[i] f) := by
    change HasCompactSupport (fun Y : ℝ^5 ↦
      fderiv ℝ f Y (EuclideanSpace.single i (1 : ℝ)))
    exact hfc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  refine ⟨(hdc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_fiveDimensionalGammaGradientKernel j) hd X).integrable_swap, ?_⟩
  change (∂[i]
    (∂[j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X = _
  rw [fundamentalSolution_five_compact_partialDeriv_eq_gradientConvolution f hf hfc j,
    PDE.Analysis.convolution_partialDeriv_right _ _
    (locallyIntegrable_fiveDimensionalGammaGradientKernel j) hfc hf i X]
  exact convolution_mul_swap

/-- A fixed smooth cutoff separates the first derivative into a
compact C¹ convolution and a tail which vanishes near the evaluation point.
Both derivatives are proved before applying the sum rule. -/
private theorem fundamentalSolution_five_integral_partialDeriv_cutoff
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (χ : ContDiffBump X) (j : Fin 5) :
    DifferentiableAt ℝ
        (∂[j]
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y)) X ∧
      (∀ i : Fin 5,
        iteratedPartialDeriv [i, j]
            (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X =
          (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel j (X - Y) *
            (∂[i] (fun W : ℝ^5 ↦ χ W * f W)) Y) +
          ∫ Y : ℝ^5, iteratedPartialDeriv [i, j] (fundamentalSolution 5) (X - Y) *
            (f Y - χ Y * f Y)) := by
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ f Y - fnear Y
  let Pnear : ℝ^5 → ℝ := fun Z ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * fnear Y
  let Ptail : ℝ^5 → ℝ := fun Z ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y
  have hfnear : ContDiff ℝ 1 fnear := χ.contDiff.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hg : ContDiff ℝ 1 g := hf.sub hfnear
  have hnearInt (Z : ℝ^5) :
      Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * fnear Y) :=
    (hfnearc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hfnear.continuous Z).integrable_swap
  have hgInt (Z : ℝ^5) : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * g Y) := by
    simpa only [g, mul_sub] using! (integrable_fundamentalSolution_five_mul_of_integrable_at_anchor
      f hf.continuous A Z hInt).sub' (hnearInt Z)
  have hzero : ∀ Y ∈ Metric.ball X χ.rIn, g Y = 0 := fun Y hY ↦ by
    simp only [g, fnear, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hY), one_mul,
      sub_self]
  have hnearConv :
      Pnear = convolution (fundamentalSolution 5) fnear (ContinuousLinearMap.mul ℝ ℝ) volume :=
    funext fun Z ↦ convolution_mul_swap.symm
  have hnearC1 : ContDiff ℝ 1 Pnear := by
    rw [hnearConv]
    exact hfnearc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hfnear
  have hnearFirst : DifferentiableAt ℝ (∂[j] Pnear) X := by
    rw [hnearConv]
    exact ((contDiff_one_partialDeriv_fundamentalSolution_five_convolution
      fnear hfnear hfnearc j).differentiable (by norm_num)).differentiableAt
  have htailFirst : DifferentiableAt ℝ (∂[j] Ptail) X :=
    (hasFDerivAt_partialDeriv_fundamentalSolution_five_integral_of_zero_on_ball
      g hg.continuous.measurable j X χ.rIn χ.rIn_pos hzero (hgInt X)).2.differentiableAt
  have hfirst : ∂[j] (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) =
      fun Z ↦ (∂[j] Pnear) Z + (∂[j] Ptail) Z := by
    have hpotential : (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) =
        fun Z ↦ Pnear Z + Ptail Z := funext fun Z ↦ by
      change _ = (∫ Y : ℝ^5, _) + ∫ Y : ℝ^5, _
      rw [← integral_add (hnearInt Z) (hgInt Z)]
      simp only [g, ← mul_add, add_sub_cancel]
    funext Z
    rw [hpotential]
    exact PDE.partialDeriv_add ((hnearC1.differentiable (by norm_num)).differentiableAt)
      (hasFDerivAt_fundamentalSolution_five_integral_of_integrable_at_anchor
        g hg X Z (hgInt X)).2.2.differentiableAt
  refine ⟨hfirst ▸ hnearFirst.add htailFirst, fun i ↦ ?_⟩
  change (∂[i] (∂[j]
    (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y))) X = _
  rw [hfirst, PDE.partialDeriv_add hnearFirst htailFirst]
  change iteratedPartialDeriv [i, j] Pnear X + iteratedPartialDeriv [i, j] Ptail X = _
  rw [hnearConv, (fundamentalSolution_five_convolution_hessian_eq_gradientKernel_sourceDerivative
      fnear hfnear hfnearc i j X).2,
    (fundamentalSolution_five_integral_hessian_eq_integral_of_zero_on_ball
      g hg.continuous.measurable i j X χ.rIn χ.rIn_pos hzero (hgInt X)).2]

/-- A noncompact C¹ source with an absolutely convergent Newtonian potential
at one anchor has differentiable first partial derivatives everywhere.
The cutoff argument supplies the second derivative without asking for a
second source derivative or an independently integrable Hessian kernel. -/
theorem differentiable_partialDeriv_fundamentalSolution_five_integral_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A : ℝ^5) (j : Fin 5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    Differentiable ℝ
      (∂[j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y)) := by
  intro X
  exact (fundamentalSolution_five_integral_partialDeriv_cutoff
    f hf A X hInt (default : ContDiffBump X) j).1

/-- A Newtonian Hessian entry splits into a compact C¹ near pairing
and an absolutely convergent classical tail. The near term differentiates
the cutoff source once; spherical cancellation can subsequently rewrite it
as the centered Hessian kernel with its diagonal correction. -/
theorem fundamentalSolution_five_integral_hessian_eq_cutoff_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (χ : ContDiffBump X) (i j : Fin 5) :
    iteratedPartialDeriv [i, j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X =
      (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel j (X - Y) *
        (∂[i] (fun W : ℝ^5 ↦ χ W * f W)) Y) +
      ∫ Y : ℝ^5, iteratedPartialDeriv [i, j] (fundamentalSolution 5) (X - Y) *
        (f Y - χ Y * f Y) :=
  (fundamentalSolution_five_integral_partialDeriv_cutoff f hf A X hInt χ j).2 i

/-- For a compact C¹ source, the first-gradient pairing equals a centered
near integral and an ordinary exterior integral, with the diagonal mass
removed. Both limits describe the same spherical truncation. -/
private theorem fundamentalSolution_five_compact_gradientPairing_eq_centered
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (X : ℝ^5) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun H : ℝ^5 ↦
        iteratedPartialDeriv [i, j] (fundamentalSolution 5) H *
          (f (X - H) - f X)) (Metric.ball (0 : ℝ^5) R) ∧
      IntegrableOn (fun H : ℝ^5 ↦
        iteratedPartialDeriv [i, j] (fundamentalSolution 5) H * f (X - H))
        (Metric.ball (0 : ℝ^5) R)ᶜ ∧
      (∫ Y : ℝ^5,
          fiveDimensionalGammaGradientKernel j (X - Y) * (∂[i] f) Y) =
        (∫ H in Metric.ball (0 : ℝ^5) R,
          iteratedPartialDeriv [i, j] (fundamentalSolution 5) H *
            (f (X - H) - f X)) +
        (∫ H in (Metric.ball (0 : ℝ^5) R)ᶜ,
          iteratedPartialDeriv [i, j] (fundamentalSolution 5) H * f (X - H)) -
        (if i = j then f X / 5 else 0) := by
  let F : ℝ^5 → ℝ := fun H ↦ f (X - H)
  let K : ℝ^5 → ℝ := iteratedPartialDeriv [i, j] (fundamentalSolution 5)
  let B : Set (ℝ^5) := Metric.ball 0 R
  have hF : ContDiff ℝ 1 F := hf.comp (contDiff_const.sub contDiff_id)
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (show HasCompactSupport F from hfc.comp_homeomorph (Homeomorph.subLeft X)) hF one_ne_zero
  have hlip : ∀ H ∈ Metric.ball (0 : ℝ^5) R, |F H - F 0| ≤ (C : ℝ) * ‖H‖ := fun H _ ↦ by
    simpa only [Real.norm_eq_abs, sub_zero] using hLip.norm_sub_le H 0
  have hnear := fundamentalSolution_five_hessian_near_principalValue_tendsto
    i j F hF.continuous.measurable R C hR C.coe_nonneg hlip
  have hpv := fundamentalSolution_five_hessian_principalValue_sub_of_contDiff_one i j f hf hfc X
  have hfar : IntegrableOn (fun H : ℝ^5 ↦ K H * F H) Bᶜ :=
    (hpv.1 (R / 2) (half_pos hR)).mono_set fun H hH ↦
      (half_lt_self hR).trans_le (by simpa [B] using hH)
  have hlimit : Tendsto (fun ε : ℝ ↦ ∫ H in {H : ℝ^5 | ε < ‖H‖}, K H * F H) (𝓝[>] 0)
      (𝓝 ((∫ H in B, K H * (F H - F 0)) + ∫ H in Bᶜ, K H * F H)) := by
    refine (hnear.2.add_const (∫ H in Bᶜ, K H * F H)).congr' ?_
    filter_upwards [self_mem_nhdsWithin, Filter.mem_inf_of_left (Iio_mem_nhds hR)]
      with ε hε (hεR : ε < R)
    have hdiff : {H : ℝ^5 | ε < ‖H‖} \ B = Bᶜ := Set.sdiff_eq_compl_inter.trans
      (Set.inter_eq_left.2 fun H hH ↦ hεR.trans_le (by simpa [B] using hH))
    rw [← integral_inter_add_sdiff (measurableSet_ball : MeasurableSet B) (hpv.1 ε hε), hdiff,
      Set.inter_comm {H : ℝ^5 | ε < ‖H‖} B]
  have heq := tendsto_nhds_unique hpv.2 hlimit
  rw [show (∫ H : ℝ^5, fiveDimensionalGammaGradientKernel j H * (∂[i] f) (X - H)) =
      ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel j (X - Y) * (∂[i] f) Y from
    convolution_mul_swap] at heq
  exact ⟨by simpa only [F, sub_zero] using
      (integrableOn_and_norm_integral_fundamentalSolution_five_hessian_sub
        i j F hF.continuous.measurable R C hR C.coe_nonneg hlip).1, hfar,
    by simpa only [F, sub_zero] using eq_sub_iff_add_eq.mpr heq⟩

/-- The Hessian of a noncompact C¹ Newtonian source is its centered
near integral plus its classical exterior integral, with the exact diagonal
correction. The near subtraction and both integrability statements are
derived here. Absolute convergence of the potential at one anchor is the
only decay assumption; neither a principal value nor a Hessian identity is
assumed. -/
theorem fundamentalSolution_five_integral_hessian_eq_centered_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y))
    (i j : Fin 5) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun H : ℝ^5 ↦
        iteratedPartialDeriv [i, j] (fundamentalSolution 5) H *
          (f (X - H) - f X)) (Metric.ball (0 : ℝ^5) R) ∧
      IntegrableOn (fun H : ℝ^5 ↦
        iteratedPartialDeriv [i, j] (fundamentalSolution 5) H * f (X - H))
        (Metric.ball (0 : ℝ^5) R)ᶜ ∧
      iteratedPartialDeriv [i, j]
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X =
        (∫ H in Metric.ball (0 : ℝ^5) R,
          iteratedPartialDeriv [i, j] (fundamentalSolution 5) H *
            (f (X - H) - f X)) +
        (∫ H in (Metric.ball (0 : ℝ^5) R)ᶜ,
          iteratedPartialDeriv [i, j] (fundamentalSolution 5) H * f (X - H)) -
        (if i = j then f X / 5 else 0) := by
  let χ : ContDiffBump X := ⟨R, R + 1, hR, lt_add_one R⟩
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ f Y - fnear Y
  let K : ℝ^5 → ℝ := iteratedPartialDeriv [i, j] (fundamentalSolution 5)
  let B : Set (ℝ^5) := Metric.ball 0 R
  have hfnear : ContDiff ℝ 1 fnear := χ.contDiff.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hnearEq (Y : ℝ^5) (hY : Y ∈ Metric.closedBall X R) : fnear Y = f Y := by
    simp only [fnear, χ.one_of_mem_closedBall hY, one_mul]
  have hcenter : fnear X = f X := hnearEq X (Metric.mem_closedBall_self hR.le)
  have hzero : ∀ Y ∈ Metric.ball X R, g Y = 0 := fun Y hY ↦ by
    simp only [g, hnearEq Y (Metric.ball_subset_closedBall hY), sub_self]
  have hsubmem (H : ℝ^5) (hH : H ∈ B) : X - H ∈ Metric.ball X R := by
    simpa [B, dist_eq_norm] using hH
  have hnearInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * fnear Y) :=
    (hfnearc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hfnear.continuous X).integrable_swap
  have hgInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y) := by
    simpa only [g, mul_sub] using! (integrable_fundamentalSolution_five_mul_of_integrable_at_anchor
      f hf.continuous A X hInt).sub' hnearInt
  have htailShift : Integrable (fun H : ℝ^5 ↦ K H * g (X - H)) := by
    simpa only [sub_sub_cancel] using
      (integrable_and_norm_integral_fundamentalSolution_five_hessian_of_zero_on_ball
        g (hf.continuous.sub hfnear.continuous).measurable i j X X R hR
        (by simpa only [sub_self, norm_zero] using (half_pos hR).le) hzero hgInt).1.comp_sub_left X
  have htailExterior : (∫ Y : ℝ^5, K (X - Y) * g Y) = ∫ H in Bᶜ, K H * g (X - H) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun H hH ↦ by
      rw [hzero (X - H) (hsubmem H (not_not.1 hH)), mul_zero]]
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self (fun H : ℝ^5 ↦ K H * g (X - H)) (volume : Measure (ℝ^5)) X
  have hcompact :=
    fundamentalSolution_five_compact_gradientPairing_eq_centered i j fnear hfnear hfnearc X R hR
  have hcentered : Set.EqOn (fun H : ℝ^5 ↦ K H * (fnear (X - H) - fnear X))
      (fun H : ℝ^5 ↦ K H * (f (X - H) - f X)) B := fun H hH ↦ by
    simp only [hnearEq (X - H) (Metric.ball_subset_closedBall (hsubmem H hH)), hcenter]
  have hsum : Set.EqOn (fun H ↦ K H * fnear (X - H) + K H * g (X - H))
      (fun H ↦ K H * f (X - H)) Bᶜ := fun H _ ↦ by
    simp only [g, ← mul_add, add_sub_cancel]
  refine ⟨hcompact.1.congr_fun hcentered measurableSet_ball,
    (hcompact.2.1.add htailShift.integrableOn).congr_fun hsum measurableSet_ball.compl, ?_⟩
  have hactual : iteratedPartialDeriv [i, j]
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) X =
    (∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel j (X - Y) * (∂[i] fnear) Y) +
      ∫ Y : ℝ^5, K (X - Y) * g Y :=
    fundamentalSolution_five_integral_hessian_eq_cutoff_of_integrable_at_anchor
      f hf A X hInt χ i j
  rw [hactual, hcompact.2.2, setIntegral_congr_fun measurableSet_ball hcentered, hcenter,
    htailExterior, ← setIntegral_congr_fun measurableSet_ball.compl hsum,
    integral_add hcompact.2.1 htailShift.integrableOn]
  ring

end PotentialTheory
