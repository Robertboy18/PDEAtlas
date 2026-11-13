/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactPoisson
public import PDE.Elliptic.Classical.Harmonic.Smoothness
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Finite regularity of the Newtonian potential

The first-gradient kernel is locally integrable, so a compact source gains
one derivative without assuming infinitely many source derivatives. For a
noncompact source, a fixed cutoff separates this calculation from a harmonic
tail. The tail first acquires two continuous derivatives from its integrable
Hessian majorant; interior harmonic regularity then supplies every order.

Absolute convergence at one anchor controls the tail throughout this argument.
No integrability of higher source derivatives is used.
-/

@[expose] public section

open PDE (laplacian iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace PotentialTheory

/-- A compact Cᵏ source gains one derivative in the Newtonian convolution.
The first derivative stays on the locally integrable kernel; the remaining
derivatives fall on the source. -/
theorem contDiff_succ_fundamentalSolution_five_convolution
    (k : ℕ) (hk : 1 ≤ k) (f : ℝ^5 → ℝ) (hf : ContDiff ℝ k f)
    (hfc : HasCompactSupport f) :
    ContDiff ℝ (k + 1)
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) := by
  let P := convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast hk)
  have hP1 : ContDiff ℝ 1 P :=
    hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hf1
  have hpartial (j : Fin 5) : ContDiff ℝ k (∂[j] P) := by
    have heq : ∂[j] P =
        convolution (fiveDimensionalGammaGradientKernel j) f
          (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext X
      exact (fundamentalSolution_five_convolution_partialDeriv_eq_integral
        f hf1 hfc j X).2.trans convolution_mul_swap.symm
    rw [heq]
    exact hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fiveDimensionalGammaGradientKernel j) hf
  refine contDiff_succ_iff_hasFDerivAt.mpr ⟨fderiv ℝ P, ?_, ?_⟩
  · apply contDiff_clm_apply_iff.mpr
    intro v
    have hsum : ContDiff ℝ k
        (fun X : ℝ^5 ↦ ∑ j : Fin 5, (∂[j] P) X * v j) :=
      ContDiff.sum (fun j _ ↦ (hpartial j).mul contDiff_const)
    simpa only [PDE.fderiv_apply_eq_sum_partialDeriv_mul] using hsum
  · intro X
    exact (hP1.differentiable_one X).hasFDerivAt

/-- A separated Hessian integral is continuous at its anchor. The same
Newtonian pairing that controls the Hessian also dominates nearby integrands,
so continuity does not require an extra tail assumption. -/
theorem continuousAt_integral_fundamentalSolution_five_hessian_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (i j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    ContinuousAt
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5,
        iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y) * g Y) X := by
  let B : ℝ^5 → ℝ := fun Y ↦
    (576 / r ^ 2) * ‖fundamentalSolution 5 (X - Y) * g Y‖
  apply continuousAt_of_dominated (bound := B)
  · exact Eventually.of_forall fun Z ↦
      (((measurable_fundamentalSolution_five_hessian i j).comp
        (measurable_const.sub measurable_id)).mul hg).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds X (half_pos hr)] with Z hZ
    refine Eventually.of_forall fun Y ↦ ?_
    by_cases hY : g Y = 0
    · simp only [B, hY, mul_zero, norm_zero, le_refl]
    have haway : r ≤ ‖X - Y‖ :=
      not_lt.1 fun h ↦ hY (hzero Y (by rwa [Metric.mem_ball, dist_comm, dist_eq_norm]))
    have hbound := abs_fundamentalSolution_five_hessian_sub_le_of_near
      i j hr (mem_ball_iff_norm.1 hZ).le haway
    calc
      ‖iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y) * g Y‖ =
          |iteratedPartialDeriv [i, j] (fundamentalSolution 5) (Z - Y)| * |g Y| := by
            simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ((576 / r ^ 2) * |fundamentalSolution 5 (X - Y)|) * |g Y| := by gcongr
      _ = B Y := by simp only [B, norm_mul, Real.norm_eq_abs, mul_assoc]
  · exact hInt.norm.const_mul _
  · refine Eventually.of_forall fun Y ↦ ?_
    by_cases hY : g Y = 0
    · simpa only [hY, mul_zero] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ^5 ↦ (0 : ℝ)) X)
    have hXY : X - Y ≠ 0 := fun h ↦ hY (hzero Y (sub_eq_zero.mp h ▸ Metric.mem_ball_self hr))
    have hΓ : ContDiffAt ℝ 2 (fundamentalSolution 5) (X - Y) :=
      (contDiffAt_fundamentalSolution 5 (X - Y) hXY).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hH := (PDE.contDiffAt_partialDeriv 0 (PDE.contDiffAt_partialDeriv 1 hΓ j) i).continuousAt
    exact (ContinuousAt.comp (f := fun Z : ℝ^5 ↦ Z - Y) (x := X) hH (by fun_prop)).mul
      continuousAt_const

private theorem contDiffOn_succ_of_partialDeriv
    (k : ℕ) (f : ℝ^5 → ℝ) (hf : Differentiable ℝ f)
    {U : Set (ℝ^5)} (hU : IsOpen U)
    (hpartial : ∀ i : Fin 5, ContDiffOn ℝ k (∂[i] f) U) :
    ContDiffOn ℝ (k + 1) f U := by
  apply contDiffOn_succ_of_fderiv_apply hf.differentiableOn (by simp)
  intro v
  have hsum : ContDiffOn ℝ k
      (fun X : ℝ^5 ↦ ∑ i : Fin 5, (∂[i] f) X * v i) U :=
    ContDiffOn.sum (fun i _ ↦ (hpartial i).mul contDiffOn_const)
  apply hsum.congr
  intro X hX
  rw [fderivWithin_of_isOpen hU hX, PDE.fderiv_apply_eq_sum_partialDeriv_mul]

/-- The Hessian of a separated C¹ source is continuous near the pole.
This transfers continuity of the integral to the derivative already identified
by the tail differentiation theorem. -/
theorem continuousAt_hessian_fundamentalSolution_five_integral_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g) (i j : Fin 5)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    ContinuousAt
      (iteratedPartialDeriv [i, j]
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y)) X := by
  have hcont := continuousAt_integral_fundamentalSolution_five_hessian_of_zero_on_ball
    g hg.continuous.measurable i j X r hr hzero hInt
  apply hcont.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds X (half_pos hr)] with Z hZ
  have hIntZ :=
    integrable_fundamentalSolution_five_mul_of_integrable_at_anchor g hg.continuous X Z hInt
  have hzeroZ : ∀ Y ∈ Metric.ball Z (r / 2), g Y = 0 := fun Y hY ↦
    hzero Y (Metric.ball_subset_ball' (by linarith [Metric.mem_ball.mp hZ]) hY)
  exact (fundamentalSolution_five_integral_hessian_eq_integral_of_zero_on_ball
    g hg.continuous.measurable i j Z (r / 2) (half_pos hr) hzeroZ hIntZ).2

/-- A Newtonian source which vanishes on a ball gives a smooth potential
inside that ball. Two derivatives follow from the Hessian formula
and dominated continuity; harmonic regularity supplies the higher orders. -/
theorem contDiffAt_fundamentalSolution_five_integral_of_zero_on_ball
    (m : ℕ∞) (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g)
    (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    ContDiffAt ℝ m
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y) X := by
  let P : ℝ^5 → ℝ := fun Z ↦
    ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y
  let B : Set (ℝ^5) := Metric.ball X (r / 2)
  have hPdiff : Differentiable ℝ P := fun Z ↦
    (hasFDerivAt_fundamentalSolution_five_integral_of_integrable_at_anchor
      g hg X Z hInt).2.2.differentiableAt
  have hfirstDiff (j : Fin 5) : Differentiable ℝ (∂[j] P) :=
    differentiable_partialDeriv_fundamentalSolution_five_integral_of_integrable_at_anchor
      g hg X j hInt
  have hH (i j : Fin 5) : ContinuousOn (iteratedPartialDeriv [i, j] P) B := by
    intro Z hZ
    have hIntZ :=
      integrable_fundamentalSolution_five_mul_of_integrable_at_anchor g hg.continuous X Z hInt
    have hzeroZ : ∀ Y ∈ Metric.ball Z (r / 2), g Y = 0 := fun Y hY ↦
      hzero Y (Metric.ball_subset_ball' (by linarith [Metric.mem_ball.mp hZ]) hY)
    exact (continuousAt_hessian_fundamentalSolution_five_integral_of_zero_on_ball
      g hg i j Z (r / 2) (half_pos hr) hzeroZ hIntZ).continuousWithinAt
  have hfirst (j : Fin 5) : ContDiffOn ℝ 1 (∂[j] P) B :=
    contDiffOn_succ_of_partialDeriv 0 _ (hfirstDiff j) Metric.isOpen_ball
      (fun i ↦ contDiffOn_zero.mpr (hH i j))
  have hPtwo : ContDiffOn ℝ 2 P B :=
    contDiffOn_succ_of_partialDeriv 1 P hPdiff Metric.isOpen_ball hfirst
  have hharmonic : LaplacianEquation.IsHarmonicPDE 5 P B := by
    refine ⟨hPtwo, fun Z hZ ↦ neg_eq_zero.mp ?_⟩
    simpa only [P, laplacian, iteratedPartialDeriv,
      hzero Z (Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hZ)] using
      fundamentalSolution_five_integral_solves_poisson_of_integrable_at_anchor g hg X Z hInt
  let : Fact (0 < (5 : ℕ)) := ⟨by norm_num⟩
  have hsmooth : ContDiffOn ℝ m P B :=
    hharmonic.contDiffOn_of_isOpen Metric.isOpen_ball
  exact (hsmooth X (Metric.mem_ball_self (half_pos hr))).contDiffAt
    (Metric.ball_mem_nhds X (half_pos hr))

/-- Finite source regularity gives one additional derivative of the
noncompact Newtonian integral. A compact cutoff supplies the local gain,
and the remaining potential is harmonic near the evaluation point.
Only the original absolute Newtonian pairing is required at infinity. -/
theorem contDiff_succ_fundamentalSolution_five_integral_of_integrable_at_anchor
    (k : ℕ) (hk : 1 ≤ k) (f : ℝ^5 → ℝ) (hf : ContDiff ℝ k f) (A : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    ContDiff ℝ (k + 1)
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast hk)
  rw [contDiff_iff_contDiffAt]
  intro X
  let χ : ContDiffBump X := default
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ f Y - fnear Y
  let Pnear : ℝ^5 → ℝ := fun Z ↦
    ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * fnear Y
  let Ptail : ℝ^5 → ℝ := fun Z ↦
    ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y
  have hfnear : ContDiff ℝ k fnear := χ.contDiff.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hg : ContDiff ℝ 1 g :=
    hf1.sub (hfnear.of_le (by exact_mod_cast hk))
  have hAll (Z : ℝ^5) :=
    integrable_fundamentalSolution_five_mul_of_integrable_at_anchor f hf.continuous A Z hInt
  have hnearInt (Z : ℝ^5) :
      Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * fnear Y) :=
    (hfnearc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hfnear.continuous Z).integrable_swap
  have hgInt (Z : ℝ^5) :
      Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * g Y) := by
    simpa only [g, mul_sub] using! (hAll Z).sub' (hnearInt Z)
  have hzero : ∀ Y ∈ Metric.ball X χ.rIn, g Y = 0 := fun Y hY ↦ by
    simp only [g, fnear, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hY), one_mul,
      sub_self]
  have hnear : ContDiff ℝ (k + 1) Pnear := by
    rw [show Pnear = convolution (fundamentalSolution 5) fnear (ContinuousLinearMap.mul ℝ ℝ)
      volume from funext fun Z ↦ convolution_mul_swap.symm]
    exact contDiff_succ_fundamentalSolution_five_convolution k hk fnear hfnear hfnearc
  have htail : ContDiffAt ℝ (k + 1) Ptail X :=
    contDiffAt_fundamentalSolution_five_integral_of_zero_on_ball
      ((k + 1 : ℕ) : ℕ∞) g hg X χ.rIn χ.rIn_pos hzero (hgInt X)
  have hpotential :
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) =
        (fun Z : ℝ^5 ↦ Pnear Z + Ptail Z) := by
    funext Z
    change (∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) =
      (∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * fnear Y) +
      ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y
    rw [← integral_add (hnearInt Z) (hgInt Z)]
    exact integral_congr_ae (.of_forall fun Y ↦ by dsimp only [g]; ring)
  rw [hpotential]
  exact hnear.contDiffAt.add htail

end PotentialTheory
