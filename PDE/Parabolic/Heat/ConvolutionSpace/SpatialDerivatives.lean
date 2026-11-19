/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValue
public import PDE.Parabolic.Heat.Kernel.SpatialDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.Parabolic.Heat.ConvolutionSpace.GaussianDomination
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Spatial derivatives of heat-kernel convolutions

For bounded continuous data `g` and `t > 0`, first and second spatial derivatives pass
through the convolution `x ↦ ∫ Γ(x - y, t) g(y) dy`: the gradient is the integral of
`g(y) ∇ₓΓ(x - y, t)`, each pure second partial is the integral of `g(y)` times the
corresponding Hessian entry, and hence `Δ` commutes with the convolution. All
interchanges are justified by the Gaussian majorants of `GaussianDomination`; the Hessian
of the kernel is the explicit operator `fundamentalSolutionHeatHessian`.

## Main results

* `hasFDerivAt_heatKernel_convolution_space`: the Fréchet derivative in `x` is the
  integral of `-(1/(2t)) Γ(x - y, t) g(y) ⟪x - y, ·⟫`.
* `hasFDerivAt_heatKernel_convolution_gradient_coord`: each coordinate of that gradient
  is again differentiable, with derivative the corresponding evaluated Hessian slot.
* `secondPartial_heatKernel_convolution`, `laplacian_heatKernel_convolution`: pure
  second partials and the Laplacian commute with the convolution.
* `hasFDerivAt_initialValueSolution_space`, `differentiableAt_initialValueSolution_space`,
  `differentiableAt_partialDeriv_initialValueSolution_space`: the same statements for
  `initialValueSolution`, giving the pointwise second-order spatial
  differentiability (differentiable first partials) used to interpret the heat equation
  classically.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 1 and equation (10) in its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace HeatEquation

open scoped Pointwise
open PDE.Common
open ConvolutionSpace

variable {n : ℕ}

/-! ## Spatial differentiation under the heat-kernel convolution -/

section SpatialConvolutionDerivative

open MeasureTheory

/-- Fréchet derivative commutes with the heat-kernel convolution in the spatial variable.

This is the spatial analogue of `hasDerivAt_heatKernel_convolution_time`. -/
theorem hasFDerivAt_heatKernel_convolution_space
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    HasFDerivAt
        (fun x' ↦
          ∫ y : ℝ^n,
            fundamentalSolutionHeat (n := n) (x' - y) t * g y)
        (∫ y : ℝ^n,
            ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x - y) t) * g y) •
              innerSL ℝ (x - y))
        x := by
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨bound, hbound_int, -, hbound⟩ :=
    exists_integrable_bound_heatKernelHessian g x t ht ⟨M, hM⟩
  have hKc : Continuous fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t :=
    continuous_iff_continuousAt.2 fun z ↦
      (differentiableAt_fundamentalSolutionHeat t ht z).continuousAt
  have hKxc : Continuous fun y : ℝ^n ↦ fundamentalSolutionHeat (n := n) (x - y) t :=
    hKc.comp (continuous_const.sub continuous_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x' y ↦ fundamentalSolutionHeat (n := n) (x' - y) t * g y)
    (F' := fun x' y ↦ ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x' - y) t) * g y) •
      innerSL ℝ (x' - y))
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun x' ↦
      ((hKc.comp (continuous_const.sub continuous_id)).mul hg_cont).aestronglyMeasurable)
    (((Measure.measurePreserving_sub_left _ x).integrable_comp_of_integrable
      (fundamentalSolutionHeat_integrable t ht)).mul_bdd hg_cont.aestronglyMeasurable
      (ae_of_all _ fun y ↦ (Real.norm_eq_abs _).trans_le (hM y)))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun y x' hx' ↦ by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using (hbound y x' hx').1)
    hbound_int (ae_of_all _ fun y x' _ ↦ ?_)
  have h := ((hasFDerivAt_fundamentalSolutionHeat_space t ht (x' - y)).comp x'
    ((hasFDerivAt_id x').sub_const y)).mul_const (g y)
  rw [ContinuousLinearMap.comp_id, smul_smul, mul_comm (g y)] at h
  exact h

/-- A coordinate of the convolution gradient can be differentiated under the integral sign.

The derivative is the corresponding evaluated slot of the Gaussian Hessian. The Bochner
integral is covector-valued rather than operator-valued, which is all the coordinate Laplacian
needs. -/
theorem hasFDerivAt_heatKernel_convolution_gradient_coord
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ)
    (i : Fin n) (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    HasFDerivAt
      (fun x' ↦
        ∫ y : ℝ^n,
          g y *
            (((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x' - y) t) •
              innerSL ℝ (x' - y)) (EuclideanSpace.single i (1 : ℝ))))
      (∫ y : ℝ^n,
        (g y) •
          (((ContinuousLinearMap.apply ℝ ℝ)
              (EuclideanSpace.single i (1 : ℝ))).comp
            (fundamentalSolutionHeatHessian (n := n) (x - y) t)))
      x := by
  obtain ⟨bound, hbound_int, -, hbound⟩ := exists_integrable_bound_heatKernelHessian g x t ht hg_bdd
  set ei : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  have hev (A : ℝ^n →L[ℝ] ℝ) : ‖A ei‖ ≤ ‖A‖ :=
    (A.le_opNorm ei).trans_eq (by simp [ei])
  have hgradient_cont : Continuous fun z : (ℝ^n) ↦
      (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) z t) • innerSL ℝ z :=
    continuous_iff_continuousAt.mpr fun z ↦
      (hasFDerivAt_fundamentalSolutionHeat_gradient (n := n) t ht z).continuousAt
  have hG_meas (x' : ℝ^n) : AEStronglyMeasurable (fun y ↦ g y *
      (((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x' - y) t) •
        innerSL ℝ (x' - y)) ei)) volume :=
    (hg_cont.mul ((hgradient_cont.comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const)).aestronglyMeasurable
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x' y ↦ (g y) • (((ContinuousLinearMap.apply ℝ ℝ) ei).comp
      (fundamentalSolutionHeatHessian (n := n) (x' - y) t)))
    (Metric.ball_mem_nhds x one_pos) (Filter.Eventually.of_forall hG_meas)
    (hbound_int.mono' (hG_meas x) (ae_of_all _ fun y ↦ ?_))
    (hg_cont.smul ((continuous_fundamentalSolutionHeatHessian_apply t ei).comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun y x' hx' ↦ ?_) hbound_int (ae_of_all _ fun y x' _ ↦ ?_)
  · refine (le_of_eq ?_).trans ((hev _).trans (hbound y x (Metric.mem_ball_self one_pos)).1)
    simp [smul_eq_mul]
  · refine (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
      fun h ↦ ?_).trans (hbound y x' hx').2
    calc _ = ‖(g y • fundamentalSolutionHeatHessian (n := n) (x' - y) t) h ei‖ := by
          simp [smul_eq_mul]
      _ ≤ _ := (hev _).trans (ContinuousLinearMap.le_opNorm _ _)
  · have h := (((ContinuousLinearMap.apply ℝ ℝ) ei).hasFDerivAt.comp x'
      ((hasFDerivAt_fundamentalSolutionHeat_gradient t ht (x' - y)).comp x'
        ((hasFDerivAt_id x').sub_const y))).const_mul (g y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp)

/-- A first partial of the heat-kernel convolution is the convolution of `g` with the matching
coordinate of the kernel gradient. -/
private theorem partialDeriv_heatKernel_convolution
    (g : ℝ^n → ℝ) (z : ℝ^n) (t : ℝ)
    (i : Fin n) (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    (∂[i] (fun x' ↦ ∫ y : ℝ^n, fundamentalSolutionHeat (n := n) (x' - y) t * g y)) z =
      ∫ y : ℝ^n, g y *
        (((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (z - y) t) •
          innerSL ℝ (z - y)) (EuclideanSpace.single i (1 : ℝ))) := by
  have hfirst : HasFDerivAt
      (fun x' ↦ ∫ y : ℝ^n, fundamentalSolutionHeat (n := n) (x' - y) t * g y)
      (∫ y : ℝ^n, (g y) • ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (z - y) t) •
        innerSL ℝ (z - y))) z := by
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using
      hasFDerivAt_heatKernel_convolution_space (n := n) g z t ht hg_cont hg_bdd
  unfold partialDeriv
  rw [hfirst.fderiv,
    ContinuousLinearMap.integral_apply (integrable_heatKernel_gradient g z t ht hg_cont hg_bdd)]
  rfl

/-- A coordinate second derivative commutes with heat-kernel convolution. -/
theorem secondPartial_heatKernel_convolution
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ)
    (i : Fin n) (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    (∂[i]
        (fun z ↦ (∂[i]
          (fun x' ↦ ∫ y : ℝ^n,
            fundamentalSolutionHeat (n := n) (x' - y) t * g y)) z)) x =
      ∫ y : ℝ^n,
        g y * fundamentalSolutionHeatHessian (n := n) (x - y) t
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
  have hD := (hasFDerivAt_heatKernel_convolution_gradient_coord g x t i ht hg_cont
    hg_bdd).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦
      partialDeriv_heatKernel_convolution g z t i ht hg_cont hg_bdd)
  change fderiv ℝ _ x _ = _
  rw [hD.fderiv, ContinuousLinearMap.integral_apply
    (integrable_heatKernelHessian_coord g x t i ht hg_cont hg_bdd)]
  simp [smul_eq_mul]

private theorem laplacian_heatKernel_convolution_eq_sum
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ)
    (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    laplacian (n := n)
        (fun x' ↦ ∫ y : ℝ^n,
          fundamentalSolutionHeat (n := n) (x' - y) t * g y) x =
      ∑ i : Fin n, ∫ y : ℝ^n,
        g y * fundamentalSolutionHeatHessian (n := n) (x - y) t
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
  unfold laplacian
  exact Finset.sum_congr rfl (fun i _hi ↦
    secondPartial_heatKernel_convolution (n := n) g x t i ht hg_cont hg_bdd)

private theorem sum_integral_heatKernelHessian_coord
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ)
    (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    (∑ i : Fin n, ∫ y : ℝ^n,
        g y * fundamentalSolutionHeatHessian (n := n) (x - y) t
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ))) =
      ∫ y : ℝ^n, ∑ i : Fin n,
        g y * fundamentalSolutionHeatHessian (n := n) (x - y) t
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
  symm
  refine MeasureTheory.integral_finsetSum Finset.univ ?_
  intro i _hi
  have hcoord := integrable_heatKernelHessian_coord (n := n) g x t i ht hg_cont hg_bdd
  have happ := ((ContinuousLinearMap.apply ℝ ℝ)
    (EuclideanSpace.single i (1 : ℝ))).integrable_comp hcoord
  simpa [smul_eq_mul] using happ

private theorem sum_heatKernelHessian_coord_eq_laplacian
    (g : ℝ^n → ℝ) (x y : ℝ^n) (t : ℝ)
    (ht : 0 < t) :
    (∑ i : Fin n,
      g y * fundamentalSolutionHeatHessian (n := n) (x - y) t
        (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) =
      g y * laplacian (n := n)
        (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)
        (x - y) := by
  rw [← trace_fundamentalSolutionHeatHessian_eq_laplacian (n := n) (x - y) t ht,
    Finset.mul_sum]

/-- The spatial Laplacian commutes with heat-kernel convolution for bounded continuous data. -/
theorem laplacian_heatKernel_convolution
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ)
    (ht : 0 < t) (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    laplacian (n := n)
        (fun x' ↦ ∫ y : ℝ^n,
          fundamentalSolutionHeat (n := n) (x' - y) t * g y) x =
      ∫ y : ℝ^n,
        g y * laplacian (n := n)
          (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)
          (x - y) := by
  rw [laplacian_heatKernel_convolution_eq_sum g x t ht hg_cont hg_bdd,
    sum_integral_heatKernelHessian_coord g x t ht hg_cont hg_bdd]
  exact integral_congr_ae (ae_of_all _ fun y ↦ sum_heatKernelHessian_coord_eq_laplacian g x y t ht)

end SpatialConvolutionDerivative

/-- The positive-time spatial derivative theorem stated for `initialValueSolution`.

For fixed positive time, `initialValueSolution` is exactly the heat-kernel convolution, so its
Fréchet derivative is the integral of the spatial derivative of the Gaussian kernel. -/
theorem hasFDerivAt_initialValueSolution_space
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    HasFDerivAt (fun x' ↦ initialValueSolution (n := n) g x' t)
      (∫ y : ℝ^n,
        ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) (x - y) t) * g y) •
          innerSL ℝ (x - y)) x := by
  simpa [initialValueSolution, not_le_of_gt ht] using
    hasFDerivAt_heatKernel_convolution_space (n := n) g x t ht hg_cont hg_bdd

/-- Bounded continuous initial data has a spatially differentiable heat evolution at every
positive time. -/
theorem differentiableAt_initialValueSolution_space
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    DifferentiableAt ℝ (fun x' ↦ initialValueSolution (n := n) g x' t) x :=
  (hasFDerivAt_initialValueSolution_space (n := n) g x t ht hg_cont hg_bdd).differentiableAt

/-- Every first spatial partial derivative of the heat-kernel convolution is
differentiable at positive time.

Together with `hasDerivAt_initialValueSolution_time`, this shows that every derivative
in the heat equation exists at each positive time, so `fderiv` never falls back to its
default value there. -/
theorem differentiableAt_partialDeriv_initialValueSolution_space
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (i : Fin n) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    DifferentiableAt ℝ
      (fun z ↦
        (∂[i]
          (fun x' ↦ initialValueSolution (n := n) g x' t)) z) x := by
  have hu : (fun x' ↦ initialValueSolution (n := n) g x' t) =
      fun x' ↦ ∫ y : ℝ^n, fundamentalSolutionHeat (n := n) (x' - y) t * g y := by
    funext x'
    simp [initialValueSolution, not_le_of_gt ht]
  rw [hu]
  exact (hasFDerivAt_heatKernel_convolution_gradient_coord g x t i ht hg_cont
    hg_bdd).differentiableAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦
      partialDeriv_heatKernel_convolution g z t i ht hg_cont hg_bdd)

end HeatEquation
