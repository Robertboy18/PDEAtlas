/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# The locally integrable planar gradient kernel

The weak first derivatives of the Poisson-normalized logarithmic kernel on the
whole plane are `-xᵢ/(2π|x|²)`. Their singularity is bounded by `1/(2π|x|)`, which is
locally integrable in the plane. The pole is assigned value zero.

## Main definitions

* `gradientKernel`: the Cartesian first derivative `-xᵢ/(2π|x|²)` of the planar logarithmic
  kernel, set to zero at the pole.

## Main results

* `norm_gradientKernel_le`: `|gradientKernel i x| ≤ 1/(2π|x|)`.
* `locallyIntegrable_gradientKernel`: the gradient kernel is locally integrable, also at the pole.
* `tendsto_integral_partialDeriv_regularizedFundamentalSolution_inv_mul`: the regularized gradient
  converges to the gradient kernel under integration against a continuous compactly supported
  multiplier.
* `integral_fundamentalSolution_mul_partialDeriv`: one distributional derivative of the planar
  logarithm is the gradient kernel, with no point mass.
* `hasWeakDerivativeOn_fundamentalSolution_two`: the gradient kernel is the weak first
  coordinate derivative of the planar fundamental solution on the whole plane.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace PotentialTheory.Planar

open MeasureTheory Filter Topology PDE.Analysis
open PDE (partialDeriv)

/-- A Cartesian first derivative of the planar logarithmic kernel, set to zero
at the pole. This point value does not affect its integral operator. -/
def gradientKernel (i : Fin 2) (x : ℝ^2) : ℝ :=
  -(1 / (2 * Real.pi)) * x i * ‖x‖ ^ (-2 : ℝ)

/-- The planar gradient singularity has inverse-radius size. -/
theorem norm_gradientKernel_le (i : Fin 2) (x : ℝ^2) :
    ‖gradientKernel i x‖ ≤ (1 / (2 * Real.pi)) * ‖x‖ ^ (-1 : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simp [gradientKernel]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hmul : ‖x‖ * ‖x‖ ^ (-2 : ℝ) = ‖x‖ ^ (-1 : ℝ) := by
    calc
      _ = ‖x‖ ^ (1 : ℝ) * ‖x‖ ^ (-2 : ℝ) := by rw [Real.rpow_one]
      _ = ‖x‖ ^ ((1 : ℝ) + -2) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [gradientKernel, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi)),
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ‖x‖ * ‖x‖ ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoord (by positivity))
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = _ := by rw [mul_assoc, hmul]

/-- First derivatives of the logarithmic kernel are locally integrable even
at their pole. -/
theorem locallyIntegrable_gradientKernel (i : Fin 2) :
    LocallyIntegrable (gradientKernel i) volume := by
  have hmeas : AEStronglyMeasurable (gradientKernel i) volume := by
    unfold gradientKernel
    fun_prop
  exact locallyIntegrable_of_norm_le_rpow
    (by norm_num : 1 ≤ Module.finrank ℝ (ℝ^2))
    (by norm_num : (1 : ℝ) < Module.finrank ℝ (ℝ^2))
    (Eventually.of_forall (norm_gradientKernel_le i)) hmeas

/-- Away from a zero denominator, the regularized logarithmic kernel has its
explicit Cartesian first derivative. This includes zero regularization away from the pole. -/
theorem partialDeriv_regularizedFundamentalSolution
    (ε : ℝ) (i : Fin 2) (x : ℝ^2) (harg : ‖x‖ ^ 2 + ε ^ 2 ≠ 0) :
    (∂[i] (regularizedFundamentalSolution ε)) x =
      -(1 / (2 * Real.pi)) * x i / (‖x‖ ^ 2 + ε ^ 2) := by
  have hlog := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).log harg
  have hd := hlog.const_mul (-(1 / (4 * Real.pi)))
  unfold partialDeriv regularizedFundamentalSolution
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial]
  field_simp
  ring

/-- The gradient kernel can also be written using the squared radius denominator. -/
theorem gradientKernel_eq_div (i : Fin 2) (x : ℝ^2) :
    gradientKernel i x = -(1 / (2 * Real.pi)) * x i / ‖x‖ ^ 2 := by
  simp [gradientKernel, Real.rpow_neg (norm_nonneg x), Real.rpow_ofNat, div_eq_mul_inv]

/-- Regularizing the logarithmic pole decreases the magnitude of every first
Cartesian derivative. -/
theorem norm_partialDeriv_regularizedFundamentalSolution_le
    {ε : ℝ} (hε : ε ≠ 0) (i : Fin 2) (x : ℝ^2) :
    ‖(∂[i] (regularizedFundamentalSolution ε)) x‖ ≤ ‖gradientKernel i x‖ := by
  have harg : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  rw [partialDeriv_regularizedFundamentalSolution ε i x harg.ne', gradientKernel_eq_div,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
    abs_of_pos harg, abs_of_nonneg (sq_nonneg ‖x‖)]
  by_cases hx : x = 0
  · subst x
    simp
  · exact div_le_div_of_nonneg_left (abs_nonneg _)
      (sq_pos_of_pos (norm_pos_iff.mpr hx)) (le_add_of_nonneg_right (sq_nonneg _))

/-- The regularized first derivatives converge to the gradient kernel away from the pole. -/
theorem tendsto_partialDeriv_regularizedFundamentalSolution_inv
    (i : Fin 2) {x : ℝ^2} (hx : x ≠ 0) :
    Tendsto (fun c : ℝ ↦ (∂[i] (regularizedFundamentalSolution c⁻¹)) x)
      atTop (𝓝 (gradientKernel i x)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hden : Tendsto (fun c : ℝ ↦ ‖x‖ ^ 2 + c⁻¹ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
    have hinv : Tendsto (fun c : ℝ ↦ c⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using tendsto_const_nhds.add (hinv.pow 2)
  have hresult : Tendsto (fun c : ℝ ↦ -(1 / (2 * Real.pi)) * x i /
      (‖x‖ ^ 2 + c⁻¹ ^ 2)) atTop (𝓝 (-(1 / (2 * Real.pi)) * x i / ‖x‖ ^ 2)) :=
    tendsto_const_nhds.div hden (pow_ne_zero 2 hr.ne')
  have hformula (c : ℝ) :
      (∂[i] (regularizedFundamentalSolution c⁻¹)) x =
        -(1 / (2 * Real.pi)) * x i / (‖x‖ ^ 2 + c⁻¹ ^ 2) :=
    partialDeriv_regularizedFundamentalSolution _ i x
      (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _)))
  simpa only [hformula, gradientKernel_eq_div] using
    (hresult : Tendsto (fun c : ℝ ↦ -(1 / (2 * Real.pi)) * x i /
      (‖x‖ ^ 2 + c⁻¹ ^ 2)) atTop (𝓝 (-(1 / (2 * Real.pi)) * x i / ‖x‖ ^ 2)))

/-- The regularized gradient converges under integration against a continuous
compactly supported multiplier. The singular gradient is an integrable majorant. -/
theorem tendsto_integral_partialDeriv_regularizedFundamentalSolution_inv_mul
    (i : Fin 2) {g : ℝ^2 → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun c : ℝ ↦ ∫ x : ℝ^2,
      (∂[i] (regularizedFundamentalSolution c⁻¹)) x * g x) atTop
      (𝓝 (∫ x : ℝ^2, gradientKernel i x * g x)) := by
  have hint : Integrable (fun x ↦ gradientKernel i x * g x) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_gradientKernel i).integrable_smul_right_of_hasCompactSupport hg hgc
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ^2 ↦ ‖gradientKernel i x * g x‖) ?_ ?_ hint.norm ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact ((PDE.contDiff_top_partialDeriv (i := i)
      (contDiff_regularizedFundamentalSolution (inv_ne_zero hc.ne'))).continuous.mul
        hg).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact Eventually.of_forall fun x ↦ by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_partialDeriv_regularizedFundamentalSolution_le (inv_ne_zero hc.ne') i x)
        (norm_nonneg _)
  · filter_upwards [Measure.ae_ne volume (0 : ℝ^2)] with x hx
    exact (tendsto_partialDeriv_regularizedFundamentalSolution_inv i hx).mul_const (g x)

/-- One distributional derivative of the planar logarithm is represented by its
locally integrable gradient kernel. No point mass occurs at first order. -/
theorem integral_fundamentalSolution_mul_partialDeriv
    (i : Fin 2) {g : ℝ^2 → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ^2, fundamentalSolution 2 x * (∂[i] g) x) =
      -(∫ x : ℝ^2, gradientKernel i x * g x) := by
  have hdg : Continuous (∂[i] g) := by
    change Continuous (fun x ↦ fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))
    exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdgc : HasCompactSupport (∂[i] g) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hleft := tendsto_integral_regularizedFundamentalSolution_inv_mul hdg hdgc
  have hright := tendsto_integral_partialDeriv_regularizedFundamentalSolution_inv_mul i
    hg.continuous hgc
  have hparts : ∀ᶠ c : ℝ in atTop,
      (∫ x : ℝ^2, regularizedFundamentalSolution c⁻¹ x * (∂[i] g) x) =
        -(∫ x : ℝ^2, (∂[i] (regularizedFundamentalSolution c⁻¹)) x * g x) := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    have hu : ContDiff ℝ 1 (regularizedFundamentalSolution c⁻¹) :=
      (contDiff_regularizedFundamentalSolution (inv_ne_zero hc.ne')).of_le (by simp)
    have hdu : Continuous (∂[i] (regularizedFundamentalSolution c⁻¹)) := by
      change Continuous (fun x ↦ fderiv ℝ (regularizedFundamentalSolution c⁻¹) x
        (EuclideanSpace.single i (1 : ℝ)))
      exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdug := (hdu.mul hg.continuous).integrable_of_hasCompactSupport (μ := volume) hgc.mul_left
    have hudg := (hu.continuous.mul hdg).integrable_of_hasCompactSupport (μ := volume) hdgc.mul_left
    have hug := (hu.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (μ := volume) hgc.mul_left
    simpa only [partialDeriv] using
      (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (ℝ^2)))
        (f := regularizedFundamentalSolution c⁻¹) (g := g)
        (v := EuclideanSpace.single i (1 : ℝ)) hdug hudg hug
        (fun _ _ ↦ (hu.differentiable (by norm_num)).differentiableAt)
        (fun _ _ ↦ (hg.differentiable (by norm_num)).differentiableAt))
  apply tendsto_nhds_unique hleft
  exact (tendsto_congr' hparts).mpr hright.neg

/-- The first coordinate derivative of the planar fundamental solution is its
locally integrable gradient kernel in the weak sense on the whole plane. -/
theorem hasWeakDerivativeOn_fundamentalSolution_two (i : Fin 2) :
    SobolevSpace.HasWeakDerivativeOn Set.univ [i] (fundamentalSolution 2) (gradientKernel i) := by
  refine ⟨(locallyIntegrable_fundamentalSolution 2).locallyIntegrableOn Set.univ,
    (locallyIntegrable_gradientKernel i).locallyIntegrableOn Set.univ, ?_⟩
  intro φ _
  simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul] using
    integral_fundamentalSolution_mul_partialDeriv (g := φ.toFun) i
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

end PotentialTheory.Planar
