/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Regularity of scalar divided differences

Mathlib's `dslope f a b` extends the secant slope continuously to the diagonal
by setting `dslope f a a = deriv f a`. For a twice continuously differentiable
real function, the extension is jointly `C¹` in the base point and
increment.

The proof writes

`dslope f a (a + h) = ∫ t in 0..1, deriv f (a + t * h)`.

This representation removes the apparent singularity at `h = 0`. Regularity
then follows by differentiating the fixed-interval integral with respect to
the two parameters.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Scalar

open Set

/-- A divided difference along an affine segment is the average derivative
along that segment. The identity includes the zero-increment case. -/
theorem dslope_add_eq_integral_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a h : ℝ) :
    dslope f a (a + h) =
      ∫ t in (0 : ℝ)..1, deriv f (a + t * h) := by
  by_cases hh : h = 0
  · subst h
    simp
  have hcont :
      ContinuousOn
        (fun t : ℝ ↦ deriv f (a + t • h)) (Icc 0 1) :=
    (hf.continuous_deriv_one.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  have hderiv :
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt f (deriv f (a + t • h)) (a + t • h) :=
    fun t _ ↦ (hf.differentiable one_ne_zero (a + t • h)).hasDerivAt
  have hftc :=
    intervalIntegral.integral_unitInterval_deriv_eq_sub hcont hderiv
  have hslope := sub_smul_dslope f a (a + h)
  simp only [add_sub_cancel_left, smul_eq_mul] at hftc hslope
  apply mul_left_cancel₀ hh
  calc
    h * dslope f a (a + h) = f (a + h) - f a := hslope
    _ = h * ∫ t in (0 : ℝ)..1, deriv f (a + t * h) := hftc.symm

/-- A function with everywhere positive derivative has positive differentiable
slope between every pair of endpoints, including equal endpoints. -/
theorem dslope_pos_of_deriv_pos
    {f : ℝ → ℝ} (hf : ∀ x, 0 < deriv f x) (a b : ℝ) :
    0 < dslope f a b := by
  have hmono : StrictMono f :=
    strictMono_of_deriv_pos hf
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [dslope_of_ne f hab.ne']
    exact (slope_pos_iff_of_le hab.le).2 (hmono hab)
  · simpa using hf a
  · rw [dslope_of_ne f hba.ne, slope_comm f a b]
    exact (slope_pos_iff_of_le hba.le).2 (hmono hba)

private def segmentIntegrand (f : ℝ → ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  deriv f (p.1.1 + p.2 * p.1.2)

private def segmentParameterFDeriv (f : ℝ → ℝ)
    (x : ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (segmentIntegrand f) (x, t)).comp
    (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)

private theorem contDiff_segmentIntegrand
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (segmentIntegrand f) := by
  have hderiv : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  apply hderiv.comp
  fun_prop

private theorem continuous_segmentParameterFDeriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous
      (Function.uncurry (segmentParameterFDeriv f)) := by
  have hcont :
      Continuous (fderiv ℝ (segmentIntegrand f)) :=
    (contDiff_segmentIntegrand hf).continuous_fderiv one_ne_zero
  change Continuous
    (fun p : (ℝ × ℝ) × ℝ ↦
      (fderiv ℝ (segmentIntegrand f) p).comp
        (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ))
  fun_prop

private theorem hasFDerivAt_segmentIntegrand_parameter
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (x : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt
      (fun y : ℝ × ℝ ↦ segmentIntegrand f (y, t))
      (segmentParameterFDeriv f x t) x := by
  exact
    ((contDiff_segmentIntegrand hf).differentiable one_ne_zero
      (x, t)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

private def segmentAverage (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, segmentIntegrand f (x, t)

private def segmentAverageFDeriv
    (f : ℝ → ℝ) (x : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, segmentParameterFDeriv f x t

private theorem contDiff_segmentAverage
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (segmentAverage f) := by
  have hintegrand :
      Continuous (segmentIntegrand f) :=
    (contDiff_segmentIntegrand hf).continuous
  have hparameter :
      Continuous
        (Function.uncurry (segmentParameterFDeriv f)) :=
    continuous_segmentParameterFDeriv hf
  have haverageDerivative :
      Continuous (segmentAverageFDeriv f) := by
    exact
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hparameter 0 1
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨segmentAverageFDeriv f, haverageDerivative, ?_⟩
  intro x
  have hcompact :
      IsCompact
        (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ :=
    hcompact.exists_bound_of_continuousOn
      hparameter.continuousOn
  apply
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.closedBall x 1) (bound := fun _ ↦ C)
      (Metric.closedBall_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall fun y ↦
      (hintegrand.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact
      (hintegrand.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact
      (hparameter.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ht y hy ↦ by
      apply hC (y, t)
      refine ⟨hy, ?_⟩
      rw [← uIcc_of_le zero_le_one]
      exact uIoc_subset_uIcc ht
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ y _ ↦
      hasFDerivAt_segmentIntegrand_parameter hf y t

/-- If `f` is `C²`, then `(a, h) ↦ dslope f a (a + h)` is jointly `C¹`.

This is the regular extension of the secant slope in base-point/increment
coordinates, including the diagonal `h = 0`. -/
theorem contDiff_dslope_add
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1
      (fun x : ℝ × ℝ ↦ dslope f x.1 (x.1 + x.2)) := by
  have hregularity : ContDiff ℝ 1 f :=
    hf.of_le (by norm_num)
  have heq :
      (fun x : ℝ × ℝ ↦ dslope f x.1 (x.1 + x.2)) =
        segmentAverage f := by
    funext x
    exact dslope_add_eq_integral_deriv hregularity x.1 x.2
  rw [heq]
  exact contDiff_segmentAverage hf

end PDE.Analysis.Scalar
