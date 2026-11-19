/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.SpatialContinuity
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Spatial derivatives of the Duhamel integral

We place the spatial derivatives on the source. Their bounds are independent of heat age,
so the differentiation argument remains valid as the heat age approaches zero.
-/

@[expose] public section

open PDE (partialDeriv)

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- Differentiate the Duhamel integral in space by integrating the heat evolution of the source
gradient. Uniform bounds on that gradient justify the interchange. -/
theorem hasFDerivAt_integral_initialValueSolution_space
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg1 : ∀ s, ContDiff ℝ 1 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (x : ℝ^n) (t : ℝ) :
    HasFDerivAt (fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s))
      (∫ s in 0..t, ∑ i : Fin n,
        initialValueSolution (∂[i] (g s)) x (t - s) •
          (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  let H : ℝ^n → ℝ → ℝ := fun z s ↦ initialValueSolution (g s) z (t - s)
  let D : ℝ^n → ℝ → ℝ^n →L[ℝ] ℝ := fun z s ↦
    ∑ i : Fin n, initialValueSolution (∂[i] (g s)) z (t - s) •
      (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)
  have hH : Continuous (Function.uncurry H) :=
    (continuous_initialValueSolution_family hg (fun p ↦ hbound p.1 p.2)).comp
      (continuous_snd.prodMk (continuous_fst.prodMk (continuous_const.sub continuous_snd)))
  have hD : Continuous (Function.uncurry D) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_initialValueSolution_family (hpartial i)
      (fun p ↦ hC i p.1 p.2)).comp
        (continuous_snd.prodMk
          (continuous_fst.prodMk (continuous_const.sub continuous_snd)))).smul continuous_const
  have hnorm (z : ℝ^n) (s : ℝ) :
      ‖D z s‖ ≤ ∑ i : Fin n, C i * ‖(EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact abs_initialValueSolution_le (∂[i] (g s)) ((hpartial i).comp
      (continuous_const.prodMk continuous_id))
      (fun y ↦ by simpa only [Real.norm_eq_abs] using hC i s y) z (t - s)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := H) (F' := D)
    (bound := fun _ ↦ ∑ i : Fin n, C i * ‖(EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)‖)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun z ↦
      (hH.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict)
    ((hH.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
    (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
    (Eventually.of_forall fun s _ z _ ↦ hnorm z s)
    (continuous_const.intervalIntegrable 0 t)
    (Eventually.of_forall fun s _ z _ ↦
      hasFDerivAt_initialValueSolution_space_source_all_time
        (g s) (hg1 s) (hgc s) z (t - s))

/-- The first coordinate derivative passes through the time integral and the heat evolution. -/
theorem partialDeriv_integral_initialValueSolution_eq_source
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg1 : ∀ s, ContDiff ℝ 1 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (x : ℝ^n) (t : ℝ) (i : Fin n) :
    (∂[i] (fun z ↦
      ∫ s in 0..t, initialValueSolution (g s) z (t - s))) x =
      ∫ s in 0..t, initialValueSolution (∂[i] (g s)) x (t - s) := by
  have hD : Continuous (fun s : ℝ ↦ ∑ j : Fin n,
      initialValueSolution (∂[j] (g s)) x (t - s) •
        (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ)) := by
    apply continuous_finsetSum
    intro j _
    exact ((continuous_initialValueSolution_family (hpartial j)
      (fun p ↦ hC j p.1 p.2)).comp
        (continuous_id.prodMk
          (continuous_const.prodMk (continuous_const.sub continuous_id)))).smul continuous_const
  rw [partialDeriv,
    (hasFDerivAt_integral_initialValueSolution_space
      g hg hg1 hgc hbound hpartial C hC x t).fderiv,
    ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 t)]
  simp

/-- Iterating the first derivative formula transfers any two coordinate derivatives to the source,
with no time derivative of the source. -/
theorem secondPartial_integral_initialValueSolution_eq_source
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (hsecond : ∀ i j : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2))
    (B : Fin n → Fin n → ℝ)
    (hB : ∀ i j s x, ‖(∂[i] (∂[j] (g s))) x‖ ≤ B i j)
    (x : ℝ^n) (t : ℝ) (i j : Fin n) :
    (∂[i] (∂[j] (fun z ↦
      ∫ s in 0..t, initialValueSolution (g s) z (t - s)))) x =
      ∫ s in 0..t, initialValueSolution (∂[i] (∂[j] (g s)))
        x (t - s) := by
  have hg1 (s : ℝ) : ContDiff ℝ 1 (g s) := (hg2 s).of_le (by norm_num)
  have heq : (∂[j] (fun z ↦
      ∫ s in 0..t, initialValueSolution (g s) z (t - s))) =
      fun z ↦ ∫ s in 0..t, initialValueSolution (∂[j] (g s)) z (t - s) :=
    funext fun z ↦ partialDeriv_integral_initialValueSolution_eq_source
      g hg hg1 hgc hbound hpartial C hC z t j
  rw [heq]
  exact partialDeriv_integral_initialValueSolution_eq_source
    (fun s ↦ (∂[j] (g s))) (hpartial j)
    (fun s ↦ PDE.contDiff_partialDeriv_of_succ (hg2 s))
    (fun s ↦ (hgc s).fderiv_apply ℝ (EuclideanSpace.single j 1))
    (hC j) (fun i ↦ hsecond i j) (fun i ↦ B i j) (fun i ↦ hB i j) x t i

/-- The spatial derivative of the Duhamel integral, expressed as the finite sum of its coordinate
derivatives. -/
theorem hasFDerivAt_integral_initialValueSolution_space_sum
    (g : ℝ → ℝ^n → ℝ) (hg : Continuous (Function.uncurry g))
    (hg1 : ∀ s, ContDiff ℝ 1 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hpartial : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2))
    (C : Fin n → ℝ) (hC : ∀ i s x, ‖(∂[i] (g s)) x‖ ≤ C i)
    (x : ℝ^n) (t : ℝ) :
    HasFDerivAt (fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s))
      (∑ i : Fin n,
        (∫ s in 0..t, initialValueSolution (∂[i] (g s)) x (t - s)) •
          (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  have hD := hasFDerivAt_integral_initialValueSolution_space
    g hg hg1 hgc hbound hpartial C hC x t
  convert hD using 1
  rw [← hD.fderiv, PDE.fderiv_eq_sum_partialDeriv_smul_proj]
  simp_rw [partialDeriv_integral_initialValueSolution_eq_source
    g hg hg1 hgc hbound hpartial C hC]

end HeatEquation
