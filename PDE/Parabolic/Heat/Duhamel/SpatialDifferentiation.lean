/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Parabolic.Heat.Duhamel.Representation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Spatial differentiation of Duhamel's formula

Two applications of Mathlib's dominated differentiation theorem pass a mixed spatial
derivative through the source-time integral. The domination assumptions concern the
full derivatives of the heat evolution and of its first coordinate derivative;
evaluating those derivatives in the chosen coordinates also proves integrability.
-/

@[expose] public section

open PDE (partialDeriv)

namespace HeatEquation

open scoped Pointwise Topology Interval
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- Local domination data for two spatial differentiations of Duhamel's formula.

The heat evolution of each source slice and its first derivative in coordinate `j` satisfy
Mathlib's dominated differentiation hypotheses on `S`. The bounds are uniform in the spatial
point, so the same data apply at every point of `S` and in every outer coordinate. -/
structure DuhamelSpatialDomination (f : ℝ^(n + 1) → ℝ) (t : ℝ) (j : Fin n)
    (S : Set (ℝ^n)) (firstBound secondBound : ℝ → ℝ) : Prop where
  /-- Measurability of the heat evolution in source time. -/
  measurable : ∀ z ∈ S, AEStronglyMeasurable
    (fun s ↦ initialValueSolution (fun y ↦ f (timeSpaceCons s y)) z (t - s))
    (volume.restrict (Ι 0 t))
  /-- Integrability of the heat evolution in source time. -/
  integrable : ∀ z ∈ S, IntervalIntegrable
    (fun s ↦ initialValueSolution (fun y ↦ f (timeSpaceCons s y)) z (t - s)) volume 0 t
  /-- Measurability of the first spatial Fréchet derivative in source time. -/
  fderiv_measurable : ∀ z ∈ S, AEStronglyMeasurable
    (fun s ↦ fderiv ℝ (fun w ↦
      initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s)) z)
    (volume.restrict (Ι 0 t))
  /-- Spatial differentiability for almost every source time. -/
  differentiable : ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ z ∈ S,
    DifferentiableAt ℝ
      (fun w ↦ initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s)) z
  /-- A uniform bound for the first spatial Fréchet derivative. -/
  fderiv_bound : ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ z ∈ S,
    ‖fderiv ℝ (fun w ↦
      initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s)) z‖ ≤ firstBound s
  /-- Integrability of the first derivative bound. -/
  firstBound_integrable : IntervalIntegrable firstBound volume 0 t
  /-- Measurability of the Fréchet derivative of the first coordinate derivative. -/
  partial_fderiv_measurable : ∀ z ∈ S, AEStronglyMeasurable
    (fun s ↦ fderiv ℝ (∂[j] (fun w ↦
      initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s))) z)
    (volume.restrict (Ι 0 t))
  /-- Differentiability of the first coordinate derivative for almost every source time. -/
  partial_differentiable : ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ z ∈ S,
    DifferentiableAt ℝ (∂[j] (fun w ↦
      initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s))) z
  /-- A uniform bound for the Fréchet derivative of the first coordinate derivative. -/
  partial_fderiv_bound : ∀ᵐ s ∂volume.restrict (Ι 0 t), ∀ z ∈ S,
    ‖fderiv ℝ (∂[j] (fun w ↦
      initialValueSolution (fun y ↦ f (timeSpaceCons s y)) w (t - s))) z‖ ≤ secondBound s
  /-- Integrability of the second derivative bound. -/
  secondBound_integrable : IntervalIntegrable secondBound volume 0 t

/-- Two dominated Fréchet differentiations prove that a mixed second derivative commutes
with the Duhamel source-time integral.

The hypotheses are the local domination conditions of Mathlib's parametric-integral
theorem, for the heat evolution of each source slice and its first coordinate derivative.
Measurability and integrable norm bounds give integrability of both covector fields, and
evaluation on the coordinate vector gives the scalar integrability needed at each step. -/
theorem nonhomogeneousSolution_secondPartial_of_dominated
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) (i j : Fin n)
    (S : Set (ℝ^n)) (hS : IsOpen S) (hx : x ∈ S)
    (firstBound secondBound : ℝ → ℝ)
    (hdom : DuhamelSpatialDomination f t j S firstBound secondBound) :
    (∂[i]
        (fun z ↦
          (∂[j]
            (fun x' : ℝ^n ↦
              nonhomogeneousSolution (n := n) f x' t))
            z))
        x =
      ∫ s in Set.Icc 0 t,
        (∂[i]
          (fun z ↦
            (∂[j]
              (fun x' : ℝ^n ↦
                initialValueSolution (n := n)
                  (fun y : ℝ^n ↦
                    f (timeSpaceCons (n := n) s y))
                  x' (t - s)))
              z))
          x ∧
      IntervalIntegrable
        (fun s ↦
          (∂[i]
            (fun z ↦
              (∂[j]
                (fun x' : ℝ^n ↦
                  initialValueSolution (n := n)
                    (fun y : ℝ^n ↦
                      f (timeSpaceCons (n := n) s y))
                    x' (t - s)))
                z))
            x)
        volume 0 t := by
  rcases hdom with ⟨hF_meas, hF_int, hDF_meas, hF_diff, hDF_bound, hfirstBound,
    hDC_meas, hC_diff, hDC_bound, hsecondBound⟩
  let F : (ℝ^n) → ℝ → ℝ := fun z s ↦
    initialValueSolution (n := n) (fun y : (ℝ^n) ↦ f (timeSpaceCons (n := n) s y)) z (t - s)
  let C : (ℝ^n) → ℝ → ℝ := fun z s ↦ (∂[j] (F · s)) z
  let eval (k : Fin n) : ((ℝ^n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ))
  have hDF_int (z : ℝ^n) (hz : z ∈ S) :
      IntervalIntegrable (fun s ↦ fderiv ℝ (F · s) z) volume 0 t :=
    hfirstBound.mono_fun' (hDF_meas z hz) (hDF_bound.mono fun s hs ↦ hs z hz)
  have hDC_int : IntervalIntegrable (fun s ↦ fderiv ℝ (C · s) x) volume 0 t :=
    hsecondBound.mono_fun' (hDC_meas x hx) (hDC_bound.mono fun s hs ↦ hs x hx)
  have hC_int (z : ℝ^n) (hz : z ∈ S) : IntervalIntegrable (C z) volume 0 t :=
    ⟨(eval j).integrable_comp (hDF_int z hz).1, (eval j).integrable_comp (hDF_int z hz).2⟩
  have hfirst (z : ℝ^n) (hz : z ∈ S) : HasFDerivAt (fun z ↦ ∫ s in (0 : ℝ)..t, F z s)
      (∫ s in (0 : ℝ)..t, fderiv ℝ (F · s) z) z :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (hS.mem_nhds hz)
      (Filter.eventually_of_mem (hS.mem_nhds hz) hF_meas) (hF_int z hz) (hDF_meas z hz)
      ((ae_restrict_iff' measurableSet_uIoc).1 hDF_bound) hfirstBound
      ((ae_restrict_iff' measurableSet_uIoc).1
        (hF_diff.mono fun s hs z hz ↦ (hs z hz).hasFDerivAt))
  have hsecond : HasFDerivAt (fun z ↦ ∫ s in (0 : ℝ)..t, C z s)
      (∫ s in (0 : ℝ)..t, fderiv ℝ (C · s) x) x :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (hS.mem_nhds hx)
      (Filter.eventually_of_mem (hS.mem_nhds hx) fun z hz ↦
        (intervalIntegrable_iff.mp (hC_int z hz)).aestronglyMeasurable)
      (hC_int x hx) (hDC_meas x hx) ((ae_restrict_iff' measurableSet_uIoc).1 hDC_bound)
      hsecondBound ((ae_restrict_iff' measurableSet_uIoc).1
        (hC_diff.mono fun s hs z hz ↦ (hs z hz).hasFDerivAt))
  have hpartial : (fun z ↦ (∂[j] (fun z ↦ ∫ s in (0 : ℝ)..t, F z s)) z) =ᶠ[𝓝 x]
      fun z ↦ ∫ s in (0 : ℝ)..t, C z s := by
    filter_upwards [hS.mem_nhds hx] with z hz
    unfold partialDeriv
    rw [(hfirst z hz).fderiv, ContinuousLinearMap.intervalIntegral_apply (hDF_int z hz)]
    rfl
  have houter : (fun z : (ℝ^n) ↦ nonhomogeneousSolution (n := n) f z t) =
      fun z ↦ ∫ s in (0 : ℝ)..t, F z s := by
    funext z
    rw [nonhomogeneousSolution_eq_integral_initialValueSolution (n := n) f z t ht,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le]
  refine ⟨?_, (eval i).integrable_comp hDC_int.1, (eval i).integrable_comp hDC_int.2⟩
  rw [houter, partialDeriv, (hsecond.congr_of_eventuallyEq hpartial).fderiv,
    ContinuousLinearMap.intervalIntegral_apply hDC_int, intervalIntegral.integral_of_le ht.le,
    ← integral_Icc_eq_integral_Ioc]
  rfl

end HeatEquation
