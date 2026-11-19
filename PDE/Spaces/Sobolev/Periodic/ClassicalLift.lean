/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.FundamentalCell
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Classical periodic derivatives in the Euclidean weak-derivative API

A continuous periodic function with a continuous coordinate derivative lifts to
a function with that weak derivative on Euclidean space. Compactly supported
tests make the integration by parts local; no global integrability of a periodic
function on Euclidean space is required.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology Distributions

namespace SobolevSpace.Periodic

/-- Euclidean coordinate lines project to the corresponding torus coordinate flow. -/
theorem toTorus_add_single {n : ℕ} (x : ℝ^n) (i : Fin n) (t : ℝ) :
    toTorus n (x + t • EuclideanSpace.single i 1) =
      toTorus n x + coordinateShift i t := by
  ext j
  by_cases h : j = i
  · subst j
    simp [toTorus, coordinateShift]
  · simp [toTorus, coordinateShift, h]

/-- A continuous coordinate derivative lifts to the canonical Euclidean weak derivative. -/
theorem hasWeakDerivativeOn_toTorus_of_continuous {n : ℕ}
    (u g : C(UnitAddTorus (Fin n), ℝ)) (i : Fin n)
    (hd : ∀ x t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t)) t) :
    HasWeakDerivativeOn univ [i] (fun x ↦ u (toTorus n x))
      (fun x ↦ g (toTorus n x)) := by
  have hu : Continuous (fun x ↦ u (toTorus n x)) :=
    u.continuous.comp (toTorus n).continuous
  have hg : Continuous (fun x ↦ g (toTorus n x)) :=
    g.continuous.comp (toTorus n).continuous
  refine ⟨hu.continuousOn.locallyIntegrableOn MeasurableSet.univ,
    hg.continuousOn.locallyIntegrableOn MeasurableSet.univ, ?_⟩
  intro φ _hφ
  have hφc := φ.contDiff.continuous
  have hdc : Continuous (∂[i] φ.toFun) :=
    (PDE.contDiff_top_partialDeriv φ.contDiff).continuous
  have hds : HasCompactSupport (∂[i] φ.toFun) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (ℝ^n))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (v := EuclideanSpace.single i 1)
    ((hg.mul hφc).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)
    ((hu.mul hdc).integrable_of_hasCompactSupport hds.mul_left)
    ((hu.mul hφc).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left)
    (fun x _ ↦ by
      change HasDerivAt (fun t ↦ u (toTorus n (x + t • EuclideanSpace.single i 1)))
        (g (toTorus n x)) 0
      simpa only [toTorus_add_single, coordinateShift_zero, add_zero] using
        hd (toTorus n x) 0)
    (fun x _ ↦
      (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.hasLineDerivAt _)
  simp only [domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul,
    ContinuousLinearMap.mul_apply'] at hparts ⊢
  convert! hparts using 1

end SobolevSpace.Periodic
