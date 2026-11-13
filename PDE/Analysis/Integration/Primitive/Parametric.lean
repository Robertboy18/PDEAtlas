/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Backward primitives with spatial parameters

The integral from the current time to a fixed terminal time is jointly smooth
when its integrand is. Affine change of variables reduces the moving interval
to a fixed interval, including when its length vanishes or changes sign.
The time derivative is the negative integrand.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

universe u v

variable {X : Type u} {E : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrate from the current time to a fixed terminal time. -/
def backwardPrimitive (φ : ℝ × X → E) (R : ℝ) (p : ℝ × X) : E :=
  ∫ s in p.1..R, φ (s, p.2)

/-- Affine reparametrization is valid also when the interval has zero or
negative length. -/
theorem backwardPrimitive_eq_unitInterval (φ : ℝ × X → E) (R : ℝ) (p : ℝ × X) :
    backwardPrimitive φ R p =
      ∫ s in (0 : ℝ)..1, (R - p.1) • φ (p.1 + (R - p.1) * s, p.2) := by
  rw [intervalIntegral.integral_smul]
  simpa [backwardPrimitive] using
    (intervalIntegral.smul_integral_comp_add_mul
      (fun s ↦ φ (s, p.2)) (a := 0) (b := 1) (R - p.1) p.1).symm

/-- A backward primitive preserves every finite order of joint smoothness,
and smoothness of all orders. -/
theorem contDiff_backwardPrimitive [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace E]
    {n : ℕ∞} {φ : ℝ × X → E} (hφ : ContDiff ℝ n φ) (R : ℝ) :
    ContDiff ℝ n (backwardPrimitive φ R) := by
  have h : ContDiff ℝ n (fun z : (ℝ × X) × ℝ ↦
      (R - z.1.1) • φ (z.1.1 + (R - z.1.1) * z.2, z.1.2)) := by
    apply ContDiff.smul
    · fun_prop
    · apply hφ.comp
      fun_prop
  have heq : backwardPrimitive φ R = fun p : ℝ × X ↦
      ∫ s in (0 : ℝ)..1, (R - p.1) • φ (p.1 + (R - p.1) * s, p.2) :=
    funext (backwardPrimitive_eq_unitInterval φ R)
  rw [heq]
  exact contDiff_intervalIntegral h 0 1

/-- Differentiating in the initial endpoint gives the negative integrand,
with no restriction on the relative order of the two endpoints. -/
theorem hasDerivAt_backwardPrimitive_time [TopologicalSpace X] [CompleteSpace E]
    {φ : ℝ × X → E} (hφ : Continuous φ) (R t : ℝ) (x : X) :
    HasDerivAt (fun s ↦ backwardPrimitive φ R (s, x)) (-φ (t, x)) t := by
  have hc : Continuous (fun s ↦ φ (s, x)) :=
    hφ.comp (continuous_id.prodMk continuous_const)
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable t R)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The Fréchet derivative in the time direction agrees with the
endpoint derivative. -/
theorem fderiv_backwardPrimitive_time [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace E]
    {φ : ℝ × X → E} (hφ : ContDiff ℝ 1 φ) (R : ℝ) (p : ℝ × X) :
    fderiv ℝ (backwardPrimitive φ R) p (1, 0) = -φ p := by
  have hd := ((contDiff_backwardPrimitive hφ R).differentiable one_ne_zero p).hasFDerivAt
  have hs := hd.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hs.unique (hasDerivAt_backwardPrimitive_time hφ.continuous R p.1 p.2)

/-- If the integrand vanishes on a spatial fiber, so does its primitive. -/
theorem backwardPrimitive_eq_zero_of_fiber (φ : ℝ × X → E) (R t : ℝ) (x : X)
    (hx : ∀ s, φ (s, x) = 0) :
    backwardPrimitive φ R (t, x) = 0 := by
  simp [backwardPrimitive, hx]

/-- After a terminal time beyond the support, the primitive vanishes. -/
theorem backwardPrimitive_eq_zero_of_le (φ : ℝ × X → E) (R t : ℝ) (x : X)
    (ht : R ≤ t) (hφ : ∀ s, R ≤ s → φ (s, x) = 0) :
    backwardPrimitive φ R (t, x) = 0 := by
  rw [backwardPrimitive, intervalIntegral.integral_of_ge ht]
  rw [setIntegral_eq_zero_of_forall_eq_zero]
  · simp
  · exact fun s hs ↦ hφ s hs.1.le

end PDE.Analysis
