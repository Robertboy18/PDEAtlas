/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts with singular endpoints

Integration by parts on an open bounded interval. The factors need only be
differentiable in the interior, while their product is controlled by one-sided limits at the
endpoints. This is useful when one factor contains a weight that is singular at the boundary but
the full boundary product still has a finite limit.

We also prove the two compact-support integration-by-parts formulas with no boundary term:
on the whole line (`integral_mul_deriv_eq_neg_deriv_mul_of_compactSupport`) and on a half-line
`(a, ∞)` when the first factor vanishes at `a`
(`integral_Ioi_mul_deriv_eq_neg_deriv_mul_of_left_eq_zero`).
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Interval Topology

section NormedRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {a b : ℝ} {left right : A}
variable {u v u' v' : ℝ → A}

/-- The fundamental theorem for the derivative of a product on an open bounded interval.

The functions may be singular at the endpoints: only the one-sided limits of their product are
used there. -/
theorem integral_Ioo_deriv_mul_eq_sub_of_tendsto
    (hab : a < b)
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hu'v : IntegrableOn (u' * v) (Ioo a b))
    (huv' : IntegrableOn (u * v') (Ioo a b))
    (ha : Tendsto (u * v) (𝓝[>] a) (𝓝 left))
    (hb : Tendsto (u * v) (𝓝[<] b) (𝓝 right)) :
    ∫ x in Ioo a b, u' x * v x + u x * v' x = right - left := by
  have hderiv :
      ∀ x ∈ Ioo a b,
        HasDerivAt (u * v) (u' x * v x + u x * v' x) x := by
    intro x hx
    simpa only [Pi.mul_apply] using (hu x hx).mul (hv x hx)
  have hint :
      IntervalIntegrable (fun x ↦ u' x * v x + u x * v' x) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
    exact hu'v.add huv'
  have hfundamental :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hab hderiv hint ha hb
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at hfundamental
  exact hfundamental

/-- Integration by parts on an open bounded interval with prescribed boundary-product limits. -/
theorem integral_Ioo_mul_deriv_eq_deriv_mul_of_tendsto
    (hab : a < b)
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hu'v : IntegrableOn (u' * v) (Ioo a b))
    (huv' : IntegrableOn (u * v') (Ioo a b))
    (ha : Tendsto (u * v) (𝓝[>] a) (𝓝 left))
    (hb : Tendsto (u * v) (𝓝[<] b) (𝓝 right)) :
    ∫ x in Ioo a b, u x * v' x =
      right - left - ∫ x in Ioo a b, u' x * v x := by
  have hproduct :=
    integral_Ioo_deriv_mul_eq_sub_of_tendsto hab hu hv hu'v huv' ha hb
  have hadd :
      (∫ x in Ioo a b, u' x * v x + u x * v' x) =
        (∫ x in Ioo a b, u' x * v x) + ∫ x in Ioo a b, u x * v' x := by
    simpa only [Pi.mul_apply, Pi.add_apply] using integral_add hu'v huv'
  rw [hadd] at hproduct
  exact eq_sub_of_add_eq' hproduct

/-- Integration by parts when the boundary product vanishes at both singular endpoints. -/
theorem integral_Ioo_mul_deriv_eq_neg_deriv_mul
    (hab : a < b)
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hu'v : IntegrableOn (u' * v) (Ioo a b))
    (huv' : IntegrableOn (u * v') (Ioo a b))
    (ha : Tendsto (u * v) (𝓝[>] a) (𝓝 0))
    (hb : Tendsto (u * v) (𝓝[<] b) (𝓝 0)) :
    ∫ x in Ioo a b, u x * v' x = -∫ x in Ioo a b, u' x * v x := by
  simpa using
    integral_Ioo_mul_deriv_eq_deriv_mul_of_tendsto
      hab hu hv hu'v huv' ha hb

end NormedRing

section RealFunctions

variable {a : ℝ} {u v : ℝ → ℝ}

/-- Integration by parts on the whole line when the first factor is compactly supported. -/
theorem integral_mul_deriv_eq_neg_deriv_mul_of_compactSupport
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hcu : HasCompactSupport u) :
    (∫ z : ℝ, u z * deriv v z) = -∫ z : ℝ, deriv u z * v z := by
  have huv'_int : Integrable (fun z ↦ u z * deriv v z) :=
    Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul (hv.continuous_deriv le_rfl)) hcu.mul_right
  have hu'v_int : Integrable (fun z ↦ deriv u z * v z) :=
    Continuous.integrable_of_hasCompactSupport
      ((hu.continuous_deriv le_rfl).mul hv.continuous) hcu.deriv.mul_right
  have huv_int : Integrable (fun z ↦ u z * v z) :=
    Continuous.integrable_of_hasCompactSupport (hu.continuous.mul hv.continuous) hcu.mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun z _ ↦ hu.differentiable_one.differentiableAt.hasDerivAt)
    (fun z _ ↦ hv.differentiable_one.differentiableAt.hasDerivAt)
    huv'_int hu'v_int huv_int

/-- Integration by parts on `(a, ∞)` when the first factor is compactly
supported and vanishes at the finite endpoint. -/
theorem integral_Ioi_mul_deriv_eq_neg_deriv_mul_of_left_eq_zero
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hcompact : HasCompactSupport u) (hua : u a = 0) :
    (∫ x in Ioi a, u x * deriv v x) =
      -∫ x in Ioi a, deriv u x * v x := by
  have huv : ContDiff ℝ 1 (fun x ↦ u x * v x) := hu.mul hv
  have hcompactProduct : HasCompactSupport (fun x ↦ u x * v x) :=
    hcompact.mul_right
  have hboundary := hcompactProduct.integral_Ioi_deriv_eq huv a
  have hu'v : IntegrableOn (fun x ↦ deriv u x * v x) (Ioi a) :=
    (Continuous.integrable_of_hasCompactSupport
      ((hu.continuous_deriv le_rfl).mul hv.continuous)
      hcompact.deriv.mul_right).integrableOn
  have huv' : IntegrableOn (fun x ↦ u x * deriv v x) (Ioi a) :=
    (Continuous.integrable_of_hasCompactSupport
      (hu.continuous.mul (hv.continuous_deriv le_rfl))
      hcompact.mul_right).integrableOn
  have hproductDerivative :
      (∫ x in Ioi a, deriv (fun y ↦ u y * v y) x) =
        ∫ x in Ioi a, deriv u x * v x + u x * deriv v x := by
    apply integral_congr_ae
    filter_upwards with x
    exact deriv_fun_mul hu.differentiable_one.differentiableAt
      hv.differentiable_one.differentiableAt
  rw [hproductDerivative, integral_add hu'v huv', hua, zero_mul, neg_zero] at hboundary
  linarith

end RealFunctions

end PDE.Analysis
