/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.WeakQuadraticFTC
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The second differentiated transport equation at weak H² regularity

For `V = ρ x + u`, the normalized De Gregorio equation is
`ω_t = V' ω - V ω'`. Its second spatial derivative has the conservative weak form
`r_t + (V r)' = V''' ω + V'' ω'`, where `r = ω''`.

The spatial identity `integral_transport_secondDerivative_test` uses continuous first
derivatives of vorticity and a weak second derivative. The velocity has two continuous
derivatives and a weak third derivative. Compact tests localize all products, so the
velocity may grow at infinity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution

namespace DeGregorio.Iteration

/-- A continuous weak derivative pair can be tested against compact C¹ functions.
Absolute continuity on a finite interval supplies integration by parts. -/
theorem integral_weakDerivative_mul_c1 {f g ψ : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, g x * ψ x) = -(∫ x, f x * deriv ψ x) := by
  obtain ⟨r, _, hr⟩ := hc.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  rw [Real.ball_zero_eq_Ioo] at hr
  have hs : Function.support ψ ⊆ Ioc (-r) r :=
    (subset_closure.trans hr).trans Ioo_subset_Ioc_self
  have hs' : Function.support (deriv ψ) ⊆ Ioc (-r) r :=
    (support_deriv_subset.trans hr).trans Ioo_subset_Ioc_self
  have hleft : Function.support (fun x ↦ g x * ψ x) ⊆ Ioc (-r) r :=
    (Function.support_mul_subset_right _ _).trans hs
  have hright : Function.support (fun x ↦ f x * deriv ψ x) ⊆ Ioc (-r) r :=
    (Function.support_mul_subset_right _ _).trans hs'
  have hneg : ψ (-r) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hx ↦ (lt_irrefl (-r)) (hr hx).1
  have hpos : ψ r = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hx ↦ (lt_irrefl r) (hr hx).2
  have hAC := hweak.absolutelyContinuousOnInterval_of_continuous hf (-r) r
  have hp := hAC.integral_mul_deriv_eq_deriv_mul
    hψ.contDiffOn.absolutelyContinuousOnInterval
  have heq : (∫ x in -r..r, deriv f x * ψ x) = ∫ x in -r..r, g x * ψ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hweak.ae_hasDerivAt_of_continuous hf] with x hx _
    rw [hx.deriv]
  rw [hneg, hpos, heq, intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at hp
  simpa only [mul_zero, sub_zero, zero_sub, neg_neg] using congrArg Neg.neg hp.symm

/-- A second weak derivative paired with a compact C² test is the base
function paired with the second derivative of the test. -/
theorem integral_weak_secondDerivative_test {w q r ψ : ℝ → ℝ}
    (hwq : HasWeakTimeDerivativeOn univ w q)
    (hqr : HasWeakTimeDerivativeOn univ q r)
    (hw : Continuous w) (hq : Continuous q)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, r x * ψ x) = ∫ x, w x * deriv (deriv ψ) x := by
  rw [integral_weakDerivative_mul_c1 hqr hq (hψ.of_le (by norm_num)) hc,
    integral_weakDerivative_mul_c1 hwq hw hψ.deriv' hc.deriv, neg_neg]

private theorem integrable_mul_compact {f ψ : ℝ → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ f x * ψ x) :=
  (hf.mul hψ).integrable_of_hasCompactSupport hc.mul_left

private theorem integrable_mul_mul_compact {f g ψ : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ f x * g x * ψ x) :=
  integrable_mul_compact (hf.mul hg) hψ hc

/-- The spatial commutator identity for the second derivative of the normalized
transport right-hand side. Both highest derivatives are weak: `r = ω''` and
`s = V'''`. -/
theorem integral_transport_secondDerivative_test
    {w V r s ψ : ℝ → ℝ}
    (hw : ContDiff ℝ 1 w) (hV : ContDiff ℝ 2 V)
    (hr : HasWeakTimeDerivativeOn univ (deriv w) r)
    (hs : HasWeakTimeDerivativeOn univ (deriv (deriv V)) s)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, (deriv V x * w x - V x * deriv w x) * deriv (deriv ψ) x) =
      (∫ x, V x * r x * deriv ψ x) +
        ∫ x, (s x * w x + deriv (deriv V) x * deriv w x) * ψ x := by
  have hq := hw.continuous_deriv le_rfl
  have hD : ContDiff ℝ 1 (deriv V) := hV.deriv'
  have hd := hD.continuous_deriv le_rfl
  have hψ' : ContDiff ℝ 1 (deriv ψ) := hψ.deriv'
  have hψ'' := hψ'.continuous_deriv le_rfl
  have hprod : deriv (fun x ↦ V x * deriv ψ x) =
      fun x ↦ deriv V x * deriv ψ x + V x * deriv (deriv ψ) x := by
    funext x
    exact (((hV.differentiable (by norm_num)) x).hasDerivAt.mul
      ((hψ'.differentiable one_ne_zero) x).hasDerivAt).deriv
  have hwp : deriv (fun x ↦ w x * ψ x) =
      fun x ↦ deriv w x * ψ x + w x * deriv ψ x := by
    funext x
    exact (((hw.differentiable one_ne_zero) x).hasDerivAt.mul
      ((hψ.differentiable (by norm_num)) x).hasDerivAt).deriv
  have hA := integral_weakDerivative_mul_c1 hr hq
    ((hV.of_le (by norm_num)).mul hψ') hc.deriv.mul_left
  rw [hprod] at hA
  simp_rw [mul_add, ← mul_assoc] at hA
  rw [integral_add
    (integrable_mul_mul_compact hq hD.continuous hψ'.continuous hc.deriv)
    (integrable_mul_mul_compact hq hV.continuous hψ'' hc.deriv.deriv)] at hA
  have hB : (∫ x, (deriv V x * w x) * deriv (deriv ψ) x) =
      -(∫ x, (deriv (deriv V) x * w x + deriv V x * deriv w x) * deriv ψ x) := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ ↦ ((hD.differentiable one_ne_zero x).hasDerivAt).mul
        ((hw.differentiable one_ne_zero x).hasDerivAt))
      (fun x _ ↦ (hψ'.differentiable one_ne_zero x).hasDerivAt)
    · exact integrable_mul_compact (hD.continuous.mul hw.continuous) hψ'' hc.deriv.deriv
    · exact integrable_mul_compact
        ((hd.mul hw.continuous).add (hD.continuous.mul hq)) hψ'.continuous hc.deriv
    · exact integrable_mul_compact (hD.continuous.mul hw.continuous) hψ'.continuous hc.deriv
  simp_rw [add_mul] at hB
  rw [integral_add
    (integrable_mul_mul_compact hd hw.continuous hψ'.continuous hc.deriv)
    (integrable_mul_mul_compact hD.continuous hq hψ'.continuous hc.deriv)] at hB
  have hC := integral_weakDerivative_mul_c1 hs hd
    (hw.mul (hψ.of_le (by norm_num))) hc.mul_left
  rw [hwp] at hC
  simp_rw [mul_add, ← mul_assoc] at hC
  rw [integral_add
    (integrable_mul_mul_compact hd hq hψ.continuous hc)
    (integrable_mul_mul_compact hd hw.continuous hψ'.continuous hc.deriv)] at hC
  have hsψ : Integrable (fun x ↦ s x * (w x * ψ x)) :=
    HasWeakTimeDerivativeOn.integrable_mul_test hs.locallyIntegrable_g
      (hw.continuous.mul hψ.continuous) hc.mul_left (subset_univ _)
  simp_rw [sub_mul, add_mul]
  rw [integral_sub
    (integrable_mul_mul_compact hD.continuous hw.continuous hψ'' hc.deriv.deriv)
    (integrable_mul_mul_compact hV.continuous hq hψ'' hc.deriv.deriv),
    integral_add (by simpa only [mul_assoc] using hsψ)
      (integrable_mul_mul_compact hd hq hψ.continuous hc)]
  simp_rw [mul_comm (r _), mul_comm (deriv w _) (V _),
    mul_comm (deriv w _) (deriv V _)] at hA
  linarith only [hA, hB, hC]

end DeGregorio.Iteration
