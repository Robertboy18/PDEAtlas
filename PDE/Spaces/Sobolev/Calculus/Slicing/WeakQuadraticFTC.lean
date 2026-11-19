/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative.ContinuousDerivative
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import CAS.ExactTactic

/-!
# The quadratic fundamental theorem for a continuous weak representative

The weak interval identity identifies the continuous function with an integral
primitive. Mathlib's product rule for absolutely continuous functions then
gives the quadratic identity on each finite interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- A continuous representative with a global weak derivative is absolutely
continuous on every finite interval. -/
theorem absolutelyContinuousOnInterval_of_continuous {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  have hg := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  have hprimitive := absolutelyContinuousOnInterval_intervalPrimitive hg 0 a b
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f 0) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hprimitive.add hconstant).congr
  intro x _hx
  change (∫ t in (0 : ℝ)..x, g t) + f 0 = f x
  rw [hweak.intervalIntegral_eq_sub hf 0 x, sub_add_cancel]

/-- The square increment equals twice the weak derivative pairing. -/
theorem integral_mul_eq_half_sq_sub {f g : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, f x * g x) = (f b ^ 2 - f a ^ 2) / 2 := by
  have hAC := hweak.absolutelyContinuousOnInterval_of_continuous hf a b
  have hparts := hAC.integral_deriv_mul_eq_sub hAC
  have heq : (∫ x in a..b, deriv f x * f x + f x * deriv f x) =
      2 * ∫ x in a..b, f x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hweak.ae_hasDerivAt_of_continuous hf] with x hx _hxab
    rw [hx.deriv]
    cas
  rw [heq] at hparts
  nlinarith [hparts]

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
