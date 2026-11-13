/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of primitives with an infinite endpoint

Only the relevant half-lines need be integrable. Subtracting the value at a
fixed finite endpoint reduces the derivative to the ordinary fundamental
theorem of calculus.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous integrand integrable on every left half-line has the usual
derivative for its primitive from negative infinity. -/
theorem hasDerivAt_integral_Iic {f : ℝ → E} (hf : Continuous f)
    (hint : ∀ a, IntegrableOn f (Iic a)) (x : ℝ) :
    HasDerivAt (fun t ↦ ∫ s in Iic t, f s) (f x) x := by
  have heq : (fun t ↦ ∫ s in Iic t, f s) =
      fun t ↦ (∫ s in (0 : ℝ)..t, f s) + ∫ s in Iic (0 : ℝ), f s := by
    funext t
    exact eq_add_of_sub_eq (intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint t))
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).add_const _

/-- Inside an integrable half-line, continuity at the moving endpoint suffices
to differentiate the tail. No regularity elsewhere or integrability to the left
of the half-line is required. -/
theorem hasDerivAt_integral_Ioi {f : ℝ → E} {a x : ℝ}
    (hint : IntegrableOn f (Ioi a)) (hx : a < x) (hf : ContinuousAt f x) :
    HasDerivAt (fun t ↦ ∫ s in Ioi t, f s) (-f x) x := by
  have hi : IntervalIntegrable f volume a x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hm : StronglyMeasurableAtFilter f (𝓝 x) :=
    ⟨Ioi a, Ioi_mem_nhds hx, hint.aestronglyMeasurable⟩
  apply ((intervalIntegral.integral_hasDerivAt_right hi hm hf).const_sub
    (∫ s in Ioi a, f s)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with t ht
  exact eq_sub_of_add_eq' (intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi ht.le)))

end PDE.Analysis
