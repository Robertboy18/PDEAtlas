/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interval integrals of bounded integrands with a singular end point

Pointwise forms of the dominated convergence theorems for an integral `∫ x in a..b, F s x` with
`a ≤ b`. The integrand is continuous and bounded on the half-open interval `(a, b]`, the set
over which Mathlib takes the interval integral. Nothing is asked at `a`, so the integrand may
have no limit there, as a bounded product with the weight `cot x` at `x = 0`. The theorems
`PDE.continuousOn_setIntegral_of_compact_interval` and
`PDE.hasDerivAt_setIntegral_of_compact_interval` ask joint continuity on a compact closure
instead. The results are standard and follow no particular source.

## Main results

* `PDE.Analysis.intervalIntegrable_of_continuousOn_Ioo_of_norm_le`: a function that is
  continuous on the open interval `(a, b)` and dominated there by an interval integrable
  function is interval integrable on `[a, b]`.
* `PDE.Analysis.intervalIntegrable_of_norm_le`: a function that is continuous and bounded on
  `(a, b]` is interval integrable on `[a, b]`.
* `PDE.Analysis.continuousOn_integral_of_norm_le`: the integral over `[a, b]` is continuous in a
  parameter, for an integrand that is continuous in `x` on `(a, b]`, continuous in the
  parameter and bounded by a constant.
* `PDE.Analysis.hasDerivAt_integral_of_norm_le`: the integral over `[a, b]` is differentiable in
  a real or complex parameter, with the derivative under the integral sign, when the derivative
  of the integrand in the parameter is continuous in `x` on `(a, b]` and bounded by a constant
  near the parameter.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] {a b : ℝ}

/-- A function that is continuous on the open interval `(a, b)` and dominated there by an
interval integrable function is interval integrable on `[a, b]`. Nothing is asked at the two
end points. -/
theorem intervalIntegrable_of_continuousOn_Ioo_of_norm_le {G : ℝ → E} {g : ℝ → ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G (Ioo a b)) (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ x ∈ Ioo a b, ‖G x‖ ≤ g x) : IntervalIntegrable G volume a b := by
  refine hg.mono_fun' ?_ ?_
  · rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hG.aestronglyMeasurable measurableSet_Ioo
  · rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbound)

/-- A function that is continuous and bounded on `(a, b]` is interval integrable on `[a, b]`. -/
theorem intervalIntegrable_of_norm_le {F : ℝ → E} {C : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Ioc a b)) (hC : ∀ x ∈ Ioc a b, ‖F x‖ ≤ C) :
    IntervalIntegrable F volume a b :=
  intervalIntegrable_of_continuousOn_Ioo_of_norm_le hab (hF.mono Ioo_subset_Ioc_self)
    intervalIntegrable_const fun x hx ↦ hC x (Ioo_subset_Ioc_self hx)

variable [NormedSpace ℝ E]

/-- Continuity of an integral in a parameter, for an integrand that is continuous in `x` on
`(a, b]`, continuous in the parameter, and bounded by a constant. -/
theorem continuousOn_integral_of_norm_le {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {F : X → ℝ → E} {C : ℝ} {S : Set X} (hab : a ≤ b)
    (hF : ∀ s ∈ S, ContinuousOn (F s) (Ioc a b)) (hC : ∀ s ∈ S, ∀ x ∈ Ioc a b, ‖F s x‖ ≤ C)
    (hS : ∀ x ∈ Ioc a b, ContinuousOn (F · x) S) :
    ContinuousOn (fun s ↦ ∫ x in a..b, F s x) S := by
  simp only [intervalIntegral.integral_of_le hab]
  exact continuousOn_of_dominated (bound := fun _ ↦ C)
    (fun s hs ↦ (hF s hs).aestronglyMeasurable measurableSet_Ioc)
    (fun s hs ↦ (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (hC s hs)))
    (integrable_const C) ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hS))

/-- Differentiation of an integral in a real or complex parameter, for an integrand `F` with
derivative `F'` in the parameter: both are continuous in `x` on `(a, b]`, and `F` at the
parameter `t` and `F'` near `t` are bounded by constants. -/
theorem hasDerivAt_integral_of_norm_le {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    {F F' : 𝕜 → ℝ → E} {C C' : ℝ} {t : 𝕜} {S : Set 𝕜} (hab : a ≤ b) (hS : S ∈ 𝓝 t)
    (hF : ∀ s ∈ S, ContinuousOn (F s) (Ioc a b)) (hC : ∀ x ∈ Ioc a b, ‖F t x‖ ≤ C)
    (hF' : ContinuousOn (F' t) (Ioc a b)) (hC' : ∀ s ∈ S, ∀ x ∈ Ioc a b, ‖F' s x‖ ≤ C')
    (hderiv : ∀ s ∈ S, ∀ x ∈ Ioc a b, HasDerivAt (F · x) (F' s x) s) :
    HasDerivAt (fun s ↦ ∫ x in a..b, F s x) (∫ x in a..b, F' t x) t := by
  have hI : uIoc a b = Ioc a b := uIoc_of_le hab
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ ↦ C') hS ?_
    (intervalIntegrable_of_norm_le hab (hF t (mem_of_mem_nhds hS)) hC) ?_ ?_
    intervalIntegrable_const ?_).2
  · filter_upwards [hS] with s hs
    rw [hI]
    exact (hF s hs).aestronglyMeasurable measurableSet_Ioc
  · rw [hI]
    exact hF'.aestronglyMeasurable measurableSet_Ioc
  · exact Eventually.of_forall fun x hx s hs ↦ hC' s hs x (hI ▸ hx)
  · exact Eventually.of_forall fun x hx s hs ↦ hderiv s hs x (hI ▸ hx)

end PDE.Analysis
