/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import PDE.Analysis.Evolution.Time.FundamentalTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak derivatives of interval primitives

A locally integrable function has a continuous primitive, absolutely
continuous on every bounded interval. Lebesgue differentiation identifies
its derivative almost everywhere, so its weak derivative is the original
integrand. The base point only chooses the additive constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Local integrability suffices for local absolute continuity of an
interval primitive, with any fixed base point. -/
theorem absolutelyContinuousOnInterval_intervalPrimitive
    {g : ℝ → X} (hg : LocallyIntegrable g volume) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in c..x, g t) a b := by
  have hint (x y : ℝ) : IntervalIntegrable g volume x y :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hconstant : AbsolutelyContinuousOnInterval
      (fun _ : ℝ ↦ ∫ t in c..a, g t) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hfromA : AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in a..x, g t) a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
      (hint a b) Set.left_mem_uIcc
  apply (hconstant.add hfromA).congr
  intro x _hx
  exact intervalIntegral.integral_add_adjacent_intervals (hint c a) (hint a x)

/-- The interval primitive of a locally integrable function has that
function as its global weak derivative. -/
theorem hasWeakTimeDerivativeOn_intervalPrimitive
    [CompleteSpace X] {g : ℝ → X} (hg : LocallyIntegrable g volume) (c : ℝ) :
    HasWeakTimeDerivativeOn Set.univ (fun x ↦ ∫ t in c..x, g t) g := by
  have hcontinuous : Continuous (fun x ↦ ∫ t in c..x, g t) :=
    intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) c
  refine HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    hcontinuous.locallyIntegrable hg
    (absolutelyContinuousOnInterval_intervalPrimitive hg c) ?_
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx
  exact hx c

end PDE.Analysis.Evolution
