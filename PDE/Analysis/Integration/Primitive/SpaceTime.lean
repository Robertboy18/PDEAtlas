/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Primitive
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Time primitives with a measurable spatial parameter

Integrating a jointly measurable field from the initial time gives a jointly
measurable primitive. A uniform bound on the field controls every time slice
and gives its weak time derivative. The definition is zero for negative
time, so it also specifies the initial value without evaluating an almost
everywhere representative on the initial hyperplane.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrate in positive time, retaining the spatial parameter. -/
def forwardPrimitive (q : ℝ × X → E) (p : ℝ × X) : E :=
  ∫ s in Ioc 0 p.1, q (s, p.2)

/-- The primitive is zero at every nonpositive time, including the initial time. -/
theorem forwardPrimitive_eq_zero_of_nonpos (q : ℝ × X → E) {t : ℝ}
    (ht : t ≤ 0) (x : X) :
    forwardPrimitive q (t, x) = 0 := by
  simp [forwardPrimitive, Ioc_eq_empty (not_lt_of_ge ht)]

/-- Measurability in both variables follows by integrating the measurable
indicator of the region `0 < s ≤ t`. -/
theorem stronglyMeasurable_forwardPrimitive [MeasurableSpace X] {q : ℝ × X → E}
    (hq : StronglyMeasurable q) :
    StronglyMeasurable (forwardPrimitive q) := by
  let S : Set ((ℝ × X) × ℝ) := {z | 0 < z.2 ∧ z.2 ≤ z.1.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hq' : StronglyMeasurable (fun z : (ℝ × X) × ℝ ↦ q (z.2, z.1.2)) :=
    hq.comp_measurable (measurable_snd.prodMk measurable_fst.snd)
  have h := (hq'.indicator hS).integral_prod_right' (ν := volume)
  convert h using 1
  funext p
  rw [forwardPrimitive, ← integral_indicator measurableSet_Ioc]
  rfl

/-- The primitive has at most linear growth in positive time, with the same
bound on every spatial fiber. No spatial regularity is used. -/
theorem norm_forwardPrimitive_le {q : ℝ × X → E} (B : ℝ≥0)
    (hB : ∀ p, ‖q p‖ ≤ B) (p : ℝ × X) :
    ‖forwardPrimitive q p‖ ≤ B * max p.1 0 := by
  by_cases ht : 0 ≤ p.1
  · have h := norm_setIntegral_le_of_norm_le_const
      (f := fun s : ℝ ↦ q (s, p.2)) (s := Ioc 0 p.1)
      (μ := volume) (by simp) (fun s _ ↦ hB (s, p.2))
    simpa [forwardPrimitive, Real.volume_real_Ioc, max_eq_left ht] using h
  · have ht' : p.1 ≤ 0 := le_of_not_ge ht
    rw [show p = (p.1, p.2) from rfl, forwardPrimitive_eq_zero_of_nonpos q ht']
    simp [max_eq_right ht']

/-- The positive-time primitive is the usual interval primitive of the field
extended by zero to negative time. This identity also holds when `t ≤ 0`. -/
theorem forwardPrimitive_eq_intervalIntegral (q : ℝ × X → E) (t : ℝ) (x : X) :
    forwardPrimitive q (t, x) =
      ∫ s in 0..t, (Ioi 0).indicator (fun r ↦ q (r, x)) s := by
  by_cases ht : 0 ≤ t
  · rw [forwardPrimitive, intervalIntegral.integral_of_le ht]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp [hs.1]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [forwardPrimitive_eq_zero_of_nonpos q ht',
      intervalIntegral.integral_of_ge ht']
    rw [setIntegral_eq_zero_of_forall_eq_zero]
    · simp
    · intro s hs
      exact indicator_of_notMem (not_lt_of_ge hs.2) _

/-- Each time fiber of a bounded measurable field has the expected global
weak derivative after extension by zero to negative time. -/
theorem hasWeakTimeDerivativeOn_forwardPrimitive [MeasurableSpace X] [CompleteSpace E]
    {q : ℝ × X → E}
    (hq : StronglyMeasurable q) (B : ℝ≥0) (hB : ∀ p, ‖q p‖ ≤ B) (x : X) :
    Evolution.HasWeakTimeDerivativeOn univ (fun t ↦ forwardPrimitive q (t, x))
      ((Ioi 0).indicator (fun t ↦ q (t, x))) := by
  have hm : StronglyMeasurable ((Ioi 0).indicator (fun t ↦ q (t, x))) :=
    (hq.comp_measurable (measurable_id.prodMk measurable_const)).indicator measurableSet_Ioi
  have hb : ∀ t : ℝ, ‖(Ioi 0).indicator (fun s ↦ q (s, x)) t‖ ≤ B := by
    intro t
    by_cases ht : t ∈ Ioi 0
    · simpa [ht] using hB (t, x)
    · simp [ht]
  have hi := (memLp_top_of_bound (μ := volume) hm.aestronglyMeasurable (B : ℝ)
    (Filter.Eventually.of_forall hb)).locallyIntegrable (by simp)
  simpa only [forwardPrimitive_eq_intervalIntegral] using
    Evolution.hasWeakTimeDerivativeOn_intervalPrimitive hi 0

/-- Joint local integrability follows from the linear time-growth bound.
In particular, no continuity in the spatial parameter is required. -/
theorem locallyIntegrable_forwardPrimitive [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ : Measure (ℝ × X)) [IsLocallyFiniteMeasure μ]
    {q : ℝ × X → E} (hq : StronglyMeasurable q) (B : ℝ≥0)
    (hB : ∀ p, ‖q p‖ ≤ B) :
    LocallyIntegrable (forwardPrimitive q) μ := by
  have hc : Continuous (fun p : ℝ × X ↦ (B : ℝ) * max p.1 0) := by fun_prop
  apply hc.locallyIntegrable.mono (stronglyMeasurable_forwardPrimitive hq).aestronglyMeasurable
  filter_upwards with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg B.coe_nonneg (le_max_right _ _))]
    using norm_forwardPrimitive_le B hB p

end PDE.Analysis
