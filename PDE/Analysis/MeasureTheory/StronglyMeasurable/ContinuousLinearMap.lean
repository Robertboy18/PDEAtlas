/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Measurable operators with finite-dimensional domain

Measurability on each fixed vector implies operator-norm strong measurability when the domain
is finite dimensional. A finite basis expresses the operator as a finite sum of rank-one maps.
-/

@[expose] public section

open MeasureTheory

namespace ContinuousLinearMap

/-- For a finite-dimensional domain, strong measurability can be checked on evaluations. -/
theorem aestronglyMeasurable_of_forall_apply
    {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : α → E →L[ℝ] F}
    (hA : ∀ v, AEStronglyMeasurable (fun t ↦ A t v) μ) :
    AEStronglyMeasurable A μ := by
  let b := Module.finBasis ℝ E
  let c := fun i ↦ (ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap
  have hsum : AEStronglyMeasurable
      (fun t ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ E F (c i) (A t (b i))) μ := by
    simpa only [Finset.sum_fn] using
      Finset.aestronglyMeasurable_sum Finset.univ fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ E F (c i)).continuous.comp_aestronglyMeasurable
        (hA (b i))
  apply hsum.congr
  filter_upwards with t
  ext v
  simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
  change (∑ i, b.repr v i • A t (b i)) = A t v
  simpa only [map_sum, map_smul] using congrArg (A t) (b.sum_repr v)

end ContinuousLinearMap
