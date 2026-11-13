/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.DualMeasure
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Dual-valued measures associated to Bochner Lp functionals

A functional on `Lp F p μ` evaluates each constant vector on each measurable-set indicator.
These evaluations form an `F*`-valued measure. Countable additivity holds in the dual norm:
the construction factors through a continuous linear map from scalar `Lp`, so the
unconditional convergence of indicators applies directly.

The construction and absolute continuity hold for every normed space `F`. A strongly
measurable dual-valued density for this measure would require a Banach-valued
Radon–Nikodym theorem.
-/

@[expose] public noncomputable section

open Set Filter Function
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Evaluating a Bochner functional on scalar functions multiplied by a fixed vector,
with the vector left as the argument of a bounded functional. -/
def scalarTestL (Λ : StrongDual ℝ (Lp F p μ)) :
    Lp ℝ p μ →L[ℝ] StrongDual ℝ F :=
  (Λ.postcomp F).comp ((ContinuousLinearMap.lsmul ℝ ℝ (E := F)).flip.compLpL₂ p μ).flip

private theorem scalarTestL_indicator (Λ : StrongDual ℝ (Lp F p μ))
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : F) :
    scalarTestL Λ (indicatorConstLp p hs hμs (1 : ℝ)) c =
      Λ (indicatorConstLp p hs hμs c) := by
  change Λ (((ContinuousLinearMap.lsmul ℝ ℝ (E := F)).flip c).compLp
    (indicatorConstLp p hs hμs (1 : ℝ))) = _
  congr 1
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLp
    ((ContinuousLinearMap.lsmul ℝ ℝ (E := F)).flip c) (indicatorConstLp p hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)] with x hx h1 hc
  rw [hx, h1, hc]
  by_cases hxs : x ∈ s <;> simp [hxs]

variable [IsFiniteMeasure μ]

/-- The dual-valued measure obtained by testing a Bochner Lp functional on indicators.
The finite exponent ensures countable additivity in the operator norm, not merely after
evaluation on each vector. -/
def dualVectorMeasure (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp F p μ)) :
    VectorMeasure α (StrongDual ℝ F) := by
  classical
  exact
    { measureOf' := fun s ↦
        if hs : MeasurableSet s then
          scalarTestL Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ))
        else 0
      empty' := by simp
      not_measurable' := fun _ hs ↦ dite_eq_right hs
      m_iUnion' := by
        intro s hs hdisj
        simpa only [dite_eq_left (MeasurableSet.iUnion hs), dite_eq_left (hs _)] using
          (scalarTestL Λ).hasSum (hasSum_indicatorConstLp (μ := μ) hp hs hdisj (1 : ℝ)) }

/-- The physical value of the measure on a measurable set and a vector. -/
@[simp] theorem dualVectorMeasure_apply (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp F p μ)) {s : Set α} (hs : MeasurableSet s) (c : F) :
    dualVectorMeasure hp Λ s c =
      Λ (indicatorConstLp p hs (measure_ne_top μ s) c) := by
  classical
  simp only [dualVectorMeasure, VectorMeasure.coe_mk, dite_eq_left hs]
  exact scalarTestL_indicator Λ hs _ c

/-- A quantitative bound on each measurable-set value, valid also for `p = 1`. -/
theorem norm_dualVectorMeasure_le (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp F p μ)) {s : Set α} (hs : MeasurableSet s) :
    ‖dualVectorMeasure hp Λ s‖ ≤ ‖Λ‖ * μ.real s ^ (1 / p.toReal) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro c
  rw [dualVectorMeasure_apply hp Λ hs]
  calc
    ‖Λ (indicatorConstLp p hs (measure_ne_top μ s) c)‖ ≤
        ‖Λ‖ * ‖indicatorConstLp p hs (measure_ne_top μ s) c‖ := Λ.le_opNorm _
    _ ≤ ‖Λ‖ * (‖c‖ * μ.real s ^ (1 / p.toReal)) :=
      mul_le_mul_of_nonneg_left norm_indicatorConstLp_le (norm_nonneg Λ)
    _ = (‖Λ‖ * μ.real s ^ (1 / p.toReal)) * ‖c‖ := by ring

/-- Null sets have zero dual-valued measure. -/
theorem dualVectorMeasure_absolutelyContinuous (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp F p μ)) :
    dualVectorMeasure hp Λ ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun s hs hzero ↦ ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (Fact.out))) hp
  simpa only [measureReal_def, hzero, ENNReal.toReal_zero,
    Real.zero_rpow (by positivity : 1 / p.toReal ≠ 0), mul_zero] using
    norm_dualVectorMeasure_le hp Λ hs

end MeasureTheory.Lp
