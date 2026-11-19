/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Primitives of continuous quotients

The denominator need only be nonzero on the closed segment joining the fixed
base to the point of differentiation. The endpoints may have either order.
Along a scalar solution, the reciprocal primitive measures elapsed time.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- A continuous quotient has the expected primitive derivative when its denominator
is nonzero on the integration segment. Zeros outside that segment are allowed. -/
theorem hasDerivAt_integral_quotient {f d : ℝ → ℝ} {a y : ℝ}
    (hf : Continuous f) (hd : Continuous d)
    (hne : ∀ v ∈ uIcc a y, d v ≠ 0) :
    HasDerivAt (fun x ↦ ∫ v in a..x, f v / d v) (f y / d y) y := by
  have hint : IntervalIntegrable (fun v ↦ f v / d v) volume a y :=
    (hf.continuousOn.div hd.continuousOn hne).intervalIntegrable
  have hmeas : StronglyMeasurable (fun v ↦ f v / d v) :=
    (hf.measurable.div hd.measurable).stronglyMeasurable
  exact intervalIntegral.integral_hasDerivAt_right hint
    hmeas.stronglyMeasurableAtFilter
    (hf.continuousAt.div hd.continuousAt (hne y right_mem_uIcc))

/-- Along `X' = d(X) * c`, a reciprocal primitive minus `c * t` is constant.
Nonvanishing is required only on each signed integration segment. The time
interval is closed, including the degenerate case. -/
theorem integral_reciprocal_comp_sub_eq {d X : ℝ → ℝ} {base c a b : ℝ}
    (hd : Continuous d)
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (d (X t) * c) t)
    (hne : ∀ t ∈ Icc a b, ∀ v ∈ uIcc base (X t), d v ≠ 0) :
    ∀ t ∈ Icc a b,
      (∫ v in base..X t, 1 / d v) - c * t =
        (∫ v in base..X a, 1 / d v) - c * a := by
  have hzero (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s ↦ (∫ v in base..X s, 1 / d v) - c * s) 0 t := by
    have hnonzero : d (X t) ≠ 0 := hne t ht (X t) right_mem_uIcc
    have hp := (hasDerivAt_integral_quotient (f := fun _ : ℝ ↦ 1)
      (d := d) (a := base) (y := X t) continuous_const hd (hne t ht)).comp t (hX t ht)
    have hct : HasDerivAt (fun s : ℝ ↦ c * s) c t := hasDerivAt_const_mul c
    have hz := hp.fun_sub hct
    have hcancel : 1 / d (X t) * (d (X t) * c) - c = 0 := by
      rw [← mul_assoc, one_div_mul_cancel hnonzero, one_mul, sub_self]
    simpa only [Function.comp_def] using hz.congr_deriv hcancel
  exact constant_of_has_deriv_right_zero
    (fun t ht ↦ (hzero t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hzero t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)

end PDE.Analysis
