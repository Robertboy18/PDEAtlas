/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Two-state Riemann data

Scalar and system Riemann problems use the same step function, with the
right state assigned at the origin. Its finite range gives strong
measurability and local integrability for arbitrary normed state spaces.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Hyperbolic.ConservationLaw

variable {E : Type*}

/-- The step datum with left and right states separated at the origin. -/
def riemannData (left right : E) (x : ℝ) : E :=
  if x < 0 then left else right

/-- The datum is the left state at negative positions. -/
@[simp] theorem riemannData_of_neg (left right : E) {x : ℝ} (hx : x < 0) :
    riemannData left right x = left := ite_eq_left hx

/-- The datum is the right state at nonnegative positions. -/
@[simp] theorem riemannData_of_nonneg (left right : E) {x : ℝ} (hx : 0 ≤ x) :
    riemannData left right x = right := ite_eq_right (not_lt_of_ge hx)

/-- Equal states give constant data. -/
@[simp] theorem riemannData_self (u : E) :
    riemannData u u = fun _ : ℝ ↦ u := by
  funext x
  exact ite_self u

/-- The two-state datum is measurable for any measurable state space. -/
theorem measurable_riemannData [MeasurableSpace E] (left right : E) :
    Measurable (riemannData left right) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- Its finite range gives strong measurability without separability of
the ambient state space. -/
theorem stronglyMeasurable_riemannData [TopologicalSpace E] (left right : E) :
    StronglyMeasurable (riemannData left right) :=
  StronglyMeasurable.ite measurableSet_Iio stronglyMeasurable_const stronglyMeasurable_const

/-- The norm is bounded by the larger endpoint norm. -/
theorem norm_riemannData_le_max [NormedAddCommGroup E] (left right : E) (x : ℝ) :
    ‖riemannData left right x‖ ≤ max ‖left‖ ‖right‖ := by
  by_cases hx : x < 0
  · rw [riemannData_of_neg left right hx]
    exact le_max_left _ _
  · rw [riemannData_of_nonneg left right (le_of_not_gt hx)]
    exact le_max_right _ _

/-- Riemann data are locally integrable in any normed state space. -/
theorem locallyIntegrable_riemannData [NormedAddCommGroup E] (left right : E) :
    LocallyIntegrable (riemannData left right) volume :=
  locallyIntegrable_of_aestronglyMeasurable_norm_le_const
    (stronglyMeasurable_riemannData left right).aestronglyMeasurable
    ((norm_nonneg left).trans (le_max_left ‖left‖ ‖right‖))
    (Filter.Eventually.of_forall (norm_riemannData_le_max left right))

end PDE.Hyperbolic.ConservationLaw
