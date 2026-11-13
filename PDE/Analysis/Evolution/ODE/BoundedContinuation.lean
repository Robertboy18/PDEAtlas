/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.MaximalContinuation

/-!
# Bounded finite-dimensional trajectories continue

For a finite-dimensional autonomous `C¹` ODE, a norm bound rules out a finite
maximal endpoint. The closed ball containing the trajectory is compact, so
continuity bounds the vector field there. The velocity is therefore integrable
on the finite time interval, and the integral continuation theorem
constructs an endpoint limit and extends the curve. Only a bound on `‖u‖` is
assumed, not on `‖f(u)‖`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A bounded solution of a finite-dimensional autonomous `C¹` ODE extends
past its right endpoint. The endpoint value is constructed, not assumed. -/
theorem exists_right_extension_of_norm_bounded
    {f : E → E} {u : ℝ → E} {a b M : ℝ}
    (hab : a < b)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hbound : ∀ t ∈ Ioo a b, ‖u t‖ ≤ M)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∃ c > b, ∃ v : ℝ → E,
      (∀ t ∈ Ioo a b, v t = u t) ∧
      ∀ t ∈ Ioo a c, HasDerivAt v (f (v t)) t := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr
    (fun x ↦ (hf x).continuousAt)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn
    hfcont.continuousOn
  have hvelocity : ContinuousOn (fun t ↦ f (u t)) (Ioo a b) :=
    hfcont.comp_continuousOn (HasDerivAt.continuousOn hu)
  have hint : IntegrableOn (fun t ↦ f (u t)) (Ioo a b) := by
    apply Integrable.of_bound (hvelocity.aestronglyMeasurable measurableSet_Ioo) C
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hC (u t) (by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t ht)
  exact exists_right_extension_of_integrableOn hab hu hint hf

end PDE.Analysis.Evolution
