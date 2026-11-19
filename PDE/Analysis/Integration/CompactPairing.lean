/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# Integrable compact inner-product pairings

A locally integrable field pairs integrably with a continuous, compactly
supported test field, with the pointwise inner product as the integrand.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace MeasureTheory

/-- A continuous compactly supported vector test pairs integrably with a
locally integrable vector field. Completeness of the state space is unnecessary. -/
theorem LocallyIntegrable.integrable_inner_right_of_hasCompactSupport
    {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [T2Space X] [SecondCountableTopology X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure X} {u ψ : X → E} (hu : LocallyIntegrable u μ)
    (hψ : Continuous ψ) (hsupport : HasCompactSupport ψ) :
    Integrable (fun x ↦ ⟪u x, ψ x⟫_ℝ) μ := by
  have hun : LocallyIntegrable (fun x ↦ ‖u x‖) μ :=
    locallyIntegrableOn_univ.mp (hu.locallyIntegrableOn Set.univ).norm
  have hdom := hun.integrable_smul_left_of_hasCompactSupport hψ.norm hsupport.norm
  apply hdom.mono' (hu.aestronglyMeasurable.inner hψ.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa only [smul_eq_mul, mul_comm] using norm_inner_le_norm (u x) (ψ x)

end MeasureTheory
