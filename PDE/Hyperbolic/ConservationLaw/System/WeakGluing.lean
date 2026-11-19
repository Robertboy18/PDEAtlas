/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Weak
import PDE.DistributionTheory.TestFunction

/-!
# Gluing weak solutions at a common state

Two weak solutions of the same conservation law can be combined when, at
each point of the domain, at least one of them equals a fixed common state.
The glued state

`u + v - common`

then agrees pointwise with one of the original solutions, and
its nonlinear flux satisfies the corresponding inclusion-exclusion identity

`flux (u + v - common) = flux u + flux v - flux common`.

This reduces the weak conservation identity to linearity of the Bochner
integral.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- Combine two states that share the value `common` pointwise. -/
def glueAtCommonState
    (common : ℝ^m) (u v : ℝ^2 → ℝ^m) :
    ℝ^2 → ℝ^m :=
  fun p ↦ u p + v p - common

/-- If two weak solutions meet at `common` pointwise, their
inclusion-exclusion gluing is again a weak solution.

The pointwise alternative is stronger than an almost-everywhere hypothesis,
but it is the natural form for explicit shock and rarefaction profiles.
-/
theorem IsWeakSolution.glue_at_common_state {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    {common : ℝ^m} (hu : IsWeakSolution flux U u) (hv : IsWeakSolution flux U v)
    (hcommon : ∀ p ∈ U, u p = common ∨ v p = common) :
    IsWeakSolution flux U (glueAtCommonState common u v) := by
  have hconstant := isWeakSolution_const (flux := flux) U common
  refine ⟨(show MeasureTheory.LocallyIntegrableOn (u + v - fun _ ↦ common) U MeasureTheory.volume
      from (hu.u_locallyIntegrable.add hv.u_locallyIntegrable).sub hconstant.u_locallyIntegrable),
    ((hu.flux_locallyIntegrable.add hv.flux_locallyIntegrable).sub
      (MeasureTheory.locallyIntegrableOn_const (flux common))).congr
      (MeasureTheory.ae_restrict_of_forall_mem U.isOpen.measurableSet fun p hp ↦ by
        rcases hcommon p hp with h | h <;> simp [glueAtCommonState, h]), fun φ ↦ ?_⟩
  have hIntegrand : weakIntegrand flux (glueAtCommonState common u v) φ = fun p ↦
      weakIntegrand flux u φ p + weakIntegrand flux v φ p -
        weakIntegrand flux (fun _ ↦ common) φ p := by
    funext p
    by_cases hp : p ∈ U
    · rcases hcommon p hp with h | h <;> simp [weakIntegrand, glueAtCommonState, h]
    · simp [weakIntegrand, φ.partialDeriv_eq_zero_of_notMem hp (0 : Fin 2),
        φ.partialDeriv_eq_zero_of_notMem hp (1 : Fin 2)]
  have huI := hu.integrable_weakIntegrand φ
  have hvI := hv.integrable_weakIntegrand φ
  rw [hIntegrand, MeasureTheory.integral_sub
      (f := fun p ↦ weakIntegrand flux u φ p + weakIntegrand flux v φ p) (huI.add hvI)
      (hconstant.integrable_weakIntegrand φ), MeasureTheory.integral_add huI hvI,
    hu.weak_eq φ, hv.weak_eq φ, hconstant.weak_eq φ]
  simp

end PDE.Hyperbolic.ConservationLaw.System
