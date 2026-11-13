/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
public import PDE.Hyperbolic.ConservationLaw.System.WeakGluing
import PDE.DistributionTheory.TestFunction

/-!
# Gluing entropy solutions at a common state

Suppose two profiles satisfy the same entropy inequality and, at every point
of the domain, at least one profile equals a fixed common state. Their
inclusion-exclusion gluing then has entropy density and flux equal to the
corresponding inclusion-exclusion combinations.

The common state contributes zero tested entropy production, so linearity of
the integral preserves the inequality. The same argument applies to every
convex entropy pair and combines with weak gluing to preserve entropy weak
solutions.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- Gluing two profiles that meet at a common state preserves a specified
entropy inequality. -/
theorem SatisfiesEntropyInequalityFor.glue_at_common_state {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m} {common : ℝ^m} (hu : SatisfiesEntropyInequalityFor U u E)
    (hv : SatisfiesEntropyInequalityFor U v E) (hcommon : ∀ p ∈ U, u p = common ∨ v p = common) :
    SatisfiesEntropyInequalityFor U (glueAtCommonState common u v) E := by
  have hconstant := satisfiesEntropyInequalityFor_const E U common
  -- On `U` one of the two profiles is the common state.
  have hglue (f : ℝ^m → ℝ) (p : ℝ^2) (hp : p ∈ U) :
      f (u p) + f (v p) - f common = f (glueAtCommonState common u v p) := by
    rcases hcommon p hp with h | h <;> simp [glueAtCommonState, h]
  refine ⟨((hu.1.add hv.1).sub hconstant.1).congr
      (MeasureTheory.ae_restrict_of_forall_mem U.isOpen.measurableSet (hglue E.entropy)),
    ((hu.2.1.add hv.2.1).sub hconstant.2.1).congr
      (MeasureTheory.ae_restrict_of_forall_mem U.isOpen.measurableSet (hglue E.entropyFlux)),
    fun φ hφ ↦ ?_⟩
  have hIntegrand : entropyWeakIntegrand E (glueAtCommonState common u v) φ = fun p ↦
      entropyWeakIntegrand E u φ p + entropyWeakIntegrand E v φ p -
        entropyWeakIntegrand E (fun _ ↦ common) φ p := by
    funext p
    by_cases hp : p ∈ U
    · rcases hcommon p hp with h | h <;> simp [entropyWeakIntegrand, glueAtCommonState, h]
    · simp [entropyWeakIntegrand, φ.partialDeriv_eq_zero_of_notMem hp (0 : Fin 2),
        φ.partialDeriv_eq_zero_of_notMem hp (1 : Fin 2)]
  have huI := hu.integrable_entropyWeakIntegrand φ
  have hvI := hv.integrable_entropyWeakIntegrand φ
  rw [hIntegrand, MeasureTheory.integral_sub
      (f := fun p ↦ entropyWeakIntegrand E u φ p + entropyWeakIntegrand E v φ p) (huI.add hvI)
      (hconstant.integrable_entropyWeakIntegrand φ), MeasureTheory.integral_add huI hvI,
    integral_entropyWeakIntegrand_const_eq_zero E common φ, sub_zero]
  exact add_nonneg (hu.2.2 φ hφ) (hv.2.2 φ hφ)

/-- Gluing at a common state preserves all convex entropy inequalities. -/
theorem SatisfiesEntropyInequality.glue_at_common_state {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ^m} {common : ℝ^m} (hu : SatisfiesEntropyInequality flux U u)
    (hv : SatisfiesEntropyInequality flux U v) (hcommon : ∀ p ∈ U, u p = common ∨ v p = common) :
    SatisfiesEntropyInequality flux U (glueAtCommonState common u v) :=
  fun E ↦ (hu E).glue_at_common_state (hv E) hcommon

/-- Gluing two entropy weak solutions at a common state preserves both weak
conservation and every convex entropy inequality. -/
theorem IsEntropyWeakSolution.glue_at_common_state {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ^m} {common : ℝ^m} (hu : IsEntropyWeakSolution flux U u)
    (hv : IsEntropyWeakSolution flux U v) (hcommon : ∀ p ∈ U, u p = common ∨ v p = common) :
    IsEntropyWeakSolution flux U (glueAtCommonState common u v) :=
  ⟨hu.1.glue_at_common_state hv.1 hcommon, hu.2.glue_at_common_state hv.2 hcommon⟩

end PDE.Hyperbolic.ConservationLaw.System
