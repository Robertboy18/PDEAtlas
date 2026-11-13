/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Equation
public import PDE.Analysis.Evolution.LionsMagenes.Basic.IntegratedDerivative
import Mathlib.Tactic.Positivity.Finset

/-!
# Integrated weak-evolution identities

An endpoint-inclusive integrated dual derivative turns a pointwise weak
evolution equation into its two-time variational identity. These statements
depend only on the Gelfand weak equation and integrated derivative, not on
the time-regularization construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Interval

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section IntegratedEvolution

variable {T : GelfandTriple (V := V) (H := H)}

/-- Two-time form of the weak evolution equation. Once the
time derivative is represented by a `V*` primitive, the pointwise equation
`u_t + B u = ell` integrates to the expected pivot-pairing identity. -/
theorem gelfandWeakEvolution_integral_identity
    (B : V →L[ℝ] StrongDual ℝ V) (ell g : ℝ → StrongDual ℝ V)
    (u : ℝ → V) {a b s t : ℝ}
    (hderiv : HasIntegratedDualDerivativeOn T
      (fun r ↦ T.inclusion (u r)) g a b)
    (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b)
    (heq : ∀ r ∈ uIcc s t,
      SatisfiesGelfandWeakEvolutionAt B (ell r) (u r) (g r))
    (v : V)
    (hB : IntervalIntegrable (fun r ↦ B (u r) v) volume s t) :
    inner ℝ (T.inclusion (u t)) (T.inclusion v) -
        inner ℝ (T.inclusion (u s)) (T.inclusion v) +
        ∫ r in s..t, B (u r) v =
      ∫ r in s..t, ell r v := by
  have hstInt := hderiv.intervalIntegrable.mono_set (uIcc_subset_uIcc hs ht)
  have hgPair : IntervalIntegrable (fun r ↦ g r v) volume s t := ⟨
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hstInt.1,
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hstInt.2⟩
  have hsum :
      (∫ r in s..t, g r v) + ∫ r in s..t, B (u r) v =
        ∫ r in s..t, ell r v := by
    rw [← intervalIntegral.integral_add hgPair hB]
    apply intervalIntegral.integral_congr
    intro r hr
    exact heq r hr v
  rw [hderiv.pairing_sub_eq_integral v hs ht]
  exact hsum

/-- Two-time form of the weak evolution equation for a time-dependent bilinear
form. This is the nonautonomous version used by Galerkin limits with
coefficients `B(t)`: integrating `u_t + B(t)u = ell(t)` between two times
gives the expected pivot-pairing identity for each fixed test vector. -/
theorem gelfandWeakEvolution_integral_identity_timeDependent
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell g : ℝ → StrongDual ℝ V)
    (u : ℝ → V) {a b s t : ℝ}
    (hderiv : HasIntegratedDualDerivativeOn T
      (fun r ↦ T.inclusion (u r)) g a b)
    (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b)
    (heq : ∀ r ∈ uIcc s t,
      SatisfiesGelfandWeakEvolutionAt (B r) (ell r) (u r) (g r))
    (v : V)
    (hB : IntervalIntegrable (fun r ↦ B r (u r) v) volume s t) :
    inner ℝ (T.inclusion (u t)) (T.inclusion v) -
        inner ℝ (T.inclusion (u s)) (T.inclusion v) +
        ∫ r in s..t, B r (u r) v =
      ∫ r in s..t, ell r v := by
  have hstInt := hderiv.intervalIntegrable.mono_set (uIcc_subset_uIcc hs ht)
  have hgPair : IntervalIntegrable (fun r ↦ g r v) volume s t := ⟨
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hstInt.1,
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hstInt.2⟩
  have hsum :
      (∫ r in s..t, g r v) + ∫ r in s..t, B r (u r) v =
        ∫ r in s..t, ell r v := by
    rw [← intervalIntegral.integral_add hgPair hB]
    apply intervalIntegral.integral_congr
    intro r hr
    exact heq r hr v
  rw [hderiv.pairing_sub_eq_integral v hs ht]
  exact hsum

end IntegratedEvolution

end PDE.Analysis.Evolution
