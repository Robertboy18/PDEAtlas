/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Recovering closed subspace membership from test integrals

If every smooth compactly supported average of a Banach-valued function belongs
to a fixed closed subspace, then the function belongs to that subspace almost
everywhere. Passing to the Banach quotient reduces this to Mathlib's
vector-valued fundamental lemma.
-/

@[expose] public noncomputable section

namespace Submodule

open MeasureTheory Set
open scoped ContDiff

/-- Smooth test averages detect membership in a closed linear subspace.
The measure is arbitrary, so the result also applies to a time restriction. -/
theorem ae_mem_of_integral_contDiff_smul_mem
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : Submodule ℝ X) (hS : IsClosed (S : Set X))
    {μ : Measure E} {U : Set E} (hU : IsOpen U) {u : E → X}
    (hu : Integrable u μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, φ x • u x ∂μ) ∈ S) :
    ∀ᵐ x ∂μ, x ∈ U → u x ∈ S := by
  let : IsClosed (S : Set X) := hS
  have hzero : ∀ᵐ x ∂μ, x ∈ U → S.mkQL (u x) = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (S.mkQL.locallyIntegrableOn_comp (hu.locallyIntegrable.locallyIntegrableOn U))
    intro φ hφ hc hs
    have hi : Integrable (fun x ↦ φ x • u x) μ :=
      hu.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    simp only [Function.comp_apply, ← map_smul]
    rw [S.mkQL.integral_comp_comm hi]
    exact (Submodule.Quotient.mk_eq_zero S).mpr (h φ hφ hc hs)
  filter_upwards [hzero] with x hx hmem
  exact (Submodule.Quotient.mk_eq_zero S).mp (hx hmem)

end Submodule
