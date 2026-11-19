/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.Analysis.MeasureTheory.Lp.NonnegativeMultiplier

/-!
# Symmetric divergence forms with nonnegative potential

With no drift, a real potential preserves symmetry. Its nonnegative quadratic
pairing preserves the coercivity that comes from uniform ellipticity and Poincaré.
The full divergence form is reused, including its potential term.
-/

open scoped Sobolev

@[expose] public section

namespace SobolevSpace.GraphSpace

open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Without drift, the full form is the principal form plus the potential pairing. -/
theorem fullDivergenceForm_zero_drift_apply
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) (c : DerivLp n ∞ Ω) (u v : H¹₀(Ω)) :
    fullDivergenceForm A (multiplicationFirstOrderOperator 0)
        (multiplicationZeroOrderOperator c) u v =
      variableCoeffForm A u v + ⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ := by
  simp only [fullDivergenceForm_apply, multiplicationFirstOrderOperator_apply,
    multiplicationZeroOrderOperator_apply, Pi.zero_apply, MeasureTheory.Lp.zero_smul,
    inner_zero_left, Finset.sum_const_zero, add_zero, variableCoeffForm_apply]

/-- A symmetric principal part and a real potential give a symmetric full form. -/
theorem fullDivergenceForm_zero_drift_symm
    {A : Fin n → Fin n → (L2 →L[ℝ] L2)} (hA : SymmetricCoefficientOperator A)
    (c : DerivLp n ∞ Ω) (u v : H¹₀(Ω)) :
    fullDivergenceForm A (multiplicationFirstOrderOperator 0)
        (multiplicationZeroOrderOperator c) u v =
      fullDivergenceForm A (multiplicationFirstOrderOperator 0)
        (multiplicationZeroOrderOperator c) v u := by
  rw [fullDivergenceForm_zero_drift_apply, fullDivergenceForm_zero_drift_apply,
    variableCoeffForm_symm hA, MeasureTheory.Lp.inner_lpSMul_left, real_inner_comm]

/-- A nonnegative potential preserves bounded-domain Dirichlet coercivity. -/
theorem fullDivergenceForm_zero_drift_isCoercive
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) {α : ℝ} (hA : IntegratedElliptic A α)
    (c : DerivLp n ∞ Ω) (hc : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ c x) :
    IsCoercive (fullDivergenceForm A (multiplicationFirstOrderOperator 0)
      (multiplicationZeroOrderOperator c)) := by
  obtain ⟨β, hβ, hbound⟩ := variableCoeffForm_isCoercive hn hbounded A hA
  refine ⟨β, hβ, fun u ↦ ?_⟩
  rw [fullDivergenceForm_zero_drift_apply]
  exact (hbound u).trans (le_add_of_nonneg_right
    (MeasureTheory.Lp.inner_lpSMul_self_nonneg c hc (baseCoordCLM u)))

end SobolevSpace.GraphSpace
