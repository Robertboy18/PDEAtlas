/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.LowerOrderForm
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# The lower-order operator with values in `L²`

Bounded drift and potential coefficients send `H¹₀` into `L²`. Pairing this
operator with a test function gives the lower-order form of `LowerOrderForm`.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The strong lower-order expression `b · Du + cu`, with bounded
coefficient operators on `L²`. -/
def lowerOrderOperator
    (b : Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) :
    H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω :=
  (∑ i, (b i).comp (derivCoordCLM i)) + c.comp baseCoordCLM

/-- The lower-order operator agrees with the usual drift and potential sum. -/
theorem lowerOrderOperator_apply
    (b : Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) (u : H¹₀(Ω)) :
    lowerOrderOperator b c u =
      (∑ i, b i (derivCoordCLM i u)) + c (baseCoordCLM u) := by
  simp only [lowerOrderOperator, add_apply, sum_apply, ContinuousLinearMap.comp_apply]

/-- The variational lower-order form is the pivot pairing of its
strong `L²` expression. -/
theorem lowerOrderForm_eq_pivot_comp (hΩ : IsOpen Ω)
    (b : Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) :
    lowerOrderForm b c = (h10L2GelfandTriple hΩ).pivotToDual.comp
      (lowerOrderOperator b c) := by
  ext u v
  simp only [ContinuousLinearMap.comp_apply,
    PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply,
    h10L2GelfandTriple_inclusion_apply, lowerOrderOperator_apply,
    inner_add_left, sum_inner, lowerOrderForm_apply]

/-- The full form splits into its principal part and the dual image of a
bounded energy-to-pivot operator. -/
theorem fullDivergenceForm_eq_principal_add_pivot_comp (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (b : Fin n → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) :
    fullDivergenceForm A b c = variableCoeffForm A +
      (h10L2GelfandTriple hΩ).pivotToDual.comp (lowerOrderOperator b c) := by
  rw [fullDivergenceForm, lowerOrderForm_eq_pivot_comp hΩ]

end SobolevSpace.GraphSpace
