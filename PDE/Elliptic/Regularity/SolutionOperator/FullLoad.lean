/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
public import PDE.Elliptic.Variational.ShiftedDivergenceForm

/-!
# The full divergence-form operator on `H²`

The weak Leibniz rule identifies the principal strong load. Bounded drift and potential
then give an `L²` load for the full operator. Equality of the base coordinates suffices
to identify the `H²` field with its zero-boundary `H¹` representative.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- An `H²` field and an `H¹₀` field representing the same function have identical
first-order Sobolev coordinates. -/
theorem lowerOrder_eq_h10SubtypeL_of_base_eq (hopen : IsOpen Ω)
    (G : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM G = baseCoordCLM u) :
    lowerOrderCLM (k := 1) (m := 2) (by omega) G = (u : H¹(Ω)) := by
  apply wkpBaseCoordinateCLM_injective hopen
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex, h10SubtypeL_apply, baseCoordCLM_apply] using hbase

/-- The full strong load `-div(a Du) + b · Du + c u`, as an `L²` class. -/
def fullStrongLoad (A : Fin n → Fin n → W^{1,∞}(Ω))
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) (G : W^{2,2}(Ω)) :
    DerivLp n 2 Ω :=
  strongLoad A G +
    ∑ i, b i • (G : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) +
    c • wkpBaseCoordinateCLM G

/-- The full `H²` load satisfies the variational equation against every `H¹₀` test function. -/
theorem fullDivergenceForm_eq_fullStrongLoad (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (G : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM G = baseCoordCLM u) (v : H¹₀(Ω)) :
    fullDivergenceForm (multiplicationCoefficientOperator (coefficientBase A))
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
      ⟪fullStrongLoad A b c G, baseCoordCLM v⟫_ℝ := by
  have hG := lowerOrder_eq_h10SubtypeL_of_base_eq hopen G u hbase
  have hprincipal :=
    (isWeakSolution_iff_isWeakDivergenceSolution hopen _ _ _).2
      (strongLoad_isWeakDivergenceSolution hopen A G u hG) v
  have hderiv (i : Fin n) :
      (G : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by norm_num) i) =
        derivCoordCLM i u := by
    have h := congrArg (fun U : H¹(Ω) ↦
      (U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)) hG
    simpa [lowerOrderCLM_apply, derivCoordCLM_apply, h10SubtypeL_apply,
      firstDerivIndex] using h
  rw [fullDivergenceForm_apply]
  change variableCoeffForm (multiplicationCoefficientOperator (coefficientBase A)) u v +
    (∑ i, ⟪b i • derivCoordCLM i u, baseCoordCLM v⟫_ℝ) +
    ⟪c • baseCoordCLM u, baseCoordCLM v⟫_ℝ = _
  rw [hprincipal, loadFunctional_apply]
  simp only [fullStrongLoad, inner_add_left, sum_inner, hderiv, hbase]

/-- Every zero-boundary `H²` field solves the full distributional equation for its strong load. -/
theorem fullStrongLoad_isWeakShiftedFullDivergenceSolution (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (G : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM G = baseCoordCLM u) :
    IsWeakShiftedFullDivergenceSolution (coefficientBase A) b c 0
      (fullStrongLoad A b c G) 0 u := by
  apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen _ _ _ _ _ _ _).1
  intro v
  simpa only [shiftedDivergenceForm_apply, zero_mul, add_zero,
    generalizedLoad_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero] using
    fullDivergenceForm_eq_fullStrongLoad hopen A b c G u hbase v

end SobolevSpace.GraphSpace.BoundaryRegularity
