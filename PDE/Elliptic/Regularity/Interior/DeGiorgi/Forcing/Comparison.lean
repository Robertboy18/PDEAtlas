/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.Ball
import PDE.Analysis.Variational.LaxMilgram

/-!
# Removing the bounded scalar forcing

Lax–Milgram constructs a zero-boundary solution with the same coefficients
and scalar forcing as the given interior solution. Their difference solves
the homogeneous equation. Stampacchia's estimate bounds the correction by
`C R² ‖f‖∞`, uniformly over balls and measurable uniformly elliptic matrices.

The comparison and its error bound are derived from the weak equation.
They require neither a bounded nor a continuous representative of the state.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Variational

variable {n : ℕ} [Fact (0 < n)]

/-- A bounded scalar load can be removed by a zero-boundary solution
whose uniform size decays quadratically with the radius of the ball. -/
theorem exists_bounded_load_homogeneous_comparison
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      ∀ a : Fin n → Fin n → DerivLp n ∞ (ball z R), AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 (ball z R)) (u : H¹(ball z R)),
        IsInteriorWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n (ball z R), ‖f x‖ ≤ M) →
        ∃ w : H¹₀(ball z R), IsWeakDivergenceSolution a f w ∧
          IsInteriorWeakDivergenceSolution a 0 (u - (w : H¹(ball z R))) ∧
          ∀ᵐ x ∂domainMeasure n (ball z R), ‖baseCoordCLM w x‖ ≤ K * R ^ 2 * M := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_le_radius_sq_of_bounded_dirichlet_load hq2 hq hα
  refine ⟨K, hK, ?_⟩
  intro z R hR a ha f u hu M hM hf
  let B : H¹₀(ball z R) →L[ℝ] H¹₀(ball z R) →L[ℝ] ℝ :=
    variableCoeffForm (multiplicationCoefficientOperator a)
  have hB : IsCoercive B := variableCoeffForm_isCoercive (Fact.out : 0 < n)
    isBounded_ball _ (integratedElliptic_multiplication_of_ae a ha)
  let w : H¹₀(ball z R) := solve (V := H¹₀(ball z R)) B hB (loadFunctional f)
  have hw : IsWeakSolution B (loadFunctional f) w :=
    solve.isWeakSolution (V := H¹₀(ball z R)) B hB (loadFunctional f)
  have hwWeak : IsWeakDivergenceSolution a f w :=
    (isWeakSolution_iff_isWeakDivergenceSolution isOpen_ball a f w).mp hw
  refine ⟨w, hwWeak, ⟨isOpen_ball, ?_⟩, hbound z R hR a ha f w hwWeak M hM hf⟩
  intro v
  change interiorVariableCoeffForm (multiplicationCoefficientOperator a)
    (u - h10SubtypeL w) v = loadFunctional 0 v
  calc
    _ = interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v -
        interiorVariableCoeffForm (multiplicationCoefficientOperator a) (h10SubtypeL w) v :=
      congrArg (fun t : H¹₀(ball z R) →L[ℝ] ℝ ↦ t v)
        (map_sub (interiorVariableCoeffForm (multiplicationCoefficientOperator a))
          u (h10SubtypeL w))
    _ = loadFunctional f v - B w v := by
      rw [hu.equation v, interiorVariableCoeffForm_h10SubtypeL]
    _ = 0 := sub_eq_zero.mpr (hw v).symm
    _ = loadFunctional 0 v := by
      simp only [loadFunctional_apply, inner_zero_left]

end SobolevSpace.GraphSpace
