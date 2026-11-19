/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.Implicit.LocalizedParameters

/-!
# Norm control of localized Sobolev parameters

The coefficient error in normal inverse recovery is bounded by the
original parameter norms and the first-order norms of their
localizations. The half-space extension has a fixed operator norm.
Thus no derivative of an unlocalized parameter enters the estimate.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Composition.Implicit

open MeasureTheory
open scoped ENNReal NNReal Sobolev

variable {n k : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform bounds on the finite parameter family control the error
term in nonlinear normal recovery. All coefficients are independent
of the parameter fields. -/
theorem localizedParameterBound_le_of_norm_le
    (K C D : ℝ≥0)
    (u : DerivLp n p (HalfSpace.upper n))
    (P : Fin k → DerivLp n p (HalfSpace.upper n))
    (W : Fin k → W^{1,p}(HalfSpace.upper n))
    {a b c : ℝ} (hu : ‖u‖ ≤ a)
    (hP : ∀ j, ‖P j‖ ≤ b) (hW : ∀ j, ‖W j‖ ≤ c) :
    localizedParameterBound K C D u P W ≤
      K * (a + k * b) +
        C * (‖(SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap‖ *
          k * c + D * (k * b)) := by
  let E := (SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap
  have hsumP : (∑ j, ‖P j‖) ≤ k * b := by
    calc
      _ ≤ ∑ _ : Fin k, b := Finset.sum_le_sum fun j _ ↦ hP j
      _ = _ := by simp
  have hsumW : (∑ j, ‖wkpCoordinateCLM
      (singleDerivIndex n (PDE.Common.lastIndex (n := n))) (E (W j))‖) ≤
      ‖E‖ * k * c := by
    calc
      _ ≤ ∑ _ : Fin k, ‖E‖ * c := by
        apply Finset.sum_le_sum
        intro j _
        exact (wkpCoordinateCLM_norm_le _ _).trans
          ((E.le_opNorm (W j)).trans
            (mul_le_mul_of_nonneg_left (hW j) E.opNorm_nonneg))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hu hsumP) K.coe_nonneg)
    (mul_le_mul_of_nonneg_left
      (add_le_add hsumW (mul_le_mul_of_nonneg_left hsumP D.coe_nonneg)) C.coe_nonneg)

end SobolevSpace.GraphSpace.Composition.Implicit
