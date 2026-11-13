/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.MollifiedCoercivity
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Localized coercivity of a mollified weak flux

A bounded multiplier localizes the coercive flux estimate without requiring a
derivative of the L² input. The multiplier is squared in the testing slot, so the
principal term controls the localized derivative norm. The coefficient determines
one error constant for all multipliers, positive scales, and inputs.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

/-- A squared bounded multiplier in the testing slot gives local coercivity for the
distributional mollified flux. The error uses only the input L² norm, and its
constant is independent of the localization and mollifier scale. -/
theorem exists_localized_mollified_flux_coercivity
    (μ : Mollifier n) (A : W^{1,∞}(ℝ^n)) (j : Fin n)
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ᵐ x ∂domainMeasure n univ,
      c ≤ (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : DerivLp n ∞ univ) (ε : ℝ) (hε : 0 < ε) (u : DerivLp n 2 univ),
        c / 2 * ‖b • mollifierDerivativeRowCLM μ hε j u‖ ^ 2 ≤
          ⟪mollifierDerivativeRowCLM μ hε j
              (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) -
            mollifierRowCLM μ hε
              (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u),
            b • (b • mollifierDerivativeRowCLM μ hε j u)⟫_ℝ +
              C * ‖b‖ ^ 2 * ‖u‖ ^ 2 := by
  let B : ℝ :=
    (∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
        (∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖) +
      ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖
  refine ⟨B ^ 2 / (2 * c), div_nonneg (sq_nonneg _) (by positivity), ?_⟩
  intro b ε hε u
  let v := mollifierDerivativeRowCLM μ hε j u
  let r := mollifierTransportCommutatorCLM μ hε A j u
  let a := (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  have hab : a • (b • v) = b • (a • v) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a (b • v),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) b (a • v),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) b v,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a v] with x hab hba hb ha
    simp only [Pi.smul_apply', smul_eq_mul] at hab hba hb ha
    rw [hab, hba, hb, ha]
    ac_rfl
  have hprincipal :
      c * ‖b • v‖ ^ 2 ≤ ⟪a • v, b • (b • v)⟫_ℝ := by
    rw [← Lp.inner_lpSMul_left b, ← hab]
    exact Lp.mul_norm_sq_le_inner_lpSMul a (b • v) hA
  have hcomm : ‖r‖ ≤ B * ‖u‖ :=
    norm_mollifierTransportCommutatorCLM_apply_le μ hε A j u
  have herror : |⟪r, b • (b • v)⟫_ℝ| ≤
      ‖b‖ * B * ‖u‖ * ‖b • v‖ := by
    rw [← Lp.inner_lpSMul_left b]
    calc
      |⟪b • r, b • v⟫_ℝ| ≤ ‖b • r‖ * ‖b • v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖b‖ * ‖r‖) * ‖b • v‖ :=
        mul_le_mul_of_nonneg_right (Lp.norm_smul_le b r) (norm_nonneg _)
      _ ≤ (‖b‖ * (B * ‖u‖)) * ‖b • v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcomm (norm_nonneg _)) (norm_nonneg _)
      _ = ‖b‖ * B * ‖u‖ * ‖b • v‖ := by rw [mul_assoc ‖b‖ B ‖u‖]
  have hyoung : ‖b‖ * B * ‖u‖ * ‖b • v‖ ≤
      c / 2 * ‖b • v‖ ^ 2 + B ^ 2 / (2 * c) * ‖b‖ ^ 2 * ‖u‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * c by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (c * ‖b • v‖ - ‖b‖ * B * ‖u‖)]
  have hflux :
      mollifierDerivativeRowCLM μ hε j
          (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) -
        mollifierRowCLM μ hε
          (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u) =
        a • v - r := by
    dsimp only [a, v, r]
    rw [mollifierTransportCommutatorCLM_apply]
    abel
  rw [hflux, inner_sub_left]
  linarith [le_abs_self ⟪r, b • (b • v)⟫_ℝ]

end SobolevSpace.Approximation
