/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.TransportCommutatorBound

/-!
# Coercivity of a mollified weak flux

For a positive W¹,∞ coefficient, the mollification of the distribution `a ∂ⱼu`
controls the derivative of the mollified input, up to a scale-independent multiple
of its L² norm. The input is only in L²: the flux is formed by the distributional
product rule, and the uniform Friedrichs commutator bound supplies the error.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

namespace MeasureTheory.Lp

/-- An almost-everywhere lower bound for a real multiplier gives the same lower
bound for its L² quadratic form, without a finite-measure assumption. -/
theorem mul_norm_sq_le_inner_lpSMul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (a : Lp ℝ ∞ ν) (u : Lp ℝ 2 ν) {c : ℝ} (hc : ∀ᵐ x ∂ν, c ≤ a x) :
    c * ‖u‖ ^ 2 ≤ ⟪a • u, u⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul, L2.inner_def]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul c)
    (L2.integrable_inner (𝕜 := ℝ) (a • u) u)
  filter_upwards [hc, coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u] with x hx hprod
  rw [hprod]
  simp only [Real.inner_apply, smul_eq_mul, Pi.mul_apply]
  nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg (u x))]

end MeasureTheory.Lp

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- The mollified flux has a coercive derivative term up to a uniformly
bounded L² error. Neither a weak derivative of the input nor a flux bound is assumed.
The coefficient and direction determine one constant for all positive scales and inputs. -/
theorem exists_mollified_flux_coercivity
    (μ : Mollifier n) (A : W^{1,∞}(ℝ^n)) (j : Fin n)
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ᵐ x ∂domainMeasure n univ,
      c ≤ (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε) (u : L2),
      c / 2 * ‖mollifierDerivativeRowCLM μ hε j u‖ ^ 2 ≤
        ⟪mollifierDerivativeRowCLM μ hε j
            (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) -
          mollifierRowCLM μ hε
            (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u),
          mollifierDerivativeRowCLM μ hε j u⟫_ℝ + C * ‖u‖ ^ 2 := by
  let B : ℝ :=
    (∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
        (∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖) +
      ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖
  refine ⟨B ^ 2 / (2 * c), div_nonneg (sq_nonneg _) (by positivity), ?_⟩
  intro ε hε u
  let v := mollifierDerivativeRowCLM μ hε j u
  let r := mollifierTransportCommutatorCLM μ hε A j u
  let a := (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  have hprincipal : c * ‖v‖ ^ 2 ≤ ⟪a • v, v⟫_ℝ :=
    Lp.mul_norm_sq_le_inner_lpSMul a v hA
  have hcomm : ‖r‖ ≤ B * ‖u‖ :=
    norm_mollifierTransportCommutatorCLM_apply_le μ hε A j u
  have herror : |⟪r, v⟫_ℝ| ≤ B * ‖u‖ * ‖v‖ :=
    (abs_real_inner_le_norm r v).trans
      (mul_le_mul_of_nonneg_right hcomm (norm_nonneg v))
  have hyoung : B * ‖u‖ * ‖v‖ ≤
      c / 2 * ‖v‖ ^ 2 + B ^ 2 / (2 * c) * ‖u‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * c by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (c * ‖v‖ - B * ‖u‖)]
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
  linarith [le_abs_self ⟪r, v⟫_ℝ]

end SobolevSpace.Approximation
