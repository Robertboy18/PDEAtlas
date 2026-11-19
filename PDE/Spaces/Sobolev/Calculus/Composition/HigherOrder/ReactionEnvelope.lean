/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous monotone bounds for reaction derivatives

Sup norms on a scaled compact unit ball depend continuously on the radius.
Inclusion of concentric balls makes these bounds nondecreasing.
-/

@[expose] public noncomputable section

open Set Metric

namespace SobolevSpace.Composition

variable {m : ℕ} {f : (Fin m → ℝ) → ℝ}

/-- Restrict a reaction derivative to a continuously scaled compact unit ball. -/
def reactionDerivativeOnUnitBall (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) (R : ℝ) :
    C(closedBall (0 : Fin m → ℝ) 1, (Fin m → ℝ) [×j]→L[ℝ] ℝ) :=
  ⟨fun x ↦ iteratedFDeriv ℝ j f (max R 1 • (x : Fin m → ℝ)),
    (hf.continuous_iteratedFDeriv (by simp)).comp (by fun_prop)⟩

private theorem scaledDerivative_bound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ)
    (R : ℝ) {x : Fin m → ℝ} (hx : ‖x‖ ≤ max R 1) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ ‖reactionDerivativeOnUnitBall hf j R‖ := by
  have hR : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let y : closedBall (0 : Fin m → ℝ) 1 := ⟨(max R 1)⁻¹ • x, by
    simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)⟩
  have h := (reactionDerivativeOnUnitBall hf j R).norm_coe_le_norm y
  simpa only [reactionDerivativeOnUnitBall, ContinuousMap.coe_mk, y, smul_smul,
    mul_inv_cancel₀ hR.ne', one_smul] using h

private theorem continuous_scaledDerivative_norm (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) :
    Continuous (fun R ↦ ‖reactionDerivativeOnUnitBall hf j R‖) := by
  have h : Continuous (reactionDerivativeOnUnitBall hf j) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hf.continuous_iteratedFDeriv (by simp)).comp (by fun_prop)
  exact (continuous_norm (E :=
    C(closedBall (0 : Fin m → ℝ) 1, (Fin m → ℝ) [×j]→L[ℝ] ℝ))).comp h

private theorem monotone_scaledDerivative_norm (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) :
    Monotone (fun R ↦ ‖reactionDerivativeOnUnitBall hf j R‖) := by
  intro R S hRS
  apply (ContinuousMap.norm_le (reactionDerivativeOnUnitBall hf j R)
    (norm_nonneg (reactionDerivativeOnUnitBall hf j S))).mpr
  intro x
  apply scaledDerivative_bound hf j S
  calc
    ‖max R 1 • (x : Fin m → ℝ)‖ = max R 1 * ‖(x : Fin m → ℝ)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ max R 1 * 1 := mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall, dist_zero_right] using x.property) (by positivity)
    _ ≤ max S 1 := by simpa using max_le_max_right 1 hRS

/-- A continuous, nondecreasing bound for all derivatives through order `k`
on the ball of radius `R`. Taking `max R 1` also defines it for negative radii. -/
def reactionDerivativeBound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (R : ℝ) : ℝ :=
  1 + ∑ j : Fin (k + 1), ‖reactionDerivativeOnUnitBall hf j.val R‖

theorem one_le_reactionDerivativeBound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (R : ℝ) :
    1 ≤ reactionDerivativeBound hf k R :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦
    norm_nonneg (reactionDerivativeOnUnitBall hf j.val R))

theorem continuous_reactionDerivativeBound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    Continuous (reactionDerivativeBound hf k) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro j _
  exact continuous_scaledDerivative_norm hf j.val

theorem monotone_reactionDerivativeBound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    Monotone (reactionDerivativeBound hf k) := by
  intro R S hRS
  change 1 + ∑ j : Fin (k + 1), ‖reactionDerivativeOnUnitBall hf j.val R‖ ≤
    1 + ∑ j : Fin (k + 1), ‖reactionDerivativeOnUnitBall hf j.val S‖
  exact add_le_add le_rfl (Finset.sum_le_sum fun (j : Fin (k + 1)) _ ↦
    monotone_scaledDerivative_norm hf j.val hRS)

theorem norm_iteratedFDeriv_le_reactionDerivativeBound
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (R : ℝ)
    {x : Fin m → ℝ} (hx : ‖x‖ ≤ R) {j : ℕ} (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ reactionDerivativeBound hf k R := by
  apply (scaledDerivative_bound hf j R (hx.trans (le_max_left _ _))).trans
  exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (reactionDerivativeOnUnitBall hf i.val R))
    (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1)))).trans
    (le_add_of_nonneg_left zero_le_one)

end SobolevSpace.Composition
