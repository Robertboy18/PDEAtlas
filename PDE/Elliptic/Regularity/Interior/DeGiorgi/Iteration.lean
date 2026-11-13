/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Convergence of the nonlinear De Giorgi energy iteration

For `δ > 0`, a recurrence `Y(k+1) ≤ C B^k Y(k)^(1+δ)` converges to zero
when its initial energy is small enough. The proof constructs a positive
threshold and compares with a geometric sequence. Both the threshold and
the geometric ratio are independent of the sequence.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Elliptic.Regularity.DeGiorgi

private theorem energy_le_geometric
    {C B δ ε θ : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hε : 0 < ε) (hθ : 0 < θ)
    (hscale : B * θ ^ δ ≤ 1) (hsmall : C * ε ^ δ ≤ θ)
    (Y : ℕ → ℝ) (hY : ∀ k, 0 ≤ Y k) (hY0 : Y 0 ≤ ε)
    (hstep : ∀ k, Y (k + 1) ≤ C * B ^ k * Y k ^ (1 + δ)) (k : ℕ) :
    Y k ≤ ε * θ ^ k := by
  induction k with
  | zero => simpa only [pow_zero, mul_one] using hY0
  | succ k ih =>
    have hprod : 0 ≤ ε * θ ^ k := mul_nonneg hε.le (pow_nonneg hθ.le _)
    calc
      Y (k + 1) ≤ C * B ^ k * (ε * θ ^ k) ^ (1 + δ) :=
        (hstep k).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hY k) ih (by linarith)) (mul_nonneg hC (pow_nonneg hB _)))
      _ = (ε * θ ^ k) * (C * ε ^ δ) * (B * θ ^ δ) ^ k := by
        rw [Real.rpow_add_of_nonneg hprod zero_le_one hδ.le, Real.rpow_one,
          Real.mul_rpow hε.le (pow_nonneg hθ.le _), ← Real.rpow_pow_comm hθ.le,
          mul_pow]
        ring
      _ ≤ (ε * θ ^ k) * θ * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsmall hprod
        · exact pow_le_one₀ (mul_nonneg hB (Real.rpow_nonneg hθ.le _)) hscale
        · positivity
        · positivity
      _ = ε * θ ^ (k + 1) := by rw [pow_succ]; ring

/-- A positive initial-energy threshold forces convergence of every nonnegative
sequence satisfying the superlinear energy recurrence. The threshold depends
only on the recurrence constants and the gain exponent. -/
theorem exists_small_energy_threshold
    {C B δ : ℝ} (hC : 0 < C) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Y : ℕ → ℝ,
      (∀ k, 0 ≤ Y k) → Y 0 ≤ ε →
      (∀ k, Y (k + 1) ≤ C * B ^ k * Y k ^ (1 + δ)) →
        Tendsto Y atTop (𝓝 0) := by
  let θ := min (1 / 2 : ℝ) (B⁻¹ ^ δ⁻¹)
  have hθ : 0 < θ := lt_min (by norm_num) (Real.rpow_pos_of_pos (inv_pos.mpr hB) _)
  have hθ1 : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hscale : B * θ ^ δ ≤ 1 := by
    have hp : θ ^ δ ≤ B⁻¹ := by
      calc
        _ ≤ (B⁻¹ ^ δ⁻¹) ^ δ :=
          Real.rpow_le_rpow hθ.le (min_le_right _ _) hδ.le
        _ = _ := Real.rpow_inv_rpow (inv_nonneg.mpr hB.le) hδ.ne'
    exact (mul_le_mul_of_nonneg_left hp hB.le).trans_eq (mul_inv_cancel₀ hB.ne')
  let ε := (θ / C) ^ δ⁻¹
  have hε : 0 < ε := Real.rpow_pos_of_pos (div_pos hθ hC) _
  have hsmall : C * ε ^ δ ≤ θ := by
    rw [show ε ^ δ = θ / C from
      Real.rpow_inv_rpow (div_nonneg hθ.le hC.le) hδ.ne']
    exact (mul_div_cancel₀ θ hC.ne').le
  refine ⟨ε, hε, ?_⟩
  intro Y hY hY0 hstep
  have hb := energy_le_geometric hC.le hB.le hδ hε hθ hscale hsmall Y hY hY0 hstep
  apply squeeze_zero hY hb
  simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1)

end PDE.Elliptic.Regularity.DeGiorgi
