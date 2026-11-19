/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From geometric essential ranges to power decay

An essential range contracting by a fixed factor on quarter-radius balls
has a power bound at every intermediate radius. The proof chooses a positive
exponent from the contraction factor and the adjacent geometric radius.
It applies to both homogeneous and forced De Giorgi iteration.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace PDE.Elliptic.Regularity.DeGiorgi

private theorem exists_exponent_of_contraction {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧ ρ ≤ (1 / 4 : ℝ) ^ (γ : ℝ) := by
  have hb : Real.log (1 / 4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  let β := Real.log ρ / Real.log (1 / 4 : ℝ)
  have hβ : 0 < β := div_pos_of_neg_of_neg (Real.log_neg hρ hρ1) hb
  let γ : ℝ≥0 := ⟨min (1 / 2) β, (lt_min (by norm_num) hβ).le⟩
  refine ⟨γ, lt_min (by norm_num) hβ, ?_, ?_⟩
  · change min (1 / 2 : ℝ) β < 1
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1 / 2 : ℝ) < 1)
  · apply (Real.le_rpow_iff_log_le hρ (by norm_num : (0 : ℝ) < 1 / 4)).mpr
    calc
      Real.log ρ = β * Real.log (1 / 4 : ℝ) := (div_mul_cancel₀ _ hb.ne).symm
      _ ≤ (γ : ℝ) * Real.log (1 / 4 : ℝ) :=
        mul_le_mul_of_nonpos_right (min_le_right _ _) hb.le

/-- Geometric essential-range decay gives a uniform positive power at all
smaller radii, for any measure on a metric space. -/
theorem exists_holder_range_decay_of_geometric_decay
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ (γ : ℝ≥0) (C : ℝ), 0 < γ ∧ γ < 1 ∧ 0 < C ∧
      ∀ (v : X → ℝ) (z : X) (R : ℝ), 0 < R →
      ∀ M : ℝ, 0 < M →
        (∀ j : ℕ, ∃ d : ℝ, ∀ᵐ x ∂μ.restrict (ball z ((1 / 4 : ℝ) ^ j * R)),
          |v x - d| ≤ ρ ^ j * M) →
      ∀ r : ℝ, 0 < r → r ≤ R → ∃ d : ℝ,
        ∀ᵐ x ∂μ.restrict (ball z r), |v x - d| ≤ C * (r / R) ^ (γ : ℝ) * M := by
  obtain ⟨γ, hγ, hγ1, hpower⟩ := exists_exponent_of_contraction hρ hρ1
  let b : ℝ := (1 / 4 : ℝ) ^ (γ : ℝ)
  have hb : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨γ, b⁻¹, hγ, hγ1, inv_pos.mpr hb, ?_⟩
  intro v z R hR M hM hdecay r hr hrR
  obtain ⟨j, hjlt, hjle⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hR) ((div_le_one hR).mpr hrR)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  obtain ⟨d, hd⟩ := hdecay j
  have hrj : r ≤ (1 / 4 : ℝ) ^ j * R := (div_le_iff₀ hR).mp hjle
  have hp : b ^ (j + 1) ≤ (r / R) ^ (γ : ℝ) := by
    have h := Real.rpow_le_rpow
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _) hjlt.le γ.coe_nonneg
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      mul_comm (↑(j + 1) : ℝ) (γ : ℝ),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h
    exact h
  have hfactor : ρ ^ j ≤ b⁻¹ * (r / R) ^ (γ : ℝ) := by
    apply (pow_le_pow_left₀ hρ.le hpower j).trans
    change b ^ j ≤ b⁻¹ * (r / R) ^ (γ : ℝ)
    have h := (le_div_iff₀ hb).mpr (show b ^ j * b ≤ (r / R) ^ (γ : ℝ) by
      simpa only [pow_succ] using hp)
    exact h.trans_eq (by rw [div_eq_mul_inv, mul_comm])
  refine ⟨d, ?_⟩
  filter_upwards [hd.filter_mono (ae_mono
    (Measure.restrict_mono (ball_subset_ball hrj) le_rfl))] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right hfactor hM.le)


end PDE.Elliptic.Regularity.DeGiorgi
