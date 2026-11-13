/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Connection
import CAS.ExactTactic

/-!
# Scalar connections between simple equilibria

The logistic field and its negative give both orientations through any prescribed
interior state.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis.Evolution.Scalar
open scoped Topology

namespace PDE.Examples.Evolution.Scalar

/-- Logistic growth connects zero to one through every interior initial value. -/
theorem exists_logistic_connection {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ → ℝ,
      x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (x t * (1 - x t)) t) ∧
      (∀ t, x t ∈ Ioo (0 : ℝ) 1) ∧ StrictMono x ∧
      Tendsto x atBot (𝓝 0) ∧ Tendsto x atTop (𝓝 1) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  exact exists_heteroclinic_of_pos
    (contDiff_id.mul (contDiff_const.sub contDiff_id)).contDiffOn
    (by norm_num) (by norm_num) (fun z hz ↦ mul_pos hz.1 (sub_pos.mpr hz.2)) hx₀

/-- Reversing the logistic field reverses the orbit and swaps its endpoints. -/
theorem exists_negative_logistic_connection {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ → ℝ,
      x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (-(x t * (1 - x t))) t) ∧
      (∀ t, x t ∈ Ioo (0 : ℝ) 1) ∧ StrictAnti x ∧
      Tendsto x atBot (𝓝 1) ∧ Tendsto x atTop (𝓝 0) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  exact exists_heteroclinic_of_neg
    (contDiff_id.mul (contDiff_const.sub contDiff_id)).neg.contDiffOn
    (by norm_num) (by norm_num)
    (fun z hz ↦ neg_neg_of_pos (mul_pos hz.1 (sub_pos.mpr hz.2))) hx₀

end PDE.Examples.Evolution.Scalar
