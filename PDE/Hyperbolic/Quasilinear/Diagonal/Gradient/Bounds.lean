/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Weight

/-!
# Uniform Riccati coefficients on a state cube

Strict positivity of the own-coordinate speed derivative and the signed gap
give a positive lower bound for the weighted quadratic coefficient. The constant
is chosen before any solution or time interval.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Hyperbolic.Quasilinear.Diagonal

variable {B : Fin 2 → (Fin 2 → ℝ) → ℝ}

/-- Genuine nonlinearity on a compact state cube gives a uniform positive
Riccati coefficient for every normalized spatial weight in that cube. -/
theorem exists_pos_le_weighted_coefficient (hB : ∀ i, ContDiff ℝ 1 (B i))
    (hgap : ∀ i z, B i z ≠ B i.rev z) (hpos : ∀ i z, 0 < fderiv ℝ (B i) z (Pi.single i 1)) (R : ℝ)
    (i : Fin 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ Icc (fun _ : Fin 2 ↦ -R) (fun _ ↦ R), ∀ w ∈ Icc (fun _ : Fin 2 ↦ -R)
      (fun _ ↦ R), κ ≤ fderiv ℝ (B i) w (Pi.single i 1) / spatialWeight B i z (w i.rev) := by
  have hK : IsCompact (Icc (fun _ : Fin 2 ↦ -R) (fun _ ↦ R)) := isCompact_Icc
  have hc : Continuous (fun z ↦ fderiv ℝ (B i) z (Pi.single i 1)) :=
    (hB i).continuous_fderiv (by simp) |>.clm_apply continuous_const
  obtain ⟨δ, hδ, hδbound⟩ := hK.exists_forall_le' hc.continuousOn (fun z _ ↦ hpos i z)
  obtain ⟨Q₀, hQ₀⟩ := hK.exists_bound_of_continuousOn
    (continuous_transverseRatio hB hgap i).continuousOn
  let Q := max Q₀ 0
  have hQ : 0 ≤ Q := le_max_right _ _
  have hQbound : ∀ z ∈ Icc (fun _ : Fin 2 ↦ -R) (fun _ ↦ R), ‖transverseRatio B i z‖ ≤ Q :=
    fun z hz ↦ (hQ₀ z hz).trans (le_max_left _ _)
  refine ⟨δ / Real.exp (2 * Q * R), div_pos hδ (Real.exp_pos _), fun z hz w hw ↦ ?_⟩
  have hweight := spatialWeight_le_exp hQ i hz ⟨hw.1 i.rev, hw.2 i.rev⟩ hQbound
  apply (div_le_div_iff₀ (Real.exp_pos _) (spatialWeight_pos i z (w i.rev))).mpr
  exact (mul_le_mul_of_nonneg_left hweight hδ.le).trans
    (mul_le_mul_of_nonneg_right (hδbound w hw) (Real.exp_pos _).le)

end PDE.Hyperbolic.Quasilinear.Diagonal
