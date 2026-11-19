/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
import CAS.ExactTactic

/-!
# Cost gaps for displaced quadratic profiles

The two inequalities isolate the algebra and positivity behind outward and inward
displacements of a quadratic profile. The expansion identities are checked by `cas`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

/-- An outward displacement creates a strict quadratic cost gap exceeding `E / s`. -/
theorem quadratic_outward_gap {P d s a E w : ℝ}
    (hd : 0 < d) (hs : 0 < s) (hP : 0 ≤ P) (ha : 0 ≤ a)
    (hgap : E < P * a / d) (hw : P * s + a ≤ |w|) :
    P ^ 2 / (2 * d) + E / s < w ^ 2 / (2 * d * s ^ 2) := by
  have heq : (P * s + a) ^ 2 / (2 * d * s ^ 2) =
      P ^ 2 / (2 * d) + (P * a / d) / s + a ^ 2 / (2 * d * s ^ 2) := by cas
  have hsq : (P * s + a) ^ 2 ≤ w ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (by positivity : 0 ≤ P * s + a) (abs_nonneg w)).2 hw
  calc
    P ^ 2 / (2 * d) + E / s < P ^ 2 / (2 * d) + (P * a / d) / s :=
      add_lt_add_of_le_of_lt le_rfl ((div_lt_div_iff_of_pos_right hs).2 hgap)
    _ ≤ (P * s + a) ^ 2 / (2 * d * s ^ 2) := by
      rw [heq]
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ w ^ 2 / (2 * d * s ^ 2) :=
      div_le_div_of_nonneg_right hsq (by positivity)

/-- A bounded inward displacement creates a strict quadratic cost deficit for
sufficiently large `s`. The square of the displacement is controlled explicitly. -/
theorem quadratic_inward_gap {P d s a M E : ℝ}
    (hd : 0 < d) (hs : 0 < s) (ha : 0 ≤ a) (haM : a ≤ M)
    (hgap : E + 2 ≤ P * a / d) (hlarge : M ^ 2 / (2 * d) ≤ s) :
    (P * s - a) ^ 2 / (2 * d * s ^ 2) + E / s < P ^ 2 / (2 * d) := by
  have hM : 0 ≤ M := ha.trans haM
  have hsq : a ^ 2 ≤ M ^ 2 := (sq_le_sq₀ ha hM).2 haM
  have hsmall : a ^ 2 / (2 * d * s ^ 2) ≤ 1 / s := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d * s ^ 2)).2
    have hb : M ^ 2 ≤ s * (2 * d) := (div_le_iff₀ (by positivity)).1 hlarge
    have heq : 1 / s * (2 * d * s ^ 2) = s * (2 * d) := by cas
    rw [heq]
    exact hsq.trans hb
  have heq : (P * s - a) ^ 2 / (2 * d * s ^ 2) =
      P ^ 2 / (2 * d) - (P * a / d) / s + a ^ 2 / (2 * d * s ^ 2) := by cas
  rw [heq]
  have hb := div_le_div_of_nonneg_right hgap hs.le
  have hsplit : (E + 2) / s = E / s + 2 / s := by cas
  rw [hsplit] at hb
  have hpos : 0 < 1 / s := one_div_pos.mpr hs
  have htwo : 2 / s = 2 * (1 / s) := by cas
  rw [htwo] at hb
  linarith

end PDE.Analysis
