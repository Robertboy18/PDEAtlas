/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Iteration

/-!
# Size of the Hölder comparison error

The squared Hölder moduli factor as the radius to twice the exponent. The
remaining coefficient is independent of radius and multiplies one plus the
mean gradient energy.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Campanato

/-- Factor the frozen comparison error into its vanishing radius power and
a constant times one plus the nonnegative mean energy. -/
theorem holder_comparison_error_le
    (n : ℕ) {α s E K M γ : ℝ} (hα : 0 < α) (hs : 0 < s) (hE : 0 ≤ E) :
    (2 * n * (M * s ^ γ) ^ 2 + 2 * (n : ℝ) ^ 2 * (K * s ^ γ) ^ 2 * E) / α ^ 2 ≤
      ((2 * n * M ^ 2 + 2 * (n : ℝ) ^ 2 * K ^ 2) / α ^ 2) *
        s ^ (2 * γ) * (1 + E) := by
  have hp : (s ^ γ) ^ 2 = s ^ (2 * γ) := by
    rw [← Real.rpow_mul_natCast hs.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm]
  rw [mul_pow, mul_pow, hp]
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hc : ((2 * n * M ^ 2 + 2 * (n : ℝ) ^ 2 * K ^ 2) / α ^ 2) *
      s ^ (2 * γ) * (1 + E) * α ^ 2 =
      (2 * n * M ^ 2 + 2 * (n : ℝ) ^ 2 * K ^ 2) * s ^ (2 * γ) * (1 + E) := by
    field_simp
  rw [hc]
  nlinarith only [mul_nonneg (mul_nonneg
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) (sq_nonneg M))
    (Real.rpow_nonneg hs.le (2 * γ))) hE,
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2)
      (sq_nonneg K)) (Real.rpow_nonneg hs.le (2 * γ))]

end PDE.Elliptic.Regularity.Campanato
