/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Series

/-!
# The power series of `s ↦ j_m (α s)`

On `0 ≤ s ≤ 1` the function `s ↦ j_m (α s)` is the polynomial
`∑_{t < K} sphericalBesselScaledTerm m t α * s ^ (m + 2t)` up to the tail bound
`sphericalBesselTailBound m K α = α ^ (m + 2K) / (2 ^ K K! (2m + 2K + 1)‼)`, as soon as
`α ^ 2 ≤ 2 (K + 1) (2m + 2K + 3)` (`abs_sphericalBesselJ_mul_sub_sum_le`). The coefficients
`(-1) ^ t α ^ (m + 2t) / (2 ^ t t! (2m + 2t + 1)‼)` do not depend on `s`, so the same
coefficients serve every point of the interval.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Nat Finset

/-- The coefficient `(-1) ^ t α ^ (m + 2t) / (2 ^ t t! (2m + 2t + 1)‼)` of `s ^ (m + 2t)` in
`j_m (α s)`. -/
def sphericalBesselScaledTerm (m t : ℕ) (α : ℝ) : ℝ :=
  (-1) ^ t * α ^ (m + 2 * t) / (2 ^ t * ((t ! : ℝ) * ((2 * m + 2 * t + 1)‼ : ℕ)))

/-- The tail bound `α ^ (m + 2K) / (2 ^ K K! (2m + 2K + 1)‼)` after `K` terms. -/
def sphericalBesselTailBound (m K : ℕ) (α : ℝ) : ℝ :=
  α ^ (m + 2 * K) / (2 ^ K * ((K ! : ℝ) * ((2 * m + 2 * K + 1)‼ : ℕ)))

theorem sphericalBesselTailBound_nonneg (m K : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ sphericalBesselTailBound m K α := by
  have := sphericalBesselTerm_denom_pos m K
  unfold sphericalBesselTailBound
  positivity

/-- The term `x ^ m τ_t (x)` of the series at `x = α s` splits into its coefficient and
`s ^ (m + 2t)`. -/
theorem pow_mul_sphericalBesselTerm (m t : ℕ) (α s : ℝ) :
    (α * s) ^ m * sphericalBesselTerm m t (α * s) =
      sphericalBesselScaledTerm m t α * s ^ (m + 2 * t) := by
  have hd := (sphericalBesselTerm_denom_pos m t).ne'
  unfold sphericalBesselTerm sphericalBesselScaledTerm
  have h2 : (2 : ℝ) ^ t ≠ 0 := by positivity
  rw [neg_div, neg_pow, div_pow]
  field_simp
  ring

/-- The polynomial approximation of `s ↦ j_m (α s)` on `[0, 1]`. -/
theorem abs_sphericalBesselJ_mul_sub_sum_le {m K : ℕ} {α s : ℝ} (hα : 0 ≤ α) (hs₀ : 0 ≤ s)
    (hs₁ : s ≤ 1) (hK : α ^ 2 ≤ 2 * (K + 1) * (2 * m + 2 * K + 3)) :
    |sphericalBesselJ m (α * s) -
        ∑ t ∈ range K, sphericalBesselScaledTerm m t α * s ^ (m + 2 * t)| ≤
      sphericalBesselTailBound m K α := by
  have hx0 : 0 ≤ α * s := mul_nonneg hα hs₀
  have hxα : α * s ≤ α := mul_le_of_le_one_right hα hs₁
  have hx2 : (α * s) ^ 2 ≤ 2 * (K + 1) * (2 * m + 2 * K + 3) :=
    (pow_le_pow_left₀ hx0 hxα 2).trans hK
  have htail := abs_reducedSphericalBesselJ_sub_sum_le (l := m) (K := K) hx2
  have hsplit : sphericalBesselJ m (α * s) -
      ∑ t ∈ range K, sphericalBesselScaledTerm m t α * s ^ (m + 2 * t) =
      (α * s) ^ m * (reducedSphericalBesselJ m (α * s) -
        ∑ t ∈ range K, sphericalBesselTerm m t (α * s)) := by
    rw [sphericalBesselJ_eq_pow_mul, mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun t _ ↦ (pow_mul_sphericalBesselTerm m t α s).symm
  rw [hsplit, abs_mul, abs_of_nonneg (pow_nonneg hx0 m)]
  have hd := sphericalBesselTerm_denom_pos m K
  calc (α * s) ^ m * |reducedSphericalBesselJ m (α * s) -
        ∑ t ∈ range K, sphericalBesselTerm m t (α * s)|
      ≤ (α * s) ^ m * sphericalBesselTermAbs m K (α * s) := by gcongr
    _ = (α * s) ^ (m + 2 * K) / (2 ^ K * ((K ! : ℝ) * ((2 * m + 2 * K + 1)‼ : ℕ))) := by
        unfold sphericalBesselTermAbs
        rw [div_pow, pow_add, pow_mul]
        field_simp
    _ ≤ α ^ (m + 2 * K) / (2 ^ K * ((K ! : ℝ) * ((2 * m + 2 * K + 1)‼ : ℕ))) := by
        gcongr
    _ = sphericalBesselTailBound m K α := rfl

end PDE.Analysis.SpecialFunctions
