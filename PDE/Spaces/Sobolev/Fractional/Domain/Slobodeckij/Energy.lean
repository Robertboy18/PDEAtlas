/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Basic

/-!
# The fractional difference energy

For finite positive `p`, the p-th power of the weighted difference has denominator
`‖x - y‖ ^ (n + s * p.toReal)`. Thus the Sobolev–Slobodeckij condition is base `Lᵖ`
membership together with finiteness of the nonnegative product integral.
The identities hold for every real order and every dimension, including the diagonal.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞}

private theorem enorm_inv_rpow_smul (v : F) {r : ℝ} (hr : 0 < r) (a q : ℝ)
    (hq : 0 ≤ q) :
    ‖(r ^ a)⁻¹ • v‖ₑ ^ q =
      ‖v‖ₑ ^ q / (ENNReal.ofReal r) ^ (a * q) := by
  rw [enorm_smul, enorm_inv (Real.rpow_pos_of_pos hr a).ne',
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg hr.le a),
    ← ENNReal.ofReal_rpow_of_pos hr, mul_comm, ← div_eq_mul_inv,
    ENNReal.div_rpow_of_nonneg _ _ hq, ← ENNReal.rpow_mul]

/-- The weighted difference gives the fractional energy integrand everywhere.
On the diagonal both sides vanish, even for negative orders. -/
theorem enorm_diffQuot_rpow (u : ℝ^n → F) (z : ℝ^n × ℝ^n)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal =
      ‖u z.1 - u z.2‖ₑ ^ p.toReal /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + s * p.toReal) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  by_cases hz : z.1 = z.2
  · simp [diffQuot, hz, ENNReal.zero_rpow_of_pos hp]
  · rw [diffQuot,
      enorm_inv_rpow_smul _ (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) _ _ hp.le]
    rw [add_mul, div_mul_cancel₀ _ hp.ne']

/-- For a finite positive exponent, the Gagliardo condition is base `Lᵖ` membership
and finite fractional energy. Base membership supplies a.e. strong measurability. -/
theorem memGagliardo_iff_lintegral_lt_top (u : ℝ^n → F)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemGagliardo n s Ω u (p := p) ↔
      MemLp u p ((volume : Measure (ℝ^n)).restrict Ω) ∧
        (∫⁻ z : ℝ^n × ℝ^n,
          ‖u z.1 - u z.2‖ₑ ^ p.toReal /
            (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + s * p.toReal)
          ∂gagliardoProductMeasure n Ω) < ∞ := by
  unfold MemGagliardo
  refine and_congr_right fun hu ↦ ?_
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop
    (aestronglyMeasurable_diffQuot hu.aestronglyMeasurable)]
  simp_rw [enorm_diffQuot_rpow u _ hp0 hptop]

end SobolevSpace.Fractional
