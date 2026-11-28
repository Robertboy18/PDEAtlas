/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.H1
import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.Constant

/-!
# The sharp Sobolev inequality on `H¹(ℝ³)`

Every `u` in `H¹(ℝ³)` lies in `L⁶` and satisfies

`‖u‖₆ ≤ K_s ‖∇u‖₂`,  `K_s = 2^{2/3} / (√3 π^{2/3})`.

This is the inequality that Hou, Wang and Yang quote from Talenti in the proof of their
Lemma 6, where they derive `K₄ = K_s^{3/2} = 2 / (3^{3/4} π)` from it. It is the case `n = 3` of
the inequality on `H¹(ℝⁿ)`. That `K_s` is the best constant is not proved.

## Main results

* `sharpSobolevConstant_three`: `sharpSobolevConstant 3 = 2^{2/3} / (√3 π^{2/3})`.
* `coe_pStar_three_two`: the Sobolev exponent `pStar 3 2` is `6`.
* `memLp_six_H1`: every `u ∈ H¹(ℝ³)` lies in `L⁶`.
* `toReal_eLpNorm_six_le_mul_norm_wkpGradientCLM`: `‖u‖₆ ≤ K_s ‖∇u‖₂` for every `u ∈ H¹(ℝ³)`.
* `eLpNorm_six_le_ofReal_mul_norm`: `‖u‖₆ ≤ K_s ‖u‖_{H¹}` for every `u ∈ H¹(ℝ³)`.

## How it works

The inequality on `H¹(ℝⁿ)` has the exponent `2n / (n - 2)` and the constant
`S_n = (n (n - 2) / 4 · (4 κ σ_n)^{2/n})^{-1/2}`. For `n = 3` the exponent is `6`, `κ = π / 8`
(`blissKappa_half`) and the unit sphere has area `σ₃ = 4π`
(`PDE.Analysis.unitSphereArea_three`), so `S₃⁻² = (3/4) (2π²)^{2/3}`, which is `K_s⁻²`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Appendix A, Lemma 6 and its
  proof. <https://arxiv.org/abs/2509.25116>
* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the inequality, with the constant in formula (2). <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev Real

namespace SobolevSpace.Inequalities

/-- **The sharp Sobolev constant in dimension three** is `K_s = 2^{2/3} / (√3 π^{2/3})`: here
`κ = π / 8` and the unit sphere has area `4π`, so `S₃⁻² = (3/4) (2π²)^{2/3}`. -/
theorem sharpSobolevConstant_three :
    sharpSobolevConstant 3 = 2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ)) := by
  have hT3 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hX : (3 : ℝ) * (3 - 2) / 4 *
      (4 * blissKappa (((3 : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea 3) ^ ((2 : ℝ) / 3) =
      3 / 4 * 2 ^ (2 / 3 : ℝ) * (π ^ (2 / 3 : ℝ)) ^ 2 := by
    rw [show ((3 : ℝ) - 2) / 2 = 1 / 2 by norm_num, blissKappa_half,
      PDE.Analysis.unitSphereArea_three, show 4 * (π / 8) * (4 * π) = 2 * π ^ 2 by ring,
      Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast π 2,
      ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_natCast (π ^ (2 / 3 : ℝ)) 2,
      ← Real.rpow_mul Real.pi_pos.le, mul_comm ((2 : ℕ) : ℝ) (2 / 3 : ℝ)]
    norm_num
    ring
  have hY0 : (0 : ℝ) < 2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ)) := by positivity
  have hXY : (3 / 4 * 2 ^ (2 / 3 : ℝ) * (π ^ (2 / 3 : ℝ)) ^ 2 : ℝ) =
      ((2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ))) ^ 2)⁻¹ := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    field_simp
    linear_combination hT3
  rw [sharpSobolevConstant, Nat.cast_ofNat, hX, hXY, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_sq hY0.le, inv_inv]

/-- In dimension three the Sobolev exponent `pStar 3 2 = 2n / (n - 2)` is `6`. -/
theorem coe_pStar_three_two : ((pStar 3 2 : ℝ≥0) : ℝ≥0∞) = 6 := by
  rw [coe_pStar_two, show 2 * (((3 : ℕ) : ℝ)) / ((((3 : ℕ) : ℝ)) - 2) = 6 by norm_num,
    ENNReal.ofReal_ofNat]

/-- Every `u` in `H¹(ℝ³)` lies in `L⁶`: the case `n = 3` of `memLp_pStar_H1`. -/
theorem memLp_six_H1 (U : H¹(ℝ^3)) :
    MemLp (baseRepresentative U) (ENNReal.ofReal 6) (domainMeasure 3 univ) := by
  simpa [coe_pStar_three_two] using memLp_pStar_H1 (n := 3) le_rfl U

/-- **The sharp Sobolev inequality on `H¹(ℝ³)`** (Aubin, Talenti): every `u` in `H¹(ℝ³)`
satisfies `‖u‖₆ ≤ K_s ‖∇u‖₂` with `K_s = 2^{2/3} / (√3 π^{2/3})`. The left side is the `L⁶`
norm of the representative of `u`, which is finite by `memLp_six_H1`, and the right side has
the `L²` norm of the weak gradient `wkpGradientCLM u`, so `‖∇u‖₂² = ∑ⱼ ‖∂ⱼu‖₂²`.

This is the inequality that Hou, Wang and Yang quote from Talenti in the proof of their
Lemma 6 (arXiv:2509.25116, Appendix A). It is the case `n = 3` of
`toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM`. That `K_s` is the smallest
constant is not proved. -/
theorem toReal_eLpNorm_six_le_mul_norm_wkpGradientCLM (u : H¹(ℝ^3)) :
    (eLpNorm (baseRepresentative u) 6 volume).toReal ≤
      2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ)) * ‖wkpGradientCLM u‖ := by
  have h := toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM (n := 3) le_rfl u
  rwa [coe_pStar_three_two, sharpSobolevConstant_three] at h

/-- **The `L⁶` bound of `H¹(ℝ³)` with the constant of Aubin and Talenti**:
`‖u‖₆ ≤ K_s ‖u‖_{H¹}`, the case `n = 3` of `eLpNorm_le_ofReal_sharpSobolevConstant_mul_norm`. -/
theorem eLpNorm_six_le_ofReal_mul_norm (u : H¹(ℝ^3)) :
    eLpNorm (baseRepresentative u) 6 volume ≤
      ENNReal.ofReal (2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ)) * ‖u‖) := by
  have h := eLpNorm_le_ofReal_sharpSobolevConstant_mul_norm (n := 3) le_rfl u
  rwa [coe_pStar_three_two, sharpSobolevConstant_three] at h

end SobolevSpace.Inequalities
