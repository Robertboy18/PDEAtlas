/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.WholeSpace
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PDE.Analysis.SpecialFunctions.Gamma.BetaIntegral

/-!
# The sharp Sobolev constant in closed form

The constant `S_n = sharpSobolevConstant n` of the sharp Sobolev inequality is defined with the
integral `κ = ∫₀¹ s √(1 - s^{2/a}) ds`, `a = (n - 2) / 2`. It is the constant of Aubin and
Talenti:

`S_n = (π n (n - 2))^{-1/2} (Γ(n) / Γ(n/2))^{1/n}`,  `n ≥ 3`.

For `n = 3` this is `K_s = 2^{2/3} / (√3 π^{2/3})` (`sharpSobolevConstant_three`). That `S_n` is
the best constant is not proved.

## Main results

* `blissKappa_eq`: `κ(a) = √π Γ(a + 1) / (4 Γ(a + 3/2))` for every `a > 0`.
* `blissKappa_half`: `κ(1/2) = π / 8`, the value for `n = 3`, as a case of `blissKappa_eq`.
* `sharpSobolevConstant_eq`: Talenti's formula above, for every `n ≥ 3`.

## How it works

The substitution `y = s^{2/a}` (`MeasureTheory.integral_comp_rpow_Ioi`) turns `κ` into
`(a/2) ∫₀¹ y^{a-1} (1 - y)^{1/2} dy`, a Beta integral (`Real.integral_rpow_mul_one_sub_rpow`), so
`κ = √π Γ(a + 1) / (4 Γ(a + 3/2))`. With `a = (n - 2) / 2`, the area `σ_n = 2 π^{n/2} / Γ(n/2)`
of the unit sphere and Legendre's duplication formula (`Real.Gamma_mul_Gamma_add_half`),

`4 κ σ_n = 2 π^{(n+1)/2} / Γ((n+1)/2) = 2ⁿ π^{n/2} Γ(n/2) / Γ(n)`,

which is the area of the unit sphere of `ℝ^{n+1}`. Hence
`S_n⁻² = (n (n - 2) / 4) (4 κ σ_n)^{2/n} = π n (n - 2) (Γ(n/2) / Γ(n))^{2/n}`.

## References

* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372,
  formula (2). <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Real

namespace SobolevSpace.Inequalities

/-! ## The constant of Bliss's inequality -/

/-- **The constant of Bliss's inequality as a quotient of Gamma values**: for `a > 0`,
`κ(a) = ∫₀¹ s √(1 - s^{2/a}) ds = √π Γ(a + 1) / (4 Γ(a + 3/2))`, by the substitution
`y = s^{2/a}` and the Beta integral. -/
theorem blissKappa_eq {a : ℝ} (ha : 0 < a) :
    blissKappa a = √π * Real.Gamma (a + 1) / (4 * Real.Gamma (a + 3 / 2)) := by
  have hp : (0 : ℝ) < 2 / a := by positivity
  set G : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator
    fun y ↦ a / 2 * (y ^ (a - 1) * (1 - y) ^ ((3 / 2 : ℝ) - 1)) with hG
  have hsub := integral_comp_rpow_Ioi G hp.ne'
  -- the left side is `κ`
  have hL : ∫ x in Ioi (0 : ℝ), (|2 / a| * x ^ (2 / a - 1)) • G (x ^ (2 / a)) = blissKappa a := by
    have hcongr : ∀ x ∈ Ioi (0 : ℝ), (|2 / a| * x ^ (2 / a - 1)) • G (x ^ (2 / a)) =
        (Ioo (0 : ℝ) 1).indicator (fun x ↦ x * √(1 - x ^ (2 / a))) x := by
      intro x hx
      have hx0 : 0 < x := hx
      by_cases hx1 : x < 1
      · have hmem : x ^ (2 / a) ∈ Ioo (0 : ℝ) 1 :=
          ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_lt_one hx0.le hx1 hp⟩
        rw [hG, indicator_of_mem hmem, indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, hx1⟩),
          abs_of_pos hp, ← Real.rpow_mul hx0.le, smul_eq_mul,
          show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
        have e : x ^ (2 / a - 1) * x ^ (2 / a * (a - 1)) = x := by
          rw [← Real.rpow_add hx0, show 2 / a - 1 + 2 / a * (a - 1) = 1 by field_simp; ring,
            Real.rpow_one]
        calc 2 / a * x ^ (2 / a - 1) * (a / 2 * (x ^ (2 / a * (a - 1)) * √(1 - x ^ (2 / a))))
            = 2 / a * (a / 2) * (x ^ (2 / a - 1) * x ^ (2 / a * (a - 1))) *
                √(1 - x ^ (2 / a)) := by ring
          _ = x * √(1 - x ^ (2 / a)) := by
              rw [e, show 2 / a * (a / 2) = 1 by field_simp, one_mul]
      · have hnot : x ^ (2 / a) ∉ Ioo (0 : ℝ) 1 := fun h ↦
          absurd h.2 (not_lt.mpr (Real.one_le_rpow (not_lt.mp hx1) hp.le))
        rw [hG, indicator_of_notMem hnot,
          indicator_of_notMem (show x ∉ Ioo (0 : ℝ) 1 from fun h ↦ hx1 h.2), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, blissKappa,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  -- the right side is a Beta integral
  have hR : ∫ y in Ioi (0 : ℝ), G y =
      a / 2 * (Real.Gamma a * Real.Gamma (3 / 2) / Real.Gamma (a + 3 / 2)) := by
    rw [hG, setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, Real.integral_rpow_mul_one_sub_rpow ha (by norm_num)]
  rw [← hL, hsub, hR, PDE.Analysis.Gamma_three_div_two, Real.Gamma_add_one ha.ne']
  have hΓ : Real.Gamma (a + 3 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp
  norm_num

/-- **The constant of Bliss's inequality for `n = 3`**: `κ(1/2) = ∫₀¹ s √(1 - s⁴) ds = π / 8`. -/
theorem blissKappa_half : blissKappa (1 / 2) = π / 8 := by
  rw [blissKappa_eq (by norm_num), show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
    show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num, PDE.Analysis.Gamma_three_div_two, Real.Gamma_two,
    show √π * (√π / 2) / (4 * 1) = √π * √π / 8 by ring, Real.mul_self_sqrt Real.pi_pos.le]

/-! ## Talenti's formula -/

/-- **Talenti's formula for the sharp Sobolev constant**: for `n ≥ 3`,
`S_n = (π n (n - 2))^{-1/2} (Γ(n) / Γ(n/2))^{1/n}`. The constant `sharpSobolevConstant n`
contains `4 κ σ_n`, which is `2ⁿ π^{n/2} Γ(n/2) / Γ(n)` by `blissKappa_eq`, the area of the unit
sphere and Legendre's duplication formula. -/
theorem sharpSobolevConstant_eq {n : ℕ} (hn : 3 ≤ n) :
    sharpSobolevConstant n =
      (π * n * (n - 2)) ^ (-(1 / 2 : ℝ)) * (Real.Gamma n / Real.Gamma (n / 2)) ^ ((1 : ℝ) / n) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have : Fact (0 < n) := ⟨by omega⟩
  have ha0 : (0 : ℝ) < ((n : ℝ) - 2) / 2 := by linarith
  have hΓ1 : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hΓ2 : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos (by positivity)
  have hΓ3 : 0 < Real.Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  -- Legendre's duplication formula at `n / 2`
  have hdup : Real.Gamma ((n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) =
      Real.Gamma n * (2 / 2 ^ n) * √π := by
    have h := Real.Gamma_mul_Gamma_add_half ((n : ℝ) / 2)
    rwa [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring, show 2 * ((n : ℝ) / 2) = n by ring,
      Real.rpow_sub two_pos, Real.rpow_one, Real.rpow_natCast] at h
  have hκ : blissKappa (((n : ℝ) - 2) / 2) =
      √π * Real.Gamma ((n : ℝ) / 2) / (4 * Real.Gamma (((n : ℝ) + 1) / 2)) := by
    rw [blissKappa_eq ha0, show ((n : ℝ) - 2) / 2 + 1 = (n : ℝ) / 2 by ring,
      show ((n : ℝ) - 2) / 2 + 3 / 2 = ((n : ℝ) + 1) / 2 by ring]
  have hσ : PDE.Analysis.unitSphereArea n = 2 * √π ^ n / Real.Gamma ((n : ℝ) / 2) := by
    rw [PDE.Analysis.unitSphereArea_eq, PDE.Analysis.unitBallVolume,
      Real.Gamma_add_one (by positivity)]
    field_simp
  have hΓ3' : Real.Gamma (((n : ℝ) + 1) / 2) =
      Real.Gamma n * (2 / 2 ^ n) * √π / Real.Gamma ((n : ℝ) / 2) := by
    rw [← hdup]
    field_simp
  have hprod : 4 * blissKappa (((n : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea n =
      (2 * √π) ^ n * (Real.Gamma ((n : ℝ) / 2) / Real.Gamma n) := by
    rw [hκ, hσ, hΓ3', mul_pow]
    field_simp
  have hq : 0 < Real.Gamma ((n : ℝ) / 2) / Real.Gamma n := div_pos hΓ1 hΓ2
  have hpow : (4 * blissKappa (((n : ℝ) - 2) / 2) * PDE.Analysis.unitSphereArea n) ^
      ((2 : ℝ) / n) = 4 * π * (Real.Gamma ((n : ℝ) / 2) / Real.Gamma n) ^ ((2 : ℝ) / n) := by
    rw [hprod, Real.mul_rpow (by positivity) hq.le, ← Real.rpow_natCast (2 * √π) n,
      ← Real.rpow_mul (by positivity), mul_div_cancel₀ (2 : ℝ) hn0, Real.rpow_two, mul_pow,
      Real.sq_sqrt Real.pi_pos.le]
    norm_num
  have hpos : (0 : ℝ) < π * n * (n - 2) := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    positivity
  rw [sharpSobolevConstant, hpow,
    show (n : ℝ) * (n - 2) / 4 * (4 * π * (Real.Gamma ((n : ℝ) / 2) / Real.Gamma n) ^
      ((2 : ℝ) / n)) = π * n * (n - 2) * (Real.Gamma ((n : ℝ) / 2) / Real.Gamma n) ^
        ((2 : ℝ) / n) by ring,
    Real.mul_rpow hpos.le (Real.rpow_nonneg hq.le _), ← Real.rpow_mul hq.le,
    show (2 : ℝ) / n * -(1 / 2) = -(1 / n) by field_simp, Real.rpow_neg hq.le,
    ← Real.inv_rpow hq.le, inv_div]

end SobolevSpace.Inequalities
