/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Beta integral over the reals

For real `α, β > 0`, `∫₀¹ x^{α-1} (1 - x)^{β-1} dx = Γ(α) Γ(β) / Γ(α + β)`, as a statement about
a real integral of real powers, and the integral `∫₀^∞ x^{α-1} (1 + x)^{-(α+β)} dx` over the
half-line has the same value. Mathlib has the value of the complex Beta integral
(`Complex.betaIntegral_eq_Gamma_mul_div`); constants of analysis, such as the sharp Sobolev
constant and the mass of the half-space Poisson kernel, need the real forms. The common value is
Mathlib's `ProbabilityTheory.beta α β`.

## Main results

* `Real.integral_rpow_mul_one_sub_rpow`: `∫₀¹ x^{α-1} (1 - x)^{β-1} dx = Γ(α) Γ(β) / Γ(α + β)`
  for all real `α, β > 0`.
* `Real.integral_Ioi_rpow_mul_one_add_rpow`: `∫₀^∞ x^{a-1} (1 + x)^{-(a+b)} dx` has the same
  value, for all real `a, b > 0`.

## How it works

For `0 ≤ x ≤ 1` the complex powers of `x` and `1 - x` with real exponents are the real powers. So
the complex Beta integral at real arguments is the cast of the real integral, and its value is
real. The substitution `x = u / (1 - u)` maps `(0, 1)` onto `(0, ∞)` and turns the integral over
the half-line into the one over `(0, 1)`.

## References

* E. Artin, *The Gamma Function*, Holt, Rinehart and Winston, 1964: the Beta function as a
  quotient of Gamma values.
* *NIST Digital Library of Mathematical Functions*, Release 1.2.8, 2026, §5.12 (Beta Function),
  (5.12.1) and (5.12.3).
  <https://dlmf.nist.gov/5.12>
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Real

/-- **The Beta integral over the reals**: for `α, β > 0`,
`∫₀¹ x^{α-1} (1 - x)^{β-1} dx = Γ(α) Γ(β) / Γ(α + β)`. It is the real form of
`Complex.betaIntegral_eq_Gamma_mul_div`. -/
theorem integral_rpow_mul_one_sub_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1) =
      Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) := by
  have h1 : ∫ x in (0 : ℝ)..1, ((x ^ (α - 1) * (1 - x) ^ (β - 1) : ℝ) : ℂ) =
      Complex.betaIntegral α β := by
    rw [Complex.betaIntegral]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le zero_le_one] at hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1, Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
    push_cast
    rfl
  have h2 := Complex.betaIntegral_eq_Gamma_mul_div (α : ℂ) (β : ℂ) (by simpa) (by simpa)
  rw [intervalIntegral.integral_ofReal, h2, ← Complex.ofReal_add, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h1
  exact_mod_cast h1

/-- **The Beta integral over the half-line**: for `a, b > 0`,
`∫₀^∞ x^{a-1} (1 + x)^{-(a+b)} dx = Γ(a) Γ(b) / Γ(a + b)` (DLMF (5.12.3)). The substitution
`x = u / (1 - u)` maps `(0, 1)` onto `(0, ∞)` and turns the integral into
`integral_rpow_mul_one_sub_rpow`. -/
theorem integral_Ioi_rpow_mul_one_add_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ (a - 1) * (1 + x) ^ (-(a + b))) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hbeta :
      (∫ x : ℝ in Ioo 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
        Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_rpow_mul_one_sub_rpow ha hb
  let f : ℝ → ℝ := fun u ↦ u / (1 - u)
  let f' : ℝ → ℝ := fun u ↦ 1 / (1 - u) ^ 2
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    refine Set.ext fun x ↦ ⟨?_, fun (hx : 0 < x) ↦ ⟨x / (1 + x), ⟨by positivity,
      (div_lt_one (by positivity)).2 (by linarith)⟩, ?_⟩⟩
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      exact div_pos hu0 (sub_pos.mpr hu1)
    · have : 1 + x ≠ 0 := by positivity
      dsimp only [f]
      field_simp
      ring
  have hderiv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivWithinAt f (f' u) (Ioo 0 1) u := by
    have hne : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
    refine (((hasDerivAt_id u).div ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
      hne).congr_deriv ?_).hasDerivWithinAt
    simp only [id_eq, Pi.sub_apply, f']
    field_simp
    ring
  have hinj : InjOn f (Ioo (0 : ℝ) 1) := fun u hu v hv huv ↦ by
    have := (div_eq_div_iff (sub_pos.mpr hu.2).ne' (sub_pos.mpr hv.2).ne').mp huv
    linarith
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine (setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_).trans hbeta
  have hd : 0 < 1 - u := sub_pos.mpr hu.2
  have hd' := hd.ne'
  have hone : 1 + u / (1 - u) = (1 - u)⁻¹ := by
    field_simp
    ring
  have hpow : (1 - u) ^ (a + b) = (1 - u) ^ 2 * (1 - u) ^ (a - 1) * (1 - u) ^ (b - 1) := by
    rw [← Real.rpow_natCast (1 - u) 2, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  simp only [smul_eq_mul, f, f', abs_of_pos (by positivity : 0 < 1 / (1 - u) ^ 2), hone,
    Real.div_rpow hu.1.le hd.le, Real.inv_rpow hd.le, Real.rpow_neg hd.le, inv_inv, hpow]
  field_simp

end Real
