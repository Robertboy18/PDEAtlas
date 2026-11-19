/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Basic.Real.Basic
public import PDE.Analysis.Analytic.PowerSeries.Catalan
public import PDE.Analytic.CauchyKovalevskaya.Formal.Recursion
import Mathlib.Tactic.LinearCombination

/-!
# The scalar quadratic majorant

The zero-trace root of `(ρ - ∑ xⱼ) v = α t + κ v²` is constructed from
the Catalan series. Differentiating this identity gives the time and spatial
equations with the same invertible formal denominator.

The affine series `A = spatialDenominator d ρ = ρ - ∑ⱼ xⱼ` involves only the spatial variables,
since time is coordinate zero. Its constant coefficient is `ρ`, so it is invertible as a formal
series for `ρ ≠ 0`. Under that hypothesis the differentiated identities are
`(A - 2κv) ∂ₜv = α` (`scalarMajorant_pderiv_zero`) and `(A - 2κv) ∂ⱼv = v`
(`scalarMajorant_pderiv_succ`).

With `ρ = r`, `α = Cr` and `2κ = m(d + 1)` the root is the explicit solution `v*` in (34)
of the proof of Evans, §4.6.3, Theorem 2, which Evans writes with a square root.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, (33)-(34).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable (d : ℕ) (ρ α κ : ℝ)

/-- The affine series `ρ - ∑ j, X j.succ`, or `ρ - (x₁ + ⋯ + x_d)`.
Time occupies coordinate zero, so this series is independent of time. -/
def spatialDenominator : MvPowerSeries (Fin (d + 1)) ℝ :=
  C ρ - ∑ j : Fin d, X j.succ

/-- The formal scalar root with zero initial trace. -/
def scalarMajorant : MvPowerSeries (Fin (d + 1)) ℝ :=
  quadraticRoot (C α * X 0 * (spatialDenominator d ρ)⁻¹)
    (C κ * (spatialDenominator d ρ)⁻¹)

@[simp]
theorem constantCoeff_spatialDenominator :
    constantCoeff (spatialDenominator d ρ) = ρ := by
  simp [spatialDenominator]

@[simp]
theorem pderiv_zero_spatialDenominator :
    pderiv 0 (spatialDenominator d ρ) = 0 := by
  simp [spatialDenominator, pderiv_X_of_ne, Fin.succ_ne_zero]

@[simp]
theorem pderiv_succ_spatialDenominator (j : Fin d) :
    pderiv j.succ (spatialDenominator d ρ) = -1 := by
  classical
  have h (k : Fin d) :
      pderiv j.succ (X k.succ : MvPowerSeries (Fin (d + 1)) ℝ) =
        if k = j then 1 else 0 := by
    split_ifs with hkj
    · subst k
      simp
    · exact pderiv_X_of_ne (by simpa using hkj)
  simp [spatialDenominator, h]

@[simp]
theorem constantCoeff_scalarMajorant :
    constantCoeff (scalarMajorant d ρ α κ) = 0 := by
  apply constantCoeff_quadraticRoot
  simp

/-- The full initial spatial series vanishes, not only its value at the origin. -/
theorem initial_trace_scalarMajorant :
    PowerSeries.constantCoeff (finSuccEquiv ℝ d (scalarMajorant d ρ α κ)) = 0 := by
  simp [scalarMajorant, quadraticRoot, finSuccEquiv_X_zero]

/-- The constructed scalar series satisfies its defining quadratic identity. -/
theorem spatialDenominator_mul_scalarMajorant (hρ : ρ ≠ 0) :
    spatialDenominator d ρ * scalarMajorant d ρ α κ =
      C α * X 0 + C κ * scalarMajorant d ρ α κ ^ 2 := by
  let a := spatialDenominator d ρ
  let v := scalarMajorant d ρ α κ
  have hv : v = C α * X 0 * a⁻¹ + C κ * a⁻¹ * v ^ 2 :=
    quadraticRoot_eq _ _ (by simp)
  have ha : constantCoeff a ≠ 0 := by simpa [a] using hρ
  calc
    a * v = a * (C α * X 0 * a⁻¹ + C κ * a⁻¹ * v ^ 2) := congrArg (a * ·) hv
    _ = (a * a⁻¹) * (C α * X 0 + C κ * v ^ 2) := by ring
    _ = C α * X 0 + C κ * v ^ 2 := by rw [a.mul_inv_cancel ha, one_mul]

/-- Formal time differentiation uses the branch whose denominator has constant term `ρ`. -/
theorem scalarMajorant_pderiv_zero (hρ : ρ ≠ 0) :
    (spatialDenominator d ρ - 2 * C κ * scalarMajorant d ρ α κ) *
        pderiv 0 (scalarMajorant d ρ α κ) = C α := by
  have h := congrArg (pderiv 0) (spatialDenominator_mul_scalarMajorant d ρ α κ hρ)
  simp only [Derivation.leibniz, smul_eq_mul, map_add, pderiv_C,
    pderiv_X_self, pderiv_zero_spatialDenominator, pderiv_pow, Nat.reduceSub,
    pow_one, mul_one, mul_zero, add_zero] at h
  linear_combination h

/-- Every spatial derivative satisfies the same scalar denominator identity. -/
theorem scalarMajorant_pderiv_succ (hρ : ρ ≠ 0) (j : Fin d) :
    (spatialDenominator d ρ - 2 * C κ * scalarMajorant d ρ α κ) *
        pderiv j.succ (scalarMajorant d ρ α κ) = scalarMajorant d ρ α κ := by
  have h := congrArg (pderiv j.succ)
    (spatialDenominator_mul_scalarMajorant d ρ α κ hρ)
  simp only [Derivation.leibniz, smul_eq_mul, map_add, pderiv_C,
    pderiv_X_of_ne (Fin.succ_ne_zero j).symm, pderiv_succ_spatialDenominator,
    pderiv_pow, Nat.reduceSub, pow_one, mul_zero, add_zero, zero_add, mul_neg,
    mul_one] at h
  rw [← sub_eq_add_neg] at h
  linear_combination h

end PDE.Analytic.CauchyKovalevskaya
