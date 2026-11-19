/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Diagonal
public import PDE.Analysis.Analytic.PowerSeries.Nonnegative
public import PDE.Analysis.Analytic.PowerSeries.QuadraticConvergence
public import PDE.Analytic.CauchyKovalevskaya.Majorant.Scalar

/-!
# Convergence of the scalar Cauchy–Kovalevskaya majorant

The coefficients of the zero-trace quadratic root are nonnegative. Identifying
all coordinates reduces convergence to the finite scalar quadratic recursion;
positivity then transfers the diagonal bound to the full multivariable series.
Radii are those of the associated `FormalMultilinearSeries`. Evans reads off the
convergence of the majorant from the closed form (34) in the proof of §4.6.3, Theorem 2;
here it comes from the scalar recursion.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, proof of Theorem 2, (34).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators

noncomputable section

namespace PDE.Analytic.CauchyKovalevskaya

variable (d : ℕ) (ρ α κ : ℝ)

/-- The affine spatial denominator has a nonnegative formal inverse. -/
theorem coeff_inv_spatialDenominator_nonneg (hρ : 0 ≤ ρ) (a : Fin (d + 1) →₀ ℕ) :
    0 ≤ coeff a (spatialDenominator d ρ)⁻¹ := by
  classical
  apply coeff_inv_nonneg_of_nonpos _ (by simpa using hρ) _ a
  intro b hb
  simp only [spatialDenominator, map_sub, coeff_C, ite_eq_right hb, zero_sub]
  apply neg_nonpos.mpr
  rw [map_sum]
  apply Finset.sum_nonneg
  intro j hj
  simp only [coeff_X]
  split_ifs <;> norm_num

/-- Nonnegative data select the nonnegative scalar majorant branch. -/
theorem coeff_scalarMajorant_nonneg (hρ : 0 ≤ ρ) (hα : 0 ≤ α) (hκ : 0 ≤ κ)
    (a : Fin (d + 1) →₀ ℕ) : 0 ≤ coeff a (scalarMajorant d ρ α κ) := by
  classical
  have hC (r : ℝ) (hr : 0 ≤ r) (b : Fin (d + 1) →₀ ℕ) : 0 ≤ coeff b (C r) := by
    simp only [coeff_C]
    split_ifs <;> positivity
  have hX (b : Fin (d + 1) →₀ ℕ) :
      0 ≤ coeff b (X 0 : MvPowerSeries (Fin (d + 1)) ℝ) := by
    simp only [coeff_X]
    split_ifs <;> norm_num
  exact coeff_quadraticRoot_nonneg _ _ (by simp)
    (fun b ↦ coeff_mul_nonneg (fun c ↦ coeff_mul_nonneg (hC α hα) hX c)
      (coeff_inv_spatialDenominator_nonneg d ρ hρ) b)
    (fun b ↦ coeff_mul_nonneg (hC κ hκ) (coeff_inv_spatialDenominator_nonneg d ρ hρ) b) a

/-- Collapsing the spatial variables gives the affine scalar denominator `ρ - d X`. -/
theorem rename_spatialDenominator :
    rename (fun _ : Fin (d + 1) ↦ ()) (spatialDenominator d ρ) =
      PowerSeries.C ρ - PowerSeries.C (d : ℝ) * PowerSeries.X := by
  change rename (fun _ : Fin (d + 1) ↦ ()) (spatialDenominator d ρ) =
    C ρ - C (d : ℝ) * X ()
  simp [spatialDenominator, nsmul_eq_mul]

/-- The multivariable scalar majorant has positive radius of convergence. -/
theorem radius_pos_scalarMajorant (hρ : 0 < ρ) (hα : 0 ≤ α) (hκ : 0 ≤ κ) :
    0 < (scalarMajorant d ρ α κ).toFormalMultilinearSeries.radius := by
  apply radius_pos_of_rename_constant _ (coeff_scalarMajorant_nonneg d ρ α κ hρ.le hα hκ)
  apply PowerSeries.radius_pos_of_zero_constant_quadratic _ hρ.ne'
  · change constantCoeff (rename (fun _ : Fin (d + 1) ↦ ())
      (scalarMajorant d ρ α κ)) = 0
    simp
  · have h := congrArg (rename (fun _ : Fin (d + 1) ↦ ()))
      (spatialDenominator_mul_scalarMajorant d ρ α κ hρ.ne')
    simpa only [map_mul, map_add, map_pow, rename_spatialDenominator, rename_C,
      rename_X, PowerSeries.C_apply, PowerSeries.X_apply] using h

end PDE.Analytic.CauchyKovalevskaya
