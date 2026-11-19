/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Majorization
public import PDE.Analysis.Analytic.PowerSeries.Multiindex
public import Mathlib.Data.Sym.Card

/-!
# Native convergence from formal coefficient majorants

For a series with nonnegative real coefficients, evaluating a homogeneous
polynomial on the all-ones vector gives the sum of its coefficients. This
compares its native multilinear norm with the coefficient bounds used in
formal majorant arguments, including a space with no coordinates.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace MvPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Realize a real multivariable formal series as a native formal multilinear series. -/
def toFormalMultilinearSeries (f : MvPowerSeries ι ℝ) :
    FormalMultilinearSeries ℝ (ι → ℝ) ℝ :=
  FormalMultilinearSeries.ofMultiindexCoefficients fun a ↦ coeff a f

/-- On the all-ones vector, each coordinate monomial contributes exactly its coefficient. -/
theorem toFormalMultilinearSeries_apply_one (f : MvPowerSeries ι ℝ) (n : ℕ) :
    f.toFormalMultilinearSeries n (fun _ ↦ 1) =
      ∑ s : Sym ι n, coeff (s : Multiset ι).toFinsupp f := by
  simp [toFormalMultilinearSeries, FormalMultilinearSeries.ofMultiindexCoefficients_apply]

/-- An absolute coefficient majorant also majorizes the native homogeneous operator norms. -/
theorem IsMajorizedOn.norm_toFormalMultilinearSeries_le
    {f g : MvPowerSeries ι ℝ} (h : IsMajorizedOn f g Set.univ) (n : ℕ) :
    ‖f.toFormalMultilinearSeries n‖ ≤ ‖g.toFormalMultilinearSeries n‖ := by
  have hones : ‖(1 : ι → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    simp
  calc
    ‖f.toFormalMultilinearSeries n‖ ≤
        ∑ s : Sym ι n, ‖coeff (s : Multiset ι).toFinsupp f‖ :=
      FormalMultilinearSeries.norm_ofMultiindexCoefficients_le _ n
    _ ≤ ∑ s : Sym ι n, coeff (s : Multiset ι).toFinsupp g :=
      Finset.sum_le_sum fun s _ ↦ h _ (Set.mem_univ _)
    _ = g.toFormalMultilinearSeries n (fun _ ↦ 1) :=
      (g.toFormalMultilinearSeries_apply_one n).symm
    _ ≤ ‖g.toFormalMultilinearSeries n (fun _ ↦ 1)‖ := le_abs_self _
    _ ≤ ‖g.toFormalMultilinearSeries n‖ := by
      simpa using (g.toFormalMultilinearSeries n).le_opNorm_mul_prod_of_le (fun _ ↦ hones)

/-- Coefficient majorization reverses the inequality between convergence radii. -/
theorem IsMajorizedOn.radius_le
    {f g : MvPowerSeries ι ℝ} (h : IsMajorizedOn f g Set.univ) :
    g.toFormalMultilinearSeries.radius ≤ f.toFormalMultilinearSeries.radius :=
  FormalMultilinearSeries.radius_le_of_le h.norm_toFormalMultilinearSeries_le

/-- An exponential bound in total degree gives a positive native analytic radius.
The number of multiindices of each degree introduces only an exponential factor. -/
theorem radius_pos_of_coeff_bound (f : MvPowerSeries ι ℝ) {C r : ℝ}
    (hr : 0 < r) (hf : ∀ a, ‖coeff a f‖ ≤ C * r ^ (a.sum fun _ ↦ id)) :
    0 < f.toFormalMultilinearSeries.radius := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hf 0)
    simpa using h
  apply FormalMultilinearSeries.radius_pos_of_multiindex_bound _
    (mul_pos (show (0 : ℝ) < 2 by norm_num) hr)
    (C := (2 : ℝ) ^ Fintype.card ι * C)
  intro n
  have hcard : Fintype.card (Sym ι n) ≤ 2 ^ (Fintype.card ι + n) := by
    rw [Sym.card_sym_eq_choose]
    exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide)
      (Nat.sub_le _ _))
  have hcard' : (Fintype.card (Sym ι n) : ℝ) ≤
      (2 : ℝ) ^ (Fintype.card ι + n) := by exact_mod_cast hcard
  calc
    ∑ s : Sym ι n, ‖coeff (s : Multiset ι).toFinsupp f‖ ≤
        ∑ _s : Sym ι n, C * r ^ n := by
      apply Finset.sum_le_sum
      intro s hs
      simpa using hf (s : Multiset ι).toFinsupp
    _ = (Fintype.card (Sym ι n) : ℝ) * (C * r ^ n) := by simp
    _ ≤ (2 : ℝ) ^ (Fintype.card ι + n) * (C * r ^ n) :=
      mul_le_mul_of_nonneg_right hcard' (mul_nonneg hC (pow_nonneg hr.le _))
    _ = ((2 : ℝ) ^ Fintype.card ι * C) * (2 * r) ^ n := by
      rw [pow_add, mul_pow]
      ring

end MvPowerSeries
