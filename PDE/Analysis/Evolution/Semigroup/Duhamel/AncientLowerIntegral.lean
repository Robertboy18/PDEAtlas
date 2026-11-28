/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Group.LIntegral
public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientSmoothing

/-!
# The mass of the smoothing kernel over the past, as a lower integral

An ancient Duhamel integral `∫_{-∞}^τ K(τ - s) G(s) ds` with a kernel that is singular like
`(τ - s)^{-α}`, `α < 1`, and a forcing of size `e^{as}` is bounded by
`∫_{-∞}^τ (τ - s)^{-α} e^{as} ds = e^{aτ} Γ(1 - α) / a^{1-α}`. This module computes that integral
as a lower integral in the variable `s`, the form needed when the norm of the integrand is only
known as a number in `[0, ∞]`, for instance a Sobolev norm of a function with values in `L²`.
For a forcing with values in a Banach space the bound is `norm_ancientDuhamel_le`, written with
the lag `r = τ - s`.

## Main results

* `lintegral_Iio_comp_sub_left`: `∫_{s<τ} F(τ - s) ds = ∫_{r>0} F(r) dr` for every function `F`
  with values in `[0, ∞]`.
* `lintegral_Iio_rpow_mul_exp`: `∫_{-∞}^τ (τ - s)^{-α} e^{as} ds = e^{aτ} Γ(1 - α) / a^{1-α}` for
  `α < 1` and `a > 0`.

## How it works

The reflection `s ↦ τ - s` preserves Lebesgue measure (`lintegral_sub_left_eq_self`) and maps
the half-line `s < τ` onto `r > 0`. There the integrand is `e^{aτ} r^{-α} e^{-ar}`, whose
integral is `smoothingMass α a = Γ(1 - α) / a^{1-α}` (`integral_smoothingWeight`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

/-- **Reflection of a half-line**: `∫_{s<τ} F(τ - s) ds = ∫_{r>0} F(r) dr` for the lower integral
of every function `F` with values in `[0, ∞]`. Lebesgue measure is invariant under
`s ↦ τ - s`. -/
theorem lintegral_Iio_comp_sub_left (F : ℝ → ℝ≥0∞) (τ : ℝ) :
    ∫⁻ s in Iio τ, F (τ - s) = ∫⁻ r in Ioi (0 : ℝ), F r := by
  rw [← lintegral_indicator measurableSet_Iio, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_sub_left_eq_self ((Ioi (0 : ℝ)).indicator F) τ]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : s < τ
  · rw [indicator_of_mem (mem_Iio.2 hs), indicator_of_mem (mem_Ioi.2 (sub_pos.2 hs))]
  · rw [indicator_of_notMem fun h ↦ hs (mem_Iio.1 h),
      indicator_of_notMem fun h ↦ hs (sub_pos.1 (mem_Ioi.1 h))]

/-- **The mass of the smoothing kernel against an exponential weight**: for `α < 1`, `a > 0`
and every `τ`,

`∫_{-∞}^τ (τ - s)^{-α} e^{as} ds = e^{aτ} Γ(1 - α) / a^{1-α}`,

as a lower integral. With the lag `r = τ - s` the integrand is `e^{aτ} r^{-α} e^{-ar}`. -/
theorem lintegral_Iio_rpow_mul_exp {α a : ℝ} (hα : α < 1) (ha : 0 < a) (τ : ℝ) :
    ∫⁻ s in Iio τ, ENNReal.ofReal ((τ - s) ^ (-α) * Real.exp (a * s)) =
      ENNReal.ofReal (Real.exp (a * τ) * smoothingMass α a) := by
  have h1 : ∀ s : ℝ, ENNReal.ofReal ((τ - s) ^ (-α) * Real.exp (a * s)) =
      (fun r ↦ ENNReal.ofReal (Real.exp (a * τ) * smoothingWeight α a r)) (τ - s) := fun s ↦ by
    change _ = ENNReal.ofReal (Real.exp (a * τ) * ((τ - s) ^ (-α) * Real.exp (-(a * (τ - s)))))
    congr 1
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r ↦
      Real.exp (a * τ) * smoothingWeight α a r :=
    (ae_restrict_mem measurableSet_Ioi).mono fun r hr ↦ mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le)
  calc ∫⁻ s in Iio τ, ENNReal.ofReal ((τ - s) ^ (-α) * Real.exp (a * s))
      = ∫⁻ s in Iio τ,
          (fun r ↦ ENNReal.ofReal (Real.exp (a * τ) * smoothingWeight α a r)) (τ - s) :=
        lintegral_congr h1
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (a * τ) * smoothingWeight α a r) :=
        lintegral_Iio_comp_sub_left
          (fun r ↦ ENNReal.ofReal (Real.exp (a * τ) * smoothingWeight α a r)) τ
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_smoothingWeight hα ha).const_mul _) hnn, integral_const_mul,
          integral_smoothingWeight hα ha]

end PDE.Analysis.Evolution
