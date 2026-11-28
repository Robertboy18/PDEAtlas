/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Minkowski's inequality for a supremum of continuous seminorms

A regularity norm `q` with values in `[0, ∞]` on a Banach space `X` is often finite on a smaller
space only, for example a Sobolev norm on `L²`. If `q` is the supremum of continuous seminorms,
`q x = sup_N ‖T_N x‖` with bounded operators `T_N` into Banach spaces, then `q(∫ g) ≤ ∫ q(g)`
for every measure and every `g : α → X`. The integral is taken in `X`, where `q` is not
continuous, `g` need not be measurable for the stronger norm, and nothing is assumed finite. If
`g` is not Bochner integrable its integral is zero by convention, so the statement carries
information for integrable `g` only. Seminorms that do not come from bounded operators into
normed spaces are not treated.

## Main results

* `iSup_eNorm_integral_le`: `q(∫ g) ≤ ∫ q(g)` for `q x = sup_N ‖T_N x‖`, with the Bochner
  integral in `X` on the left and a lower integral on the right.
* `rpow_half_integral_le_of_eq_iSup`: `E(∫ g)^{1/2} ≤ ∫ E(g)^{1/2}` for an energy
  `E x = sup_N ‖T_N x‖²`. The Sobolev energy of real order is such a supremum, with the frequency
  cut-offs as the operators (`SobolevSpace.Fractional.besselEnergy_integral_le`).

## How it works

Each `T_N` commutes with the Bochner integral (`ContinuousLinearMap.integral_comp_comm`), so
`‖T_N ∫ g‖ = ‖∫ T_N g‖ ≤ ∫ ‖T_N g‖ ≤ ∫ q(g)`, and the supremum over `N` is taken at the end.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Analysis

variable {α X κ : Type*} {Y : κ → Type*} [MeasurableSpace α] {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [CompleteSpace X]
  [∀ N, NormedAddCommGroup (Y N)] [∀ N, NormedSpace 𝕜 (Y N)] [∀ N, NormedSpace ℝ (Y N)]
  [∀ N, CompleteSpace (Y N)]

/-- **Minkowski's inequality for a supremum of continuous seminorms.** Let `q x = sup_N ‖T_N x‖`
on a Banach space `X`, with bounded operators `T_N` into Banach spaces. Then, for every measure
`μ` and every `g : α → X`,

`q(∫ g dμ) ≤ ∫ q(g) dμ`,

where the left integral is the Bochner integral in `X` and the right one is the lower integral.
Each `T_N` commutes with the Bochner integral. If `g` is not integrable, the left side is
zero. -/
theorem iSup_eNorm_integral_le (T : ∀ N, X →L[𝕜] Y N) (g : α → X) :
    ⨆ N, ‖T N (∫ a, g a ∂μ)‖ₑ ≤ ∫⁻ a, ⨆ N, ‖T N (g a)‖ₑ ∂μ := by
  by_cases hg : Integrable g μ
  · refine iSup_le fun N ↦ ?_
    rw [← (T N).integral_comp_comm hg]
    exact (eNorm_integral_le_lintegral_eNorm _).trans
      (lintegral_mono fun a ↦ le_iSup (fun N ↦ ‖T N (g a)‖ₑ) N)
  · rw [integral_undef hg]
    simp

/-- **Minkowski's inequality for an energy that is a supremum of squares of continuous
seminorms.** Let `E x = sup_N ‖T_N x‖²`. Then, for every measure `μ` and every `g : α → X`,

`E(∫ g dμ)^{1/2} ≤ ∫ E(g)^{1/2} dμ`.

The square root of `E` is the supremum of the seminorms, so this is
`iSup_eNorm_integral_le`. -/
theorem rpow_half_integral_le_of_eq_iSup {E : X → ℝ≥0∞} (T : ∀ N, X →L[𝕜] Y N)
    (hE : ∀ x, E x = ⨆ N, ‖T N x‖ₑ ^ 2) (g : α → X) :
    E (∫ a, g a ∂μ) ^ (1 / 2 : ℝ) ≤ ∫⁻ a, E (g a) ^ (1 / 2 : ℝ) ∂μ := by
  have hsq : ∀ c : ℝ≥0∞, (c ^ 2) ^ (1 / 2 : ℝ) = c := fun c ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hroot : ∀ x, E x ^ (1 / 2 : ℝ) = ⨆ N, ‖T N x‖ₑ := fun x ↦ by
    rw [hE]
    refine le_antisymm ?_ (iSup_le fun N ↦ ?_)
    · refine (ENNReal.rpow_le_rpow (iSup_le fun N ↦ pow_le_pow_left₀ zero_le
        (le_iSup (fun N ↦ ‖T N x‖ₑ) N) 2) (by norm_num)).trans_eq (hsq _)
    · exact (hsq _).symm.trans_le
        (ENNReal.rpow_le_rpow (le_iSup (fun N ↦ ‖T N x‖ₑ ^ 2) N) (by norm_num))
  simp only [hroot]
  exact iSup_eNorm_integral_le T g

end PDE.Analysis
