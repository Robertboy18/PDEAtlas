/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff
public import PDE.FDeriv.Operators

/-!
# Pointwise bounds for the radial cutoff

Consequences of the radial cutoff `radialCutoff R`, equal to `1` on `|x| ≤ R` and to `0` on
`|x| ≥ 2R`, in the forms used by localization arguments: smoothness of every finite order, values
in `[0, 1]`, radial symmetry, vanishing on the closed exterior `|x| ≥ 2R`, and the bounds
`|∂ᵢ χ_R| ≤ C R⁻¹`, `|∂ᵢ∂ⱼ χ_R| ≤ C R⁻²`, `|∂ᵢ∂ⱼ∂ₖ χ_R| ≤ C R⁻³`, `|Δχ_R| ≤ C R⁻²` with `C`
independent of `R`, each derivative vanishing on `|x| < R` and on `|x| > 2R`. These are the
cutoff bounds (6.17) of Chen and Hou (Part I, Section 6.2.2) for derivatives of order at most
three.

## Main results

* `contDiff_radialCutoff`: the radial cutoff is `Cᵏ` for every finite or infinite `k`.
* `radialCutoff_eq_zero_of_le_norm`: the radial cutoff vanishes on `|x| ≥ 2R`.
* `iteratedPartialDeriv_radialCutoff_eq_zero`: a nonempty derivative word of the cutoff vanishes
  on `|x| < R` and on `|x| > 2R`.
* `exists_abs_partialDeriv_radialCutoff_le`: `|∂ᵢ χ_R| ≤ C R⁻¹`.
* `exists_abs_partialDeriv_partialDeriv_radialCutoff_le`: `|∂ᵢ ∂ⱼ χ_R| ≤ C R⁻²`.
* `exists_abs_partialDeriv_partialDeriv_partialDeriv_radialCutoff_le`: `|∂ᵢ ∂ⱼ ∂ₖ χ_R| ≤ C R⁻³`.
* `exists_abs_laplacian_radialCutoff_le`: `|Δχ_R| ≤ C R⁻²`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.2.2, (6.17).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open PDE (laplacian partialDeriv iteratedPartialDeriv)
open Metric Set PDE.Common

namespace SobolevSpace.Approximation

set_option linter.missingDocs true

variable {n : ℕ}

/-- The radial cutoff is `Cᵏ` for every finite or infinite `k`. -/
theorem contDiff_radialCutoff (R : ℝ) {k : ℕ∞} : ContDiff ℝ k (radialCutoff (n := n) R) :=
  (radialCutoff_contDiff R).of_le (by exact_mod_cast le_top)

/-- The radial cutoff is nonnegative. -/
theorem radialCutoff_nonneg (R : ℝ) (x : ℝ^n) : 0 ≤ radialCutoff R x :=
  (radialCutoff_mem_Icc R x).1

/-- The radial cutoff is at most `1`. -/
theorem radialCutoff_le_one (R : ℝ) (x : ℝ^n) : radialCutoff R x ≤ 1 :=
  (radialCutoff_mem_Icc R x).2

/-- The radial cutoff vanishes on the closed exterior `|x| ≥ 2R`. -/
theorem radialCutoff_eq_zero_of_le_norm {R : ℝ} (hR : 0 < R) {x : ℝ^n} (hx : 2 * R ≤ ‖x‖) :
    radialCutoff R x = 0 := by
  simp only [radialCutoff, ContDiffBumpBase.ofInnerProductSpace]
  apply Real.smoothTransition.zero_of_nonpos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  have h : 2 ≤ R⁻¹ * ‖x‖ := by
    rw [le_inv_mul_iff₀ hR]
    linarith
  have h1 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [h1, div_one]
  linarith

/-- The radial cutoff is radial. -/
theorem radialCutoff_eq_of_norm_eq (R : ℝ) {x y : ℝ^n} (h : ‖x‖ = ‖y‖) :
    radialCutoff R x = radialCutoff R y := by
  simp only [radialCutoff, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

/-- A nonempty derivative word of the radial cutoff vanishes on `|x| < R` and on `|x| > 2R`. -/
theorem iteratedPartialDeriv_radialCutoff_eq_zero {α : List (Fin n)} (hα : α ≠ []) {R : ℝ}
    (hR : 0 < R) {x : ℝ^n} (hx : ‖x‖ < R ∨ 2 * R < ‖x‖) :
    iteratedPartialDeriv α (radialCutoff R) x = 0 := by
  rcases hx with hx | hx
  · exact radialCutoff_derivative_zero_inside α hα hR hx
  · exact radialCutoff_derivative_zero_outside α hR hx

/-- `|∂ᵢ χ_R| ≤ C R⁻¹`. -/
theorem exists_abs_partialDeriv_radialCutoff_le (i : Fin n) :
    ∃ C, 0 ≤ C ∧ ∀ R, 0 < R → ∀ x : ℝ^n, |(∂[i] (radialCutoff R)) x| ≤ C * R⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_radialCutoff_derivative_bound (n := n) [i]
  refine ⟨C, hC0, fun R hR x ↦ ?_⟩
  have h := hC R hR x
  rw [List.length_singleton, pow_one] at h
  exact h

/-- `∂ᵢ χ_R` vanishes on `|x| < R` and on `|x| > 2R`. -/
theorem partialDeriv_radialCutoff_eq_zero (i : Fin n) {R : ℝ} (hR : 0 < R) {x : ℝ^n}
    (hx : ‖x‖ < R ∨ 2 * R < ‖x‖) : (∂[i] (radialCutoff R)) x = 0 :=
  iteratedPartialDeriv_radialCutoff_eq_zero (α := [i]) (List.cons_ne_nil _ _) hR hx

/-- `|∂ᵢ ∂ⱼ χ_R| ≤ C R⁻²`. -/
theorem exists_abs_partialDeriv_partialDeriv_radialCutoff_le (i j : Fin n) :
    ∃ C, 0 ≤ C ∧ ∀ R, 0 < R → ∀ x : ℝ^n,
      |(∂[i] (∂[j] (radialCutoff R))) x| ≤ C * R⁻¹ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_radialCutoff_derivative_bound (n := n) [i, j]
  exact ⟨C, hC0, hC⟩

/-- `∂ᵢ ∂ⱼ χ_R` vanishes on `|x| < R` and on `|x| > 2R`. -/
theorem partialDeriv_partialDeriv_radialCutoff_eq_zero (i j : Fin n) {R : ℝ} (hR : 0 < R)
    {x : ℝ^n} (hx : ‖x‖ < R ∨ 2 * R < ‖x‖) : (∂[i] (∂[j] (radialCutoff R))) x = 0 :=
  iteratedPartialDeriv_radialCutoff_eq_zero (α := [i, j]) (List.cons_ne_nil _ _) hR hx

/-- `|∂ᵢ ∂ⱼ ∂ₖ χ_R| ≤ C R⁻³`. -/
theorem exists_abs_partialDeriv_partialDeriv_partialDeriv_radialCutoff_le (i j k : Fin n) :
    ∃ C, 0 ≤ C ∧ ∀ R, 0 < R → ∀ x : ℝ^n,
      |(∂[i] (∂[j] (∂[k] (radialCutoff R)))) x| ≤ C * R⁻¹ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := exists_radialCutoff_derivative_bound (n := n) [i, j, k]
  exact ⟨C, hC0, hC⟩

/-- `∂ᵢ ∂ⱼ ∂ₖ χ_R` vanishes on `|x| < R` and on `|x| > 2R`. -/
theorem partialDeriv_partialDeriv_partialDeriv_radialCutoff_eq_zero (i j k : Fin n) {R : ℝ}
    (hR : 0 < R) {x : ℝ^n} (hx : ‖x‖ < R ∨ 2 * R < ‖x‖) :
    (∂[i] (∂[j] (∂[k] (radialCutoff R)))) x = 0 :=
  iteratedPartialDeriv_radialCutoff_eq_zero (α := [i, j, k]) (List.cons_ne_nil _ _) hR hx

/-- `|Δχ_R| ≤ C R⁻²`. -/
theorem exists_abs_laplacian_radialCutoff_le :
    ∃ C, 0 ≤ C ∧ ∀ R, 0 < R → ∀ x : ℝ^n,
      |laplacian (radialCutoff R) x| ≤ C * R⁻¹ ^ 2 := by
  have h (i : Fin n) := exists_abs_partialDeriv_partialDeriv_radialCutoff_le (n := n) i i
  choose C hC0 hC using h
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ ↦ hC0 i, fun R hR x ↦ ?_⟩
  unfold laplacian
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hC i R hR x)

/-- `Δχ_R` vanishes on `|x| < R` and on `|x| > 2R`. -/
theorem laplacian_radialCutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : ℝ^n}
    (hx : ‖x‖ < R ∨ 2 * R < ‖x‖) : laplacian (radialCutoff R) x = 0 := by
  unfold laplacian
  exact Finset.sum_eq_zero fun i _ ↦ partialDeriv_partialDeriv_radialCutoff_eq_zero i i hR hx

end SobolevSpace.Approximation
