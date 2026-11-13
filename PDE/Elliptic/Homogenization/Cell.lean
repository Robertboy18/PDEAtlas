/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import PDE.Analysis.Integration.PeriodicAveraging.Primitive

/-!
# The one-dimensional periodic elliptic cell problem

For a positive continuous one-periodic coefficient, the effective coefficient is the
harmonic mean. The normalized corrector is the primitive of `aHom / a - 1`; its
periodicity follows from the cell mean, and its flux is the constant `aHom`.

This specializes the periodic cell problem in Evans, *Partial Differential Equations*,
second edition (2010), §4.5.4, Example 5, equation (69), p. 231, to one dimension.
The multidimensional cell problem is `Homogenization.PeriodicCell`.
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.Homogenization

open MeasureTheory Set
open PDE.Analysis.PeriodicAveraging

/-- A scalar periodic material; positivity and continuity imply uniform ellipticity. -/
structure PeriodicMedium where
  /-- The microscopic diffusion coefficient. -/
  coefficient : ℝ → ℝ
  /-- Continuity of the coefficient. -/
  continuous : Continuous coefficient
  /-- Unit periodicity of the coefficient. -/
  periodic : Function.Periodic coefficient 1
  /-- Strict positivity of the coefficient. -/
  positive : ∀ x, 0 < coefficient x

namespace PeriodicMedium

variable (a : PeriodicMedium)

/-- The reciprocal coefficient. -/
def reciprocal (x : ℝ) : ℝ := (a.coefficient x)⁻¹

/-- The average reciprocal coefficient. -/
def meanReciprocal : ℝ := mean a.reciprocal

/-- The effective diffusion coefficient, the harmonic mean over the unit cell. -/
def effective : ℝ := a.meanReciprocal⁻¹

/-- The corrector normalized by its value at zero. -/
def corrector (y : ℝ) : ℝ := a.effective * fluctuation a.reciprocal y

/-- The reciprocal coefficient is continuous. -/
theorem continuous_reciprocal : Continuous a.reciprocal :=
  a.continuous.inv₀ (fun x ↦ (a.positive x).ne')

/-- The reciprocal has the same period as the coefficient. -/
theorem periodic_reciprocal : Function.Periodic a.reciprocal 1 :=
  fun x ↦ by simp only [reciprocal, a.periodic x]

/-- The reciprocal coefficient is positive. -/
theorem reciprocal_pos (x : ℝ) : 0 < a.reciprocal x := inv_pos.mpr (a.positive x)

/-- The cell integral of the reciprocal is strictly positive. -/
theorem meanReciprocal_pos : 0 < a.meanReciprocal := by
  exact intervalIntegral.integral_pos zero_lt_one a.continuous_reciprocal.continuousOn
    (fun x _ ↦ (a.reciprocal_pos x).le) ⟨0, by simp, a.reciprocal_pos 0⟩

/-- The effective coefficient is strictly positive. -/
theorem effective_pos : 0 < a.effective := inv_pos.mpr a.meanReciprocal_pos

/-- The effective coefficient is the reciprocal of the integral of the reciprocal. -/
theorem effective_eq_harmonic_mean :
    a.effective = (∫ y in (0 : ℝ)..1, (a.coefficient y)⁻¹)⁻¹ := rfl

/-- The cell corrector is periodic. -/
theorem periodic_corrector : Function.Periodic a.corrector 1 :=
  fun x ↦ by
    simp only [corrector, periodic_fluctuation a.continuous_reciprocal a.periodic_reciprocal x]

/-- The normalization fixes the additive constant in the corrector. -/
@[simp] theorem corrector_zero : a.corrector 0 = 0 := by simp [corrector]

/-- The corrector gradient solves the algebraic cell flux equation. -/
theorem hasDerivAt_corrector (y : ℝ) :
    HasDerivAt a.corrector (a.effective * a.reciprocal y - 1) y := by
  unfold corrector
  have hm : mean a.reciprocal ≠ 0 := a.meanReciprocal_pos.ne'
  convert (hasDerivAt_fluctuation a.continuous_reciprocal y).const_mul a.effective using 1
  simp [effective, meanReciprocal, mul_sub, hm]

/-- The periodic corrector has a continuous first derivative for a continuous medium. -/
theorem contDiff_corrector : ContDiff ℝ 1 a.corrector := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y ↦ (a.hasDerivAt_corrector y).differentiableAt, ?_⟩
  have hd : deriv a.corrector = fun y ↦ a.effective * a.reciprocal y - 1 :=
    funext fun y ↦ (a.hasDerivAt_corrector y).deriv
  rw [hd]
  exact (continuous_const.mul a.continuous_reciprocal).sub continuous_const

/-- The cell flux is constant, hence has zero divergence. -/
theorem cell_flux (y : ℝ) :
    a.coefficient y * (1 + deriv a.corrector y) = a.effective := by
  rw [(a.hasDerivAt_corrector y).deriv]
  dsimp [reciprocal]
  have ha := (a.positive y).ne'
  field_simp
  simp_all

/-- The corrector solves the cell equation in flux form. -/
theorem hasDerivAt_cell_flux (y : ℝ) :
    HasDerivAt (fun z ↦ a.coefficient z * (1 + deriv a.corrector z)) 0 y := by
  simpa only [a.cell_flux] using hasDerivAt_const y a.effective

/-- The periodic corrector is bounded on the whole line. -/
theorem exists_corrector_bound : ∃ K > 0, ∀ y, |a.corrector y| ≤ K := by
  obtain ⟨K, hK, hb⟩ :=
    (a.periodic_corrector.isBounded_of_continuous one_ne_zero
      a.contDiff_corrector.continuous).exists_pos_norm_le
  exact ⟨K, hK, fun y ↦ by simpa only [Real.norm_eq_abs] using hb _ (mem_range_self y)⟩

/-- Positivity and periodicity give global upper and strictly positive lower bounds. -/
theorem exists_ellipticity_bounds :
    ∃ α > 0, ∃ β > 0, ∀ y, α ≤ a.coefficient y ∧ a.coefficient y ≤ β := by
  have hc := a.periodic.compact_of_continuous one_ne_zero a.continuous
  obtain ⟨α, hα, hmin⟩ := hc.exists_isMinOn (range_nonempty a.coefficient) continuousOn_id
  obtain ⟨y, rfl⟩ := hα
  obtain ⟨β, hβ, hmax⟩ := hc.isBounded.exists_pos_norm_le
  refine ⟨a.coefficient y, a.positive y, β, hβ, fun z ↦ ⟨hmin (mem_range_self z), ?_⟩⟩
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using hmax _ (mem_range_self z))

/-- Every differentiable periodic cell solution has the harmonic-mean flux.
This characterizes the effective coefficient independently of our corrector construction. -/
theorem effective_eq_of_cell_flux {χ : ℝ → ℝ} {c : ℝ}
    (hχ : Differentiable ℝ χ) (hp : Function.Periodic χ 1)
    (hflux : ∀ y, a.coefficient y * (1 + deriv χ y) = c) : c = a.effective := by
  have hd (y : ℝ) : HasDerivAt χ (c * a.reciprocal y - 1) y := by
    have he : 1 + deriv χ y = c / a.coefficient y := by
      apply (eq_div_iff (a.positive y).ne').mpr
      simpa only [mul_comm] using hflux y
    have he' : deriv χ y = c * a.reciprocal y - 1 := by
      dsimp [reciprocal]
      rw [div_eq_mul_inv] at he
      linarith
    exact he' ▸ (hχ y).hasDerivAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun y _ ↦ hd y)
    (((continuous_const.mul a.continuous_reciprocal).sub continuous_const).intervalIntegrable 0 1)
  have hp0 : χ 1 = χ 0 := by simpa using hp 0
  rw [hp0, sub_self] at hi
  rw [intervalIntegral.integral_sub
    (f := fun y ↦ c * a.reciprocal y) (g := fun _ ↦ (1 : ℝ))
    ((continuous_const.mul a.continuous_reciprocal).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_const_mul] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hi
  have he : c * a.meanReciprocal = 1 := by
    change c * mean a.reciprocal = 1
    dsimp [mean]
    linarith
  unfold effective
  rw [inv_eq_one_div]
  exact (eq_div_iff a.meanReciprocal_pos.ne').mpr he

end PeriodicMedium

end PDE.Elliptic.Homogenization
