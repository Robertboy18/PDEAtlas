/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Constraints.Multiplier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import CAS.ExactTactic

/-!
# A nonconstant constraint with a degenerate minimizer

The potential `(1 - cos(s²))/2` is nonconstant and smooth, with linearly
growing derivative `s * sin(s²)`. Zero is a constrained Dirichlet minimizer
whose constraint derivative vanishes. The degenerate endpoint supplies every
real scalar as a multiplier, with no nondegeneracy hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Examples.CalculusOfVariations.Constraints

/-- A nonconstant smooth constraint potential vanishing at zero. -/
def cosinePotential (s : ℝ) : ℝ := (1 - Real.cos (s ^ 2)) / 2

/-- Its linearly growing derivative. -/
def cosineSlope (s : ℝ) : ℝ := s * Real.sin (s ^ 2)

/-- The derivative of `cosinePotential` is `cosineSlope`. -/
theorem cosinePotential_hasDerivAt (s : ℝ) :
    HasDerivAt cosinePotential (cosineSlope s) s := by
  unfold cosinePotential cosineSlope
  cas

/-- The slope is smooth. -/
theorem contDiff_cosineSlope : ContDiff ℝ (⊤ : ℕ∞) cosineSlope := by
  unfold cosineSlope
  fun_prop

/-- The slope grows at most linearly: `|cosineSlope s| ≤ 1 + |s|`. -/
theorem cosineSlope_growth (s : ℝ) : |cosineSlope s| ≤ 1 * (1 + |s|) := by
  have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (s ^ 2)) (abs_nonneg s)
  simp only [cosineSlope, abs_mul, one_mul]
  linarith

/-- The constraint potential is not constant: its values at zero and `√π`
are distinct. -/
theorem cosinePotential_nonconstant :
    cosinePotential (Real.sqrt Real.pi) ≠ cosinePotential 0 := by
  norm_num [cosinePotential, Real.sq_sqrt Real.pi_pos.le]

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Zero is a global constrained minimizer of this nonconstant potential on
every domain. -/
theorem cosinePotential_zero_minimizer :
    integralConstraint (n := n) (Ω := Ω) cosinePotential 0 = 0 ∧
      IsMinOn (dirichletEnergy 0)
        {v : H¹₀(Ω) | integralConstraint cosinePotential v = 0} 0 := by
  constructor
  · simp [integralConstraint_zero, cosinePotential]
  · intro v _
    change dirichletEnergy 0 (0 : H¹₀(Ω)) ≤ dirichletEnergy 0 v
    rw [dirichletEnergy_zero_eq_norm_gradient_sq, dirichletEnergy_zero_eq_norm_gradient_sq]
    simp only [Submodule.coe_zero, map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    positivity

/-- The derivative of the constraint vanishes at its minimizer. -/
theorem cosinePotential_constraint_derivative_zero
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    fderiv ℝ (integralConstraint (n := n) (Ω := Ω) cosinePotential) 0 = 0 := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    ⟨by simpa [domainMeasure] using hΩb.measure_lt_top (μ := volume)⟩
  apply (integralConstraint_fderiv_eq_zero_iff hΩ
    cosinePotential_hasDerivAt contDiff_cosineSlope.continuous cosineSlope_growth 0).mpr
  filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
  simp only [map_zero, hx, cosineSlope, zero_mul, Pi.zero_apply]

/-- At the degenerate minimizer zero, the Lagrange multiplier equation holds for every
real multiplier `lam`. -/
theorem cosinePotential_every_multiplier
    (hn : 0 < n) (hΩ : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (lam : ℝ) (v : H¹₀(Ω)) :
    (∫ x, inner ℝ (∇ ((0 : H¹₀(Ω)) : H¹(Ω)) x) (∇ (v : H¹(Ω)) x)
      ∂domainMeasure n Ω) =
      lam * ∫ x, cosineSlope (baseCoordCLM (0 : H¹₀(Ω)) x) * baseCoordCLM v x
        ∂domainMeasure n Ω := by
  rw [← dirichletForm_eq_integral_gradient]
  apply integralConstraint_minimizer_weak_eq_of_deriv_ae_eq_zero hn hΩ hΩb
    contDiff_cosineSlope cosinePotential_hasDerivAt
    cosinePotential_zero_minimizer.1 cosinePotential_zero_minimizer.2
  filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
  simp only [map_zero, hx, cosineSlope, zero_mul, Pi.zero_apply]

end PDE.Examples.CalculusOfVariations.Constraints
