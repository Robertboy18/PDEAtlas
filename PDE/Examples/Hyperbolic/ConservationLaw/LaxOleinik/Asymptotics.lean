/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Decay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import CAS.ExactTactic

/-!
# Decay for a drifting quartic flux and noncompact initial data

The normalized quartic flux has drift two and no upper Hessian bound. The
Cauchy datum `1/(1 + x²)` is nonzero everywhere, with integral `π`. The Lax–Oleinik
solution is a weak solution (`driftingQuarticFlux_cauchy_solution`) and satisfies
`|u(t, x)| ≤ √(2π)/√t` (`driftingQuarticFlux_cauchy_decay`, from
`abs_solution_le_sqrt_div_sqrt`).
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- A normalized quartic flux with nonzero characteristic drift. -/
def driftingQuarticFlux (r : ℝ) : ℝ :=
  r ^ 4 / 4 + r ^ 2 / 2 + 2 * r

/-- The flux is `C²`. -/
theorem driftingQuarticFlux_contDiff : ContDiff ℝ 2 driftingQuarticFlux := by
  unfold driftingQuarticFlux
  fun_prop

/-- The derivative of the flux is `r³ + r + 2`. -/
theorem driftingQuarticFlux_deriv (r : ℝ) :
    deriv driftingQuarticFlux r = r ^ 3 + r + 2 := by
  cas

/-- The second derivative of the flux is `3r² + 1`. -/
theorem driftingQuarticFlux_deriv2 (r : ℝ) :
    deriv (deriv driftingQuarticFlux) r = 3 * r ^ 2 + 1 := by
  rw [show deriv driftingQuarticFlux = fun q ↦ q ^ 3 + q + 2 from
    funext driftingQuarticFlux_deriv]
  cas

/-- Uniform convexity holds with modulus one. -/
theorem driftingQuarticFlux_deriv2_lower (r : ℝ) :
    1 ≤ deriv (deriv driftingQuarticFlux) r := by
  rw [driftingQuarticFlux_deriv2]
  nlinarith [sq_nonneg r]

/-- The second derivative of the flux has no upper bound. -/
theorem driftingQuarticFlux_no_deriv2_upper :
    ¬ ∃ B : ℝ, ∀ r, deriv (deriv driftingQuarticFlux) r ≤ B := by
  rintro ⟨B, hB⟩
  have h := hB (B + 1)
  rw [driftingQuarticFlux_deriv2] at h
  nlinarith [sq_nonneg (B + 5 / 6)]

/-- Integrable initial data with noncompact support. -/
def cauchyDatum (x : ℝ) : ℝ := (1 + x ^ 2)⁻¹

/-- The datum is strictly positive at every point of the real line. -/
theorem cauchyDatum_pos (x : ℝ) : 0 < cauchyDatum x := by
  unfold cauchyDatum
  positivity

/-- The datum is integrable on the whole, unbounded spatial domain. -/
theorem cauchyDatum_integrable : Integrable cauchyDatum volume :=
  integrable_inv_one_add_sq

/-- Its essential supremum is at most one. -/
theorem cauchyDatum_memLp : MemLp cauchyDatum ∞ volume := by
  apply memLp_top_of_bound cauchyDatum_integrable.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (cauchyDatum_pos x)]
  change (1 + x ^ 2)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])

/-- The `L¹` norm of the datum is `π`. -/
theorem integral_abs_cauchyDatum : (∫ x, |cauchyDatum x|) = Real.pi := by
  simp_rw [abs_of_pos (cauchyDatum_pos _)]
  exact integral_univ_inv_one_add_sq

/-- The variational solution satisfies the weak initial-value
identity for the nonzero, noncompact datum. -/
theorem driftingQuarticFlux_cauchy_solution :
    IsWeakInitialValueSolution driftingQuarticFlux cauchyDatum
      (solution driftingQuarticFlux cauchyDatum) ∧
      MemLp (solution driftingQuarticFlux cauchyDatum) ∞ volume :=
  solution_spec_of_deriv2_lower_bound driftingQuarticFlux_contDiff (by norm_num)
    driftingQuarticFlux_deriv2_lower cauchyDatum_memLp

/-- For `t > 0`, the solution satisfies `|u(t, x)| ≤ √(2π)/√t`. -/
theorem driftingQuarticFlux_cauchy_decay {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |solution driftingQuarticFlux cauchyDatum !₂[t, x]| ≤
      √(2 * Real.pi) / √t := by
  simpa only [integral_abs_cauchyDatum, div_one] using
    abs_solution_le_sqrt_div_sqrt driftingQuarticFlux_contDiff (by norm_num)
      driftingQuarticFlux_deriv2_lower (by norm_num [driftingQuarticFlux])
      cauchyDatum_memLp cauchyDatum_integrable ht x

end PDE.Examples.ConservationLaw.LaxOleinik
