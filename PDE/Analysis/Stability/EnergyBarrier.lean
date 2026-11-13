/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
import CAS.ExactTactic

/-!
# Scalar energy barriers with arbitrary stability constants

A perturbation estimate has the form
`e' ≤ -decay * e + 2 * cubic * √e³ + 2 * error * √e`.
At radius `R`, the available forcing norm is `R * (decay / 2 - cubic * R)`.
A smaller certified residual norm makes the rate strictly inward and preserves
`e ≤ R²`. Only right derivatives are required before the terminal time.

The decay, nonlinear coefficient, forcing error, and radius are parameters.
Each PDE supplies its energy inequality and the numerical bounds that close it.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Stability

/-- Constants for a cubic perturbation-energy estimate. `forcingEnergy` bounds
the square of the residual norm; it is not an assumption about the residual. -/
structure EnergyBudget where
  /-- Decay coefficient in the differential inequality for squared energy. -/
  decay : ℝ
  /-- Coefficient of the cubic energy term before multiplication by two. -/
  cubic : ℝ
  /-- Radius of the energy ball to preserve. -/
  radius : ℝ
  /-- Certified upper bound for the squared residual norm. -/
  forcingEnergy : ℝ

/-- The largest squared residual norm that makes the boundary rate inward. -/
def EnergyBudget.maxForcingEnergy (p : EnergyBudget) : ℝ :=
  (p.radius * (p.decay / 2 - p.cubic * p.radius)) ^ 2

/-- Scalar compatibility of the proposed constants. The PDE must separately prove
its differential inequality and residual estimate with these same constants. -/
structure EnergyBudget.IsValid (p : EnergyBudget) : Prop where
  /-- The energy ball has positive radius. -/
  radius_pos : 0 < p.radius
  /-- Linear damping exceeds the cubic term on the boundary. -/
  gap_pos : 0 < p.decay / 2 - p.cubic * p.radius
  /-- The certified forcing bound lies strictly below the available damping. -/
  forcing_lt : p.forcingEnergy < p.maxForcingEnergy

/-- A squared residual bound below the available damping makes the cubic rate negative. -/
theorem cubic_energy_rate_neg_of_error_sq_lt {decay cubic error radius : ℝ}
    (hradius : 0 < radius) (hgap : 0 < decay / 2 - cubic * radius)
    (herror : error ^ 2 < (radius * (decay / 2 - cubic * radius)) ^ 2) :
    -decay * radius ^ 2 + 2 * cubic * radius ^ 3 + 2 * error * radius < 0 := by
  have hforcing : error < radius * (decay / 2 - cubic * radius) := by
    have hpositive := mul_pos hradius hgap
    nlinarith [sq_nonneg (error - radius * (decay / 2 - cubic * radius))]
  have heq : -decay * radius ^ 2 + 2 * cubic * radius ^ 3 + 2 * error * radius =
      2 * radius * (error - radius * (decay / 2 - cubic * radius)) := by cas
  rw [heq]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hradius) (sub_neg.mpr hforcing)

/-- A strict inward rate preserves a squared-energy ball on a closed time interval. -/
theorem energySquared_le_of_inward_rate
    {e rate : ℝ → ℝ} {a b decay cubic error radius : ℝ}
    (hradius : 0 ≤ radius) (he : ContinuousOn e (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt e (rate t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, e t ≤ radius ^ 2 →
      rate t ≤ -decay * e t + 2 * cubic * √(e t) ^ 3 + 2 * error * √(e t))
    (hinward : -decay * radius ^ 2 + 2 * cubic * radius ^ 3 + 2 * error * radius < 0)
    (hinit : e a ≤ radius ^ 2) : ∀ t ∈ Icc a b, e t ≤ radius ^ 2 := by
  apply image_le_of_deriv_right_lt_deriv_boundary he hderiv hinit
    (fun t ↦ hasDerivAt_const t (radius ^ 2))
  intro t ht hlevel
  have hrate := hbound t ht hlevel.le
  rw [hlevel, Real.sqrt_sq hradius] at hrate
  exact hrate.trans_lt hinward

/-- An arbitrary certified residual budget closes the cubic energy barrier. -/
theorem energySquared_le_of_error_sq_lt
    {e rate : ℝ → ℝ} {a b decay cubic error radius : ℝ}
    (hradius : 0 < radius) (hgap : 0 < decay / 2 - cubic * radius)
    (he : ContinuousOn e (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt e (rate t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, e t ≤ radius ^ 2 →
      rate t ≤ -decay * e t + 2 * cubic * √(e t) ^ 3 + 2 * error * √(e t))
    (herror : error ^ 2 < (radius * (decay / 2 - cubic * radius)) ^ 2)
    (hinit : e a ≤ radius ^ 2) : ∀ t ∈ Icc a b, e t ≤ radius ^ 2 :=
  energySquared_le_of_inward_rate hradius.le he hderiv hbound
    (cubic_energy_rate_neg_of_error_sq_lt hradius hgap herror) hinit

/-- A valid budget preserves its energy ball. Replacing the constants requires
new estimates with those constants, while the barrier argument stays the same. -/
theorem EnergyBudget.energySquared_le (p : EnergyBudget) (hp : p.IsValid)
    {e rate : ℝ → ℝ} {a b error : ℝ}
    (he : ContinuousOn e (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt e (rate t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, e t ≤ p.radius ^ 2 →
      rate t ≤ -p.decay * e t + 2 * p.cubic * √(e t) ^ 3 + 2 * error * √(e t))
    (herror : error ^ 2 ≤ p.forcingEnergy)
    (hinit : e a ≤ p.radius ^ 2) : ∀ t ∈ Icc a b, e t ≤ p.radius ^ 2 :=
  energySquared_le_of_error_sq_lt hp.radius_pos hp.gap_pos he hderiv hbound
    (herror.trans_lt hp.forcing_lt) hinit

end PDE.Analysis.Stability
