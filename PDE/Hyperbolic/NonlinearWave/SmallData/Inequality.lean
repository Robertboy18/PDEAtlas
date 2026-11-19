/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Growth
public import PDE.Hyperbolic.NonlinearWave.SmallData.Holder

/-!
# A mass differential inequality from the semilinear wave equation

For a jointly `C²` real field satisfying `u_tt - Δu = |u|^p`, forward finite propagation
gives the exact mass identity and Jensen lower bound with coefficient `|B(0,1)|^(1-p)`.
Positive integral of the prescribed initial velocity then yields a positive mass derivative
and an affine mass lower bound.

These are inputs to a small-data blowup argument. The PDE assumptions are explicit.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common
open PDE.Analysis (unitBallVolume)

namespace WaveEquation.SmallData

variable {n : ℕ}

/-- The positive ball-volume coefficient in the spatial mass inequality. -/
def massCoefficient (n : ℕ) (p : ℝ) : ℝ :=
  unitBallVolume n ^ (1 - p)

/-- The coefficient is positive for every real exponent. -/
theorem massCoefficient_pos (n : ℕ) (p : ℝ) : 0 < massCoefficient n p :=
  Real.rpow_pos_of_pos (by unfold unitBallVolume; positivity) _

/-- The ordinary second derivative satisfies the quantitative mass inequality. -/
theorem spatialMass_differential_inequality {u : ℝ^(n + 1) → ℝ} {R p t : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p) (ht : 0 < t)
    (hwave : ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p) :
    massCoefficient n p * (R + t) ^ (-(n : ℝ) * (p - 1)) *
      |spatialMass u t| ^ p ≤ deriv (deriv (spatialMass u)) t := by
  rw [deriv_deriv_spatialMass_eq_source hu hs ht hwave]
  exact radius_mass_bound
    (hu.continuous.comp (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous)
    (add_pos hR ht) hp.le (hs t ht.le)

/-- Cauchy-data endpoint: exact mass identity, ball-volume inequality, and initial-data growth.

The field is jointly `C²`; the equation is required at positive times and support only at
nonnegative times. The initial velocity is the coordinate derivative, with positive
integral. The initial displacement can have either sign.
-/
theorem cauchy_spatialMass_estimates {u : ℝ^(n + 1) → ℝ} {h : ℝ^n → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hR : 0 < R) (hp : 1 < p)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hinitial : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons 0 x) = h x) (hpositive : 0 < ∫ x : ℝ^n, h x) :
    (∀ t, 0 < t →
      deriv (deriv (spatialMass u)) t = (∫ x : ℝ^n, |u (timeSpaceCons t x)| ^ p) ∧
      massCoefficient n p * (R + t) ^ (-(n : ℝ) * (p - 1)) *
        |spatialMass u t| ^ p ≤ deriv (deriv (spatialMass u)) t ∧
      0 < deriv (spatialMass u) t) ∧
    (∀ t, 0 ≤ t → spatialMass u 0 + (∫ x : ℝ^n, h x) * t ≤ spatialMass u t) := by
  have hmass : spatialMass (∂[0] u) 0 = ∫ x : ℝ^n, h x := by
    unfold spatialMass
    simp_rw [hinitial]
  constructor
  · exact fun t ht ↦ ⟨deriv_deriv_spatialMass_eq_source hu hs ht (hwave t ht),
      spatialMass_differential_inequality hu hs hR hp ht (hwave t ht),
      deriv_spatialMass_pos hu hs hwave (hmass.symm ▸ hpositive) ht⟩
  · intro t ht
    rw [← hmass]
    exact initial_affine_le_spatialMass hu hs hwave ht

end WaveEquation.SmallData
