/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Equation
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound

/-!
# Finite propagation for defocusing power waves

We specialize the semilinear cone-energy argument to

`uₜₜ - Δu + massSq * u + coupling * u^(2k+1) = 0`.

When both coefficients are nonnegative, the canonical odd-power potential is
nonnegative and vanishes at the origin. The general semilinear finite
propagation theorem therefore applies. The statements below use the concrete
equation, on the closed and on the open backward cone.
-/

@[expose] public section

noncomputable section

open PDE.Analysis.Scalar
open Set

namespace WaveEquation

variable {n : ℕ}

/-- A classical defocusing power wave with zero Cauchy data on a closed base
ball vanishes throughout the corresponding closed backward cone. -/
theorem eq_zero_on_closed_backwardCone_defocusingPower [Fact (0 < n)] {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + massSq * u p +
      coupling * (u p) ^ (2 * k + 1) = 0)
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  apply eq_zero_on_closed_backwardCone_semilinear (n := n)
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp))
    (oddPowerPotential_nonneg k hmassSq hcoupling) (oddPowerPotential_zero massSq coupling k) hu c
  · intro t ht x hx
    simpa only [semilinearWaveOperator_oddPowerPotential] using hwave t ht x hx
  · exact hpos
  · exact hvel

/-- A classical defocusing power wave with zero Cauchy data on an open base
ball vanishes throughout the corresponding open backward cone. -/
theorem eq_zero_on_open_backwardCone_defocusingPower [Fact (0 < n)] {massSq coupling : ℝ} (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + massSq * u p +
      coupling * (u p) ^ (2 * k + 1) = 0)
    (hpos : ∀ x ∈ Metric.ball c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  apply eq_zero_on_open_backwardCone_semilinear (n := n)
    ((contDiff_oddPowerPotential massSq coupling k).of_le (by simp))
    (oddPowerPotential_nonneg k hmassSq hcoupling) (oddPowerPotential_zero massSq coupling k) hu c
  · intro t ht x hx
    simpa only [semilinearWaveOperator_oddPowerPotential] using hwave t ht x hx
  · exact hpos
  · exact hvel

end WaveEquation
