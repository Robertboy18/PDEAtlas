/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity

/-!
# Defocusing odd-power wave equation

The odd-power scalar potential in the semilinear wave operator. The scalar
polynomial, potential, and their calculus and order properties are in
`PDE.Analysis.Scalar.OddPower`.
-/

@[expose] public section

noncomputable section

open PDE.Analysis.Scalar

namespace WaveEquation

variable {n : ℕ}

/-- The semilinear operator for the canonical odd-power potential is the
defocusing power wave operator. -/
theorem semilinearWaveOperator_oddPowerPotential (massSq coupling : ℝ) (k : ℕ) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) :
    semilinearWaveOperator (n := n) (oddPowerPotential massSq coupling k) u p =
      waveOperator (n := n) u p + massSq * u p + coupling * (u p) ^ (2 * k + 1) := by
  simp only [semilinearWaveOperator, deriv_oddPowerPotential, oddPowerPolynomial, add_assoc]

end WaveEquation
