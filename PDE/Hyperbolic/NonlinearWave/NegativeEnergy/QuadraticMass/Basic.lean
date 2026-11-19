/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.PartialDeriv

/-!
# Quadratic mass and momentum for semilinear waves

We define the normalized spatial quadratic mass

`I(t) = (1 / 2) ∫ u(t, x)² dx`,

its momentum `P(t) = ∫ u(t, x) uₜ(t, x) dx`, and the formal time derivative
of the momentum density.

The mass `I` is the function `I(t)` of step 1 of the proof of Evans, §12.5.1, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, step 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace WaveEquation

variable {n : ℕ}

/-- The normalized spatial quadratic mass
`I(t) = (1 / 2) ∫ u(t, x)² dx` of a spacetime field. -/
def waveSpatialQuadraticMass
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x : ℝ^n,
    (1 / 2 : ℝ) *
      u (PDE.Common.timeSpaceCons (n := n) t x) ^ 2

/-- The fixed-time density `u(t, x) uₜ(t, x)` of the quadratic momentum. -/
def waveSpatialQuadraticMomentumDensity
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  u (PDE.Common.timeSpaceCons (n := n) t x) *
    (∂[0] u)
      (PDE.Common.timeSpaceCons (n := n) t x)

/-- The momentum associated with the spatial quadratic mass,
`∫ u(t, x) uₜ(t, x) dx`. -/
def waveSpatialQuadraticMomentum
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x : ℝ^n,
    waveSpatialQuadraticMomentumDensity (n := n) u t x

/-- The formal time derivative
`uₜ(t, x)² + u(t, x) uₜₜ(t, x)` of the quadratic-momentum density. -/
def waveSpatialQuadraticMomentumDerivativeDensity
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  ((∂[0] u)
      (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
    u (PDE.Common.timeSpaceCons (n := n) t x) *
      (∂[0]
        (fun p ↦
          (∂[0] u) p))
        (PDE.Common.timeSpaceCons (n := n) t x)

end WaveEquation
