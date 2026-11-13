/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import PDE.Notation.PartialDerivative

/-!
# Formal power-series notation

With `open scoped MvPowerSeries`, `[X^α] f` denotes the coefficient of the
multi-index `α` in `f`. It is Mathlib's `MvPowerSeries.coeff`, with no change
to the coefficient convention.

For series indexed by `Fin n`, the shared notation `∂[i] f` denotes Mathlib's
formal partial derivative. Formal differentiation requires no convergence
assumption; identifying it with a derivative of a represented function does.

Here `α : Fin n →₀ ℕ`, and `[X^0] f` is the constant coefficient. Mathlib's
`MvPowerSeries.coeff_pderiv` gives `[X^α] (∂[i] f) = (α i + 1) [X^(α + e_i)] f`, where `e_i`
is the multi-index `Finsupp.single i 1`. For the Taylor series of a real analytic function,
the coefficient of `X^α` is the derivative of order `α` at the center divided by `α!`; the
notation adds no normalization of its own. One-variable series use Mathlib's `R⟦X⟧` under
`open scoped PowerSeries`.
-/

@[expose] public section

/-- `[X^α] f` is the coefficient `MvPowerSeries.coeff α f` of the multi-index `α` in `f`. -/
scoped[MvPowerSeries] notation:max "[X^" α "] " f:max => MvPowerSeries.coeff α f

namespace MvPowerSeries

/-- Formal coordinate differentiation uses the same notation as classical and weak derivatives. -/
noncomputable instance instPartialDerivative {n : ℕ} {R : Type*} [CommRing R] :
    PDE.PartialDerivative n (MvPowerSeries (Fin n) R) (MvPowerSeries (Fin n) R) where
  partialDeriv i := pderiv i

end MvPowerSeries
