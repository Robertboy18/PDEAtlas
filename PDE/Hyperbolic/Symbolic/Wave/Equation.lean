/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ClosedForm.Scalar.Models

/-!
# The symbolic one-dimensional wave equation

The first coordinate is time and the second is space.
-/

@[expose] public section

namespace WaveEquation.Symbolic

open CAS
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- The one-dimensional symbolic wave equation `u_tt - u_xx = 0`.

Here `x` is used as time and `y` as the one spatial coordinate. -/
def travelingWave1DEquation : DiffExpr.Equation 2 Scalar.Unknown :=
  Scalar.wave1D x y 0
end

end WaveEquation.Symbolic
