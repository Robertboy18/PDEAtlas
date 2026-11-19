/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.ClosedForm.Scalar.Core

/-!
# The symbolic unit transport equation

The first coordinate is time and the second is space. The equation
`u_t + u_x = 0` is shared by the closed-form profiles in this directory.
-/

@[expose] public section

namespace TransportEquation.Symbolic

open CAS
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- Unit transport equation in spacetime coordinates: `u_t + u_x = 0`. -/
def unitTransport1DEquation : DiffExpr.Equation 2 Scalar.Unknown where
  lhs := DiffExpr.D x Scalar.u + DiffExpr.D y Scalar.u
  rhs := 0
end

end TransportEquation.Symbolic
