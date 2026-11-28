/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Symbolic.ClosedForm.Scalar.Core

/-!
# The symbolic unit transport equation

This module encodes `u_t + u_x = 0` as a symbolic scalar equation, with time as the
first coordinate and space as the second.
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
