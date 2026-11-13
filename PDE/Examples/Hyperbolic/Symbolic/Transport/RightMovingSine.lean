/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Symbolic.Transport.Equation
public import CAS.ExactTactic

/-!
# A right-moving sine profile

The profile `u(t, x) = sin(x - t)` as a symbolic expression, with the first coordinate
`x` as time and the second `y` as space. It is the shared profile of the transport
integrand example `PDE.Examples.Hyperbolic.Symbolic.Transport.Integrand` and the wave
examples `PDE.Examples.Hyperbolic.Symbolic.Wave.TravelingSine` and
`PDE.Examples.Hyperbolic.Symbolic.Wave.WeakForm`.
-/

@[expose] public section

namespace TransportEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2
open scoped CAS

noncomputable section

/-- The closed-form traveling profile `u(t,x)=sin(x-t)`. -/
def rightMovingSineAnsatz : Verified.Expr (Fin 2) :=
  .sin (y - x : Verified.Expr (Fin 2))

end

end TransportEquation.Symbolic
