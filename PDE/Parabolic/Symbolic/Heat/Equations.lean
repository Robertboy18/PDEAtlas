/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.ClosedForm.Scalar.Models

/-!
# Symbolic heat equations

The one- and two-space-dimensional symbolic heat equations used by the
closed-form examples. In both expressions, coordinate `0` is time and the remaining coordinates
are spatial.
-/

@[expose] public section

namespace HeatEquation.Symbolic

open CAS
open scoped CAS

namespace Space1

open CAS.Euclid2

/-- The one-space-dimensional heat equation `u_t - u_xx = 0`. -/
def heat1DEquation : DiffExpr.Equation 2 Scalar.Unknown :=
  Scalar.heat1D x y 0

end Space1

namespace Space2

open CAS.Euclid3

/-- The two-space-dimensional heat equation `u_t - (u_xx + u_yy) = 0`. -/
def heat2DEquation : DiffExpr.Equation 3 Scalar.Unknown :=
  Scalar.heatSpatial x [y, z] 0

end Space2

end HeatEquation.Symbolic
