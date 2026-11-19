/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.Finite
public import PDE.Numerics.Certificates.LinearSystem
public import CAS.Numerics.Polynomial
public import CAS.Numerics.SignedPolynomial
public import CAS.Numerics.Sums
public import CAS.Numerics.Tactic
public import CAS.Numerics.Json
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certificate engines for PDE quantities

The modules under `PDE.Numerics.Certificates` check finite certificates for quantities of PDE
arguments: planar kernel balls, axial and radial power cells, space-time and tensor-spline nodes,
and linear systems. This module collects the generic engines of SymLean (`CAS.Numerics`) with the
linear-system certificates. The declarations live in `CAS.Numerics` and its subnamespaces, the
SymLean namespace they extend, so dot notation on the SymLean types reaches them.
-/
