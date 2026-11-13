/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

import CAS.CEGA
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# The downward second coefficient of the fast-weight curvature

The curvature expression of `Curvature` combines first and second coefficients of
the downward and upward speed variations. We bound the downward second coefficient
`(4 - y w) / d² + 2 v (J y - d) / d³` on the gate's scalar ranges with one certificate of the
`cega` tactic of SymLean, our computer algebra system for Lean, over a five-dimensional box.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- On the gate's scalar ranges, the second coefficient of the downward speed
variation is at most `6`. -/
theorem linear_fast_down_second_le {y J d v w : ℝ} (hy : y ∈ Set.Icc (205 : ℝ) (2051 / 10))
    (hJ : J ∈ Set.Icc (15799 / 4000 : ℝ) 4) (hd : d ∈ Set.Icc (13 / 5 : ℝ) 3)
    (hv : v ∈ Set.Icc (0 : ℝ) (201 / 4000)) (hw : w ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    (4 - y * w) / d ^ 2 + 2 * v * (J * y - d) / d ^ 3 ≤ (6 : ℝ) := by
  cega

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
