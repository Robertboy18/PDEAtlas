/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import PDE.Analysis.Calculus.CompactParametricIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Parameter integrals beyond finite-dimensional spaces

The parameter `x` ranges over a real normed space `X` in a higher universe than `ℝ`.
`Analysis.contDiff_intervalIntegral` shows that `x ↦ ∫ t in a..b, L x * t` is smooth, and
`Analysis.contDiffOn_intervalIntegral` that `x ↦ ∫ t in 1..2, L x * √t` is smooth on an
open set, although `√t` is not smooth at `t = 0`, outside the interval of integration.
-/

open MeasureTheory Set
open scoped ContDiff

namespace PDE.Examples

universe u

-- Regression: the theorems once needed a finite-dimensional `X` and values in a universe at least
-- `X`'s, which ruled out real-valued integrands over `X : Type (u + 1)`.
variable {X : Type (u + 1)} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The integral of a smooth integrand depends smoothly on the parameter. -/
example (L : X →L[ℝ] ℝ) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in a..b, L x * t) :=
  Analysis.contDiff_intervalIntegral
    ((L.contDiff.comp contDiff_fst).mul contDiff_snd) a b

/-- Smoothness of the integrand on the strip `U × [1, 2]` suffices. -/
example (L : X →L[ℝ] ℝ) {U : Set X} (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ t in (1 : ℝ)..2, L x * Real.sqrt t) U := by
  apply Analysis.contDiffOn_intervalIntegral
    (n := ⊤) (H := fun p ↦ L p.1 * Real.sqrt p.2) hU
  apply (L.contDiff.comp contDiff_fst).contDiffOn.mul
  apply contDiffOn_snd.sqrt
  intro p hp
  have hp' : p.2 ∈ Icc (1 : ℝ) 2 := by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hp.2
  linarith [hp'.1]

end PDE.Examples
