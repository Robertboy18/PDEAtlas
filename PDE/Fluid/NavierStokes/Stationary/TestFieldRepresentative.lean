/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Representative
public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity

/-!
# Representatives of the `H¹` field of a test field

The `H¹` velocity `testFieldH1 φ` of a smooth compactly supported field `φ` has `φ` as its
representative and the classical partial derivatives of `φ` as its gradient representative,
almost everywhere.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ContDiff

namespace NavierStokes.Stationary

set_option linter.missingDocs true

variable {n : ℕ} {φ : ℝ^n → ℝ^n}

/-- The representative of the `H¹` field of a test field is the field almost everywhere. -/
theorem representative_testFieldH1_ae (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    representative (testFieldH1 φ hφ hφc) =ᵐ[volume] φ := by
  filter_upwards [ae_all_iff.mpr fun i ↦ testFieldH1_base_ae hφ hφc i] with x hx
  ext i
  rw [representative_apply, massCLM_apply]
  exact hx i

/-- The gradient representative of the `H¹` field of a test field is the classical gradient
almost everywhere. -/
theorem gradientRepresentative_testFieldH1_ae (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (i j : Fin n) :
    (fun x ↦ gradientRepresentative (testFieldH1 φ hφ hφc) x i j) =ᵐ[volume]
      PDE.partialDeriv j (fun x ↦ φ x i) := by
  filter_upwards [testFieldH1_partial_ae hφ hφc i j] with x hx
  rw [gradientRepresentative, gradientCLM_apply]
  exact hx

end NavierStokes.Stationary
