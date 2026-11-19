/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The derivative equivalence in normed-space coordinates

Mathlib's derivative equivalence of a diffeomorphism acts between tangent
spaces. Composing with the canonical tangent-space identifications gives a
continuous linear equivalence between the original normed spaces, with
forward map equal to the Fréchet derivative.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative equivalence, expressed in the original normed spaces. -/
def fderivEquiv (Φ : E ≃ₘ[ℝ] F) (x : E) : E ≃L[ℝ] F :=
  ((NormedSpace.fromTangentSpace x).symm.trans
    (Φ.mfderivToContinuousLinearEquiv (by simp) x)).trans
      (NormedSpace.fromTangentSpace (Φ x))

/-- The forward map of the derivative equivalence is the actual Fréchet derivative. -/
theorem coe_fderivEquiv (Φ : E ≃ₘ[ℝ] F) (x : E) :
    (Φ.fderivEquiv x).toContinuousLinearMap = fderiv ℝ Φ x := by
  have h := (Φ.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)).trans
    mfderiv_eq_fderiv
  convert! h

end Diffeomorph
