/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commuting derivatives of Schwartz maps

Schwartz maps are smooth, so their directional derivatives commute. The finite-word
version lets us move derivatives between a tempered distribution and its test function
without leaving an artificial reversal of directions in the resulting formula.
-/

@[expose] public noncomputable section

open LineDeriv
open scoped SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two bundled directional derivatives of a Schwartz map commute. -/
theorem lineDerivOp_comm (v w : E) (φ : 𝓢(E, F)) :
    ∂_{v} (∂_{w} φ) = ∂_{w} (∂_{v} φ) := by
  ext x
  change ∂^{![v, w]} φ x = ∂^{![w, v]} φ x
  rw [iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_eq_iteratedFDeriv]
  exact ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).iteratedFDeriv_cons

/-- A directional derivative commutes with any finite word of Schwartz derivatives. -/
theorem lineDerivOp_iteratedLineDerivOp (v : E) {k : ℕ} (m : Fin k → E)
    (φ : 𝓢(E, F)) :
    ∂_{v} (∂^{m} φ) = ∂^{m} (∂_{v} φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, lineDerivOp_comm, ih,
      iteratedLineDerivOp_succ_left]

end SchwartzMap
