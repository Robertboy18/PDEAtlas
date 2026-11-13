/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives through continuous linear maps

A continuous linear map commutes with ordinary iterated differentiation.
This is the one-dimensional form of Mathlib's Fréchet derivative theorem:
evaluate the multilinear derivative on the tuple whose entries are all one.
It applies, for example, when embedding a real-valued function into a complex
space or projecting a vector-valued derivative onto one coordinate.
-/

@[expose] public noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Ordinary iterated differentiation commutes with a continuous linear map. -/
theorem iteratedDeriv_comp_left (L : E →L[𝕜] F) {n : ℕ} {f : 𝕜 → E} {x : 𝕜}
    (hf : ContDiffAt 𝕜 n f x) :
    iteratedDeriv n (L ∘ f) x = L (iteratedDeriv n f x) := by
  exact congrArg (fun A ↦ A (fun _ : Fin n ↦ (1 : 𝕜)))
    (L.iteratedFDeriv_comp_left hf le_rfl)

end ContinuousLinearMap
