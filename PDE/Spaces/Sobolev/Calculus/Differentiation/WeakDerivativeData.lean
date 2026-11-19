/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Sobolev representatives of weak derivatives

A Sobolev representative together with the weak derivative identity that it
satisfies. The derivative word is arbitrary, so the same structure covers
coordinate, mixed, and higher weak derivatives.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev

variable {n : ℕ}

/--
A `W^{r,p}` representative of the weak derivative of `source` along the
coordinate word `alpha`.
-/
structure WeakDerivativeData
    (r : ℕ)
    (p : ℝ≥0∞)
    (Ω : Set (ℝ^n))
    (alpha : List (Fin n))
    (source : ℝ^n → ℝ) where
  /-- The Sobolev representative of the weak derivative. -/
  derivative : W^{r,p}(Ω)
  /-- The representative satisfies the specified weak derivative identity. -/
  derivative_spec :
    HasWeakDerivativeOn (n := n) Ω alpha source
      ((((derivative : WkpAmbientOn n r p Ω)
        (baseIndex n r) : DerivLp n p Ω) : ℝ^n → ℝ))

end SobolevSpace.GraphSpace
