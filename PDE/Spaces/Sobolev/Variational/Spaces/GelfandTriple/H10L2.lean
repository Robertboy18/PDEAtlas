/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# The `H¹₀`-`L²` Gelfand triple

The dense embedding

`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`

used by both parabolic and hyperbolic variational problems, as an instance of the
abstract Gelfand triple of the parent module. On a bounded open set the inclusion
`H¹₀(Ω) → L²(Ω)` is compact.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Evolution
open scoped Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical Gelfand triple induced by the base-coordinate inclusion
`H¹₀(Ω) → L²(Ω)` on an open set. -/
noncomputable def h10L2GelfandTriple (hΩopen : IsOpen Ω) :
    GelfandTriple
      (V := H¹₀(Ω))
      (H := DerivLp n 2 Ω) where
  inclusion :=
    baseCoordCLM (n := n) (Ω := Ω)
  injective :=
    baseCoordCLM_injective (n := n) (Ω := Ω) hΩopen
  denseRange :=
    baseCoordCLM_denseRange
      (n := n) (Ω := Ω) hΩopen

/-- The inclusion of the Sobolev Gelfand triple is the base-coordinate map
from `H¹₀(Ω)` to `L²(Ω)`. -/
@[simp]
theorem h10L2GelfandTriple_inclusion_apply
    (hΩopen : IsOpen Ω)
    (v : H¹₀(Ω)) :
    (h10L2GelfandTriple hΩopen).inclusion v =
      baseCoordCLM (n := n) (Ω := Ω) v :=
  rfl

/-- On a bounded open set, the energy-to-pivot inclusion is compact. -/
theorem h10L2GelfandTriple_inclusion_isCompactOperator
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (h10L2GelfandTriple hΩopen).inclusion := by
  exact baseCoordCLM.isCompactOperator_of_bounded
    hΩopen.measurableSet hΩbounded

end SobolevSpace.GraphSpace
