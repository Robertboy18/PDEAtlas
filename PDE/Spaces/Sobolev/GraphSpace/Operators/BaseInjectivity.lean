/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Injectivity of the Sobolev base coordinate

On an open domain, the base function determines every weak derivative.
The base-coordinate map is therefore injective. Both elliptic solution lifts
and measurable Sobolev curves use this consequence of weak-derivative uniqueness.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal

/-- On an open domain, the base-coordinate map on W^{r,p} is injective. -/
theorem wkpBaseCoordinateCLM_injective
    {n : ℕ} {Ω : Set ℝ^n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hOmegaOpen : IsOpen Ω) {r : ℕ} :
    Function.Injective
      (wkpBaseCoordinateCLM (n := n) (m := r) (p := p) (Ω := Ω)) := by
  intro U V hbase
  apply WkpSpaceOn.ext_of_base_ae hOmegaOpen
  rw [← wkpBaseCoordinateCLM_apply, ← wkpBaseCoordinateCLM_apply, hbase]

end SobolevSpace.GraphSpace
