/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Reflexivity

/-!
# Reflexivity of supported-core Sobolev spaces

The closure of the supported smooth core is a closed subspace of the Sobolev graph space.
For `1 < p < ∞`, reflexivity of that graph space therefore gives reflexivity of its
supported-core closure, including on unbounded domains.

On open domains this is `W^{k,p}_0(Ω)`. Its definition is the closure of compactly supported
smooth functions. Boundedness and boundary
regularity are not required, and the order may be any natural number.
-/

@[expose] public section

open Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The supported-core Sobolev space is reflexive for every finite order and `1 < p < ∞`.
For open domains this is `W^{k,p}_0(Ω)`, defined as the closure of compactly supported
smooth functions. No boundedness or boundary regularity assumption is needed. -/
theorem Wkp0SpaceOn.surjective_inclusionInDoubleDual
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (W₀^{k,p}(Ω))) := by
  exact NormedSpace.surjective_inclusionInDoubleDual_submodule
    (wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω)).toSubmodule
    (wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω)).isClosed'
    (WkpSpaceOn.surjective_inclusionInDoubleDual hp hp_top)

end SobolevSpace.GraphSpace
