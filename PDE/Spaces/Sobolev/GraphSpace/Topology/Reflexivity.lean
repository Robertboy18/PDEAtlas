/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Reflexivity
public import PDE.Analysis.Normed.Reflexivity
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Reflexivity of Sobolev graph spaces

The ambient derivative coordinates form a finite `PiLp` product of real `Lp` spaces.
For `1 < p < ∞` these coordinates are reflexive. The weak-derivative graph is closed,
so the closed-subspace transfer gives reflexivity of the Sobolev graph space.

Restricted Lebesgue measure is σ-finite, even when the domain is unbounded. On open domains
this gives reflexivity of `W^{k,p}(Ω)` for every finite order, without a boundedness or
boundary regularity assumption. The supported-core closure is treated in
`Boundary.ZeroTrace.Reflexivity`.
-/

@[expose] public section

open Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The real Sobolev graph space is reflexive for every finite order and `1 < p < ∞`.
For open domains this is the usual `W^{k,p}(Ω)` reflexivity theorem, including unbounded
domains. -/
theorem WkpSpaceOn.surjective_inclusionInDoubleDual
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (W^{k,p}(Ω))) := by
  apply NormedSpace.surjective_inclusionInDoubleDual_submodule
    (wkpSubmoduleOn n k p Ω) (isClosed_WkpSubmoduleOn n k p Ω)
  exact NormedSpace.surjective_inclusionInDoubleDual_piLp p
    (fun _ : DerivIndex n k ↦ DerivLp n p Ω)
    (fun _ ↦ MeasureTheory.Lp.surjective_inclusionInDoubleDual hp hp_top)

end SobolevSpace.GraphSpace
