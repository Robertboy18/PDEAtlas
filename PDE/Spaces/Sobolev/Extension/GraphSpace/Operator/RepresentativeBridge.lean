/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic
public import PDE.Spaces.Sobolev.Extension.Representative.Basic
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# From graph-space extensions to representative extensions

We transport a bounded graph-space extension through the equivalence between graph-space
weak derivatives and representative-based Sobolev functions.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace Extension

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Ω : Set (ℝ^n)}

namespace GraphSpace

open SobolevSpace.GraphSpace

/-- A graph-space extension induces an extension on representative-based Sobolev functions. -/
theorem exists_representativeExtensionOperator
    (h : HasExtensionOperator (n := n) (k := k) (p := p) Ω) :
    SobolevSpace.Extension.Representative.HasExtension n k p Ω := by
  classical
  rcases h with ⟨E⟩
  refine ⟨
    fun u ↦
      toRepresentative (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
        (E.toContinuousLinearMap
          (ofRepresentative (n := n) (k := k) (p := p) (Ω := Ω) u)),
    ?_⟩
  intro u
  have hE :=
    E.agree_ae (ofRepresentative (n := n) (k := k) (p := p) (Ω := Ω) u)
  have hpack :=
    ofRepresentative_base_ae (n := n) (k := k) (p := p) (Ω := Ω) u
  filter_upwards [hE, hpack] with x hxE hxP
  simpa [toRepresentative] using hxE.trans hxP

end GraphSpace

end Extension

end SobolevSpace

end
