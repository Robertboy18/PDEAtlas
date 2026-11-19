/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic

/-!
# The whole-space Sobolev graph-space extension

On `ℝ^n`, the graph-space extension operator is the identity. We
record its exact application norm and the resulting operator-norm bound.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace Extension
namespace GraphSpace

open SobolevSpace.GraphSpace

namespace Trivial

variable (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The identity continuous linear map is an extension operator for `Ω = univ`. -/
noncomputable def operatorUniv :
    Operator n k p (Set.univ : Set (ℝ^n)) where
  toContinuousLinearMap := ContinuousLinearMap.id ℝ (W^{k,p}(ℝ^n))
  agree_ae := by
    intro u
    simp

/-- The identity map supplies a graph-space extension operator on the whole space. -/
theorem exists_extensionOperator_univ :
    HasExtensionOperator n k p (Set.univ : Set (ℝ^n)) :=
  ⟨operatorUniv (n := n) (k := k) (p := p)⟩

/-- The Sobolev graph-space trivial extension preserves the project's `PiLp`
`W^{k,p}` norm exactly.

This is stronger than the bounded-extension interface: because the source and target are both
`W^{k,p}(ℝ^n)`, the underlying continuous linear map is the identity, so the sharp pointwise
bound has constant `1`. At `p = ∞`, this exact identity uses the
maximum-over-coordinates norm. -/
theorem norm_operator_univ_apply
    (u : W^{k,p}((Set.univ : Set (ℝ^n)))) :
    ‖(operatorUniv (n := n) (k := k) (p := p)).toContinuousLinearMap u‖ = ‖u‖ := by
  simp [operatorUniv]

/-- The continuous linear map underlying the trivial extension has operator norm at most `1`.

The inequality formulation remains valid even in a degenerate zero-dimensional Sobolev space,
where the operator norm need not be shown to equal `1`. -/
theorem norm_operator_univ_le_one :
    ‖(operatorUniv (n := n) (k := k) (p := p)).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simpa using
    (norm_operator_univ_apply (n := n) (k := k) (p := p) u).le

end Trivial

end GraphSpace

end Extension

end SobolevSpace

end
