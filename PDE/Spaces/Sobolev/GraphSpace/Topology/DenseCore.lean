/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Sobolev recovery from a dense algebraic core

Suppose a dense core carries scalar `H¹` jets, and their gradient rows extend
continuously to an ambient seminormed space. A bound for the scalar `L²` row in the ambient
norm then recovers the entire `H¹` jet continuously. The scalar bound is preserved.

`exists_h1_extension_of_scalar_bound` uses Mathlib's `LinearMap.extendOfNorm` for the
scalar row. Closedness of the weak-derivative graph identifies the prescribed gradient
rows as weak derivatives of this extension. The core may be a space of test functions
with no chosen norm, and the ambient space need not be complete.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open scoped Distributions ENNReal Sobolev

variable {R H : Type*} [AddCommGroup R] [Module ℝ R]
  [SeminormedAddCommGroup H] [NormedSpace ℝ H]
  {n : ℕ} {Ω : Set (ℝ^n)}

/-- A scalar `L²` bound on a dense algebraic core and continuous gradient rows agreeing
with its `H¹` jet give a continuous `H¹` recovery map on the ambient space.
The map recovers the full core jet, has the prescribed weak gradients, and preserves the
scalar bound. The core needs no topology or norm, and its realization need not be injective.
Weak derivatives on the ambient space follow from closedness of the Sobolev graph. -/
theorem exists_h1_extension_of_scalar_bound
    (e : R →ₗ[ℝ] H) (he : DenseRange e)
    (jet : R →ₗ[ℝ] W^{1,2}(Ω))
    (gradient : Fin n → H →L[ℝ] DerivLp n 2 Ω)
    (hgradient : ∀ r i, (jet r).val (singleDerivIndex n i) = gradient i (e r))
    (C : ℝ)
    (hscalar : ∀ r, ‖(jet r).val (baseIndex n 1)‖ ≤ C * ‖e r‖) :
    ∃ recover : H →L[ℝ] W^{1,2}(Ω),
      (∀ r, recover (e r) = jet r) ∧
      (∀ u i, (recover u).val (singleDerivIndex n i) = gradient i u) ∧
      (∀ u, ‖(recover u).val (baseIndex n 1)‖ ≤ C * ‖u‖) := by
  let base : W^{1,2}(Ω) →L[ℝ] DerivLp n 2 Ω := wkpBaseCoordinateCLM
  let scalar : R →ₗ[ℝ] DerivLp n 2 Ω := base.toLinearMap.comp jet
  let extendedScalar : H →L[ℝ] DerivLp n 2 Ω := scalar.extendOfNorm e
  have hscalar_eq (r : R) : extendedScalar (e r) = (jet r).val (baseIndex n 1) :=
    LinearMap.extendOfNorm_eq he ⟨C, hscalar⟩ r
  let ambient : H →L[ℝ] WkpAmbientOn n 1 2 Ω :=
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (firstOrderRows extendedScalar gradient))
  have hambient_base (u : H) :
      ambient u (baseIndex n 1) = extendedScalar u := by
    change firstOrderRows extendedScalar gradient (baseIndex n 1) u = _
    rw [firstOrderRows_baseIndex]
  have hambient_gradient (u : H) (i : Fin n) :
      ambient u (singleDerivIndex n i) = gradient i u := by
    change firstOrderRows extendedScalar gradient (singleDerivIndex n i) u = _
    rw [firstOrderRows_singleDerivIndex]
  have hambient_core (r : R) : ambient (e r) = (jet r).val := by
    apply PiLp.ext
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · exact (hambient_base _).trans (hscalar_eq r)
    · exact (hambient_gradient _ i).trans (hgradient r i).symm
  have hgraph (u : H) : ambient u ∈ wkpSubmoduleOn n 1 2 Ω := by
    refine he.induction_on u
      ((isClosed_WkpSubmoduleOn n 1 2 Ω).preimage ambient.continuous) ?_
    intro r
    rw [hambient_core]
    exact (jet r).property
  let recover : H →L[ℝ] W^{1,2}(Ω) :=
    ambient.codRestrict (wkpSubmoduleOn n 1 2 Ω) hgraph
  refine ⟨recover, ?_, ?_, ?_⟩
  · intro r
    exact Subtype.ext (hambient_core r)
  · intro u i
    exact hambient_gradient u i
  · intro u
    change ‖ambient u (baseIndex n 1)‖ ≤ _
    rw [hambient_base]
    exact LinearMap.norm_extendOfNorm_apply_le he C hscalar u

end SobolevSpace.GraphSpace
