/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Time differentiation in the Sobolev graph space

Differentiating the finitely many `Lᵖ` coordinates gives differentiation in
the Sobolev graph norm. Closedness of the weak-derivative graph
also proves that an ambient coordinate derivative satisfies the spatial
weak-derivative identities: it is a limit of graph-valued difference quotients.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Coordinatewise `Lᵖ` differentiation gives differentiation in the finite
Sobolev ambient product, with its `PiLp` norm. -/
theorem hasDerivAt_ambient_of_coordinates
    {u : ℝ → WkpAmbientOn n k p Ω} {v : WkpAmbientOn n k p Ω} {t : ℝ}
    (h : ∀ a, HasDerivAt (fun s ↦ u s a) (v a) t) :
    HasDerivAt u v t := by
  let e := PiLp.continuousLinearEquiv p ℝ (fun _ : DerivIndex n k ↦ DerivLp n p Ω)
  exact e.symm.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)

/-- Time differentiation in the Sobolev graph norm is equivalent to
differentiation of each of its `Lᵖ` coordinates. -/
theorem WkpSpaceOn.hasDerivAt_iff_coordinates
    {u : ℝ → W^{k,p}(Ω)} {v : W^{k,p}(Ω)} {t : ℝ} :
    HasDerivAt u v t ↔ ∀ a,
      HasDerivAt (fun s ↦ (u s).val a) (v.val a) t := by
  constructor
  · intro h a
    exact (wkpCoordinateCLM a).hasFDerivAt.comp_hasDerivAt t h
  · intro h
    have hamb := hasDerivAt_ambient_of_coordinates h
    rw [hasDerivAt_iff_tendsto] at hamb ⊢
    exact hamb

/-- An ambient time derivative of a Sobolev trajectory automatically
satisfies the spatial weak-derivative constraints. -/
theorem isWkpOn_of_hasDerivAt_coordinates
    {u : ℝ → W^{k,p}(Ω)} {v : WkpAmbientOn n k p Ω} {t : ℝ}
    (h : ∀ a, HasDerivAt (fun s ↦ (u s).val a) (v a) t) :
    IsWkpOn v := by
  have hd := hasDerivAt_ambient_of_coordinates h
  apply (isClosed_WkpSubmoduleOn n k p Ω).mem_of_tendsto hd.tendsto_slope
  exact Filter.Eventually.of_forall fun s ↦
    (wkpSubmoduleOn n k p Ω).smul_mem _ ((u s - u t).property)

/-- Coordinate derivatives produce a derivative in the
Sobolev space; no weak-derivative identity for the velocity is assumed. -/
theorem WkpSpaceOn.exists_hasDerivAt_of_coordinates
    {u : ℝ → W^{k,p}(Ω)} {v : WkpAmbientOn n k p Ω} {t : ℝ}
    (h : ∀ a, HasDerivAt (fun s ↦ (u s).val a) (v a) t) :
    ∃ V : W^{k,p}(Ω), V.val = v ∧ HasDerivAt u V t := by
  exact ⟨⟨v, isWkpOn_of_hasDerivAt_coordinates h⟩, rfl,
    WkpSpaceOn.hasDerivAt_iff_coordinates.mpr h⟩

end SobolevSpace.GraphSpace
