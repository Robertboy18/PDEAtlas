/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Laplacian
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives.Naturality

/-!
# The weak Laplacian under linear maps and restriction

The Laplacian commutes with linear changes of codomain and with restriction
to smaller open sets. Both facts follow from the corresponding partial
derivative identities, so the operator used in a local PDE is the restriction
of the one on the original domain.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped ENNReal Sobolev Laplacian

namespace SobolevSpace.VectorValued

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens ℝ^n}
  {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A continuous linear codomain map commutes with the weak Laplacian. -/
theorem laplacian_mapCLM (L : F →L[ℝ] G) (u : W^{k + 2,p}(Ω; F)) :
    Δ (mapCLM L u) = mapCLM L (Δ u) := by
  simp only [laplacian_eq_sum, partialDeriv_mapCLM, map_sum]

/-- Restricting a weak Laplacian gives the weak Laplacian on the smaller domain. -/
theorem laplacian_restrictCLM (hΩ : Ω' ≤ Ω) (u : W^{k + 2,p}(Ω; F)) :
    Δ (restrictCLM hΩ u) = restrictCLM hΩ (Δ u) := by
  simp only [laplacian_eq_sum, partialDeriv_restrictCLM, map_sum]

end SobolevSpace.VectorValued
