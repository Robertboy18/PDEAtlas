/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction

/-!
# Weak derivatives under linear maps and restriction

A linear change of codomain and restriction to a smaller open set both act
coordinatewise. They therefore commute with weak differentiation as equalities
of Sobolev functions, without choosing representatives.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

variable {n m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ω' : Opens ℝ^n}
  {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Applying a continuous linear map commutes with any weak derivative word. -/
theorem derivativeWordCLM_mapCLM (L : F →L[ℝ] G) (α : List (Fin n))
    (hα : α.length + r ≤ m) (u : W^{m,p}(Ω; F)) :
    derivativeWordCLM α hα (mapCLM L u) = mapCLM L (derivativeWordCLM α hα u) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

/-- A weak partial derivative commutes with a continuous linear codomain map. -/
theorem partialDeriv_mapCLM (L : F →L[ℝ] G) (i : Fin n) (u : W^{m + 1,p}(Ω; F)) :
    ∂[i] (mapCLM L u) = mapCLM L (∂[i] u) :=
  derivativeWordCLM_mapCLM L [i] _ u

/-- Restriction to a smaller open set commutes with any weak derivative word. -/
theorem derivativeWordCLM_restrictCLM (hΩ : Ω' ≤ Ω) (α : List (Fin n))
    (hα : α.length + r ≤ m) (u : W^{m,p}(Ω; F)) :
    derivativeWordCLM α hα (restrictCLM hΩ u) =
      restrictCLM hΩ (derivativeWordCLM α hα u) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

/-- Weak partial derivatives restrict to the same derivatives on a smaller domain. -/
theorem partialDeriv_restrictCLM (hΩ : Ω' ≤ Ω) (i : Fin n)
    (u : W^{m + 1,p}(Ω; F)) :
    ∂[i] (restrictCLM hΩ u) = restrictCLM hΩ (∂[i] u) :=
  derivativeWordCLM_restrictCLM hΩ [i] _ u

end SobolevSpace.VectorValued
