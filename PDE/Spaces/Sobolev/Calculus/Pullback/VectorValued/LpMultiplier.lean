/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# Bounded scalar coefficients acting on Banach-valued Lp spaces

Mathlib's heterogeneous `Lp` multiplication gives a bounded linear operator for
each essentially bounded scalar coefficient. This primitive supplies the finite
rows in Sobolev product and change-of-coordinates formulas. It works at both
exponent endpoints and commutes with continuous linear maps of the target.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SobolevSpace.VectorValued

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [Fact (1 ≤ p)]

/-- Mathlib's heterogeneous `Lp` multiplication by a fixed bounded scalar coefficient,
bundled as a real continuous linear map. -/
def lpScalarMultiplierCLM (c : Lp ℝ ⊤ (domainMeasure n Ω)) :
    Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n Ω) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ c • u
      map_add' := Lp.add_smul c
      map_smul' := fun r u ↦ (Lp.smul_comm r c u).symm }
    ‖c‖ (Lp.norm_smul_le c)

/-- The bundled coefficient action is Mathlib's scalar multiplication on `Lp`. -/
@[simp] theorem lpScalarMultiplierCLM_apply (c : Lp ℝ ∞ (domainMeasure n Ω))
    (u : Lp F p (domainMeasure n Ω)) :
    lpScalarMultiplierCLM c u = c • u :=
  rfl

/-- Scalar coefficients multiply the representatives almost everywhere. -/
theorem lpScalarMultiplierCLM_apply_ae (c : Lp ℝ ∞ (domainMeasure n Ω))
    (u : Lp F p (domainMeasure n Ω)) :
    ⇑(lpScalarMultiplierCLM c u) =ᵐ[domainMeasure n Ω] fun x ↦ c x • u x :=
  Lp.coeFn_lpSMul c u

/-- The multiplier norm is at most the essential supremum of its coefficient. -/
theorem norm_lpScalarMultiplierCLM_le (c : Lp ℝ ∞ (domainMeasure n Ω)) :
    ‖lpScalarMultiplierCLM (F := F) (p := p) c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) (Lp.norm_smul_le c)

/-- A continuous linear codomain map commutes with scalar multiplication in `Lp`. -/
theorem compLpL_lpScalarMultiplierCLM (L : F →L[ℝ] G)
    (c : Lp ℝ ∞ (domainMeasure n Ω)) (u : Lp F p (domainMeasure n Ω)) :
    L.compLpL p (domainMeasure n Ω) (lpScalarMultiplierCLM c u) =
      lpScalarMultiplierCLM c (L.compLpL p (domainMeasure n Ω) u) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (lpScalarMultiplierCLM c u),
    lpScalarMultiplierCLM_apply_ae c u,
    lpScalarMultiplierCLM_apply_ae c (L.compLpL p (domainMeasure n Ω) u),
    L.coeFn_compLpL u] with x hout hmul hrhs hu
  rw [hout, hmul, map_smul, hrhs, hu]

end SobolevSpace.VectorValued
