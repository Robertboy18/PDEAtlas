/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.CompactEmbedding
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction

/-!
# Compact L1 values of Sobolev functions

On a finite measure domain, lowering the Sobolev exponent from `p ≥ 1` to one
and taking the base coordinate gives the original function in `L¹`. On a
bounded C¹ extension domain this map is compact in every positive dimension:
it factors through the compact base coordinate of `W¹¹`. The almost-everywhere
identity below lets integral functionals keep their original representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.RellichKondrachov

variable {n : ℕ} {Ω : Set (ℝ^n)}
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- The value of a Sobolev function as an `L¹` class, obtained by lowering all
graph coordinates to exponent one before taking the base coordinate. -/
def valueL1CLM [IsFiniteMeasure (domainMeasure n Ω)] :
    W^{1,p}(Ω) →L[ℝ] Lp ℝ 1 (domainMeasure n Ω) :=
  (wkpBaseCoordinateCLM (p := 1)).comp (lowerExponentOfFiniteMeasureCLM hp.out)

/-- Lowering the exponent preserves the original base representative almost
everywhere; it changes only the normed space in which that class is viewed. -/
theorem valueL1CLM_apply_ae [IsFiniteMeasure (domainMeasure n Ω)]
    (u : W^{1,p}(Ω)) :
    (valueL1CLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  exact lowerExponentOfFiniteMeasure_apply_ae hp.out u (baseIndex n 1)

/-- The value map `W¹ᵖ → L¹` is compact for every `p ≥ 1` and every positive
dimension on a bounded C¹ extension domain, including dimension one. -/
theorem valueL1CLM_isCompactOperator_of_c1Domain
    [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω] :
    IsCompactOperator (valueL1CLM (n := n) (Ω := Ω) (p := p)) :=
  baseCoordinateL1_isCompactOperator_of_c1Domain.comp_clm
    (lowerExponentOfFiniteMeasureCLM hp.out)

end SobolevSpace.GraphSpace.RellichKondrachov
