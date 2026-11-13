/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Coordinates and support for a C1 boundary piece

We expose the base coordinate of a first-order Sobolev graph-space
field and prove that the flattened base and derivative coordinates remain
supported in the compact chart target.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- First-derivative coordinate of a Sobolev graph-space `W^{1,p}` field. -/
def derivativeCoordinate {S : Set (ℝ^n)}
    (U : W^{1,p}(S)) (k : Fin n) : ℝ^n → ℝ :=
  ((U : SobolevSpace.GraphSpace.WkpAmbientOn n 1 p S)
    (SobolevSpace.GraphSpace.singleDerivIndex n k) : ℝ^n → ℝ)

/-- The base coordinate of a localized flattened Sobolev field vanishes almost
everywhere off `boundarySupportInTarget`. This is the public support
fact used when a chart-local weak identity is extended to the whole upper half
space. -/
theorem flattenCLM_base_boundarySupportInTarget_indicator_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω)) :
    (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
        (GraphSpace.baseRepresentative (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U)) =ᵐ[
      domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        GraphSpace.baseRepresentative (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U) := by
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  let flat := GraphSpace.baseRepresentative (n := n) (p := p)
    (flattenCLM (n := n) (p := p) (Ω := Ω) i U)
  have hactual : flat =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
      preparedFlattenBaseRepresentative (n := n) (p := p) (Ω := Ω) i U := by
    simpa [flat, GraphSpace.baseRepresentative, flattenCLM_apply_coe] using
      preparedFlattenAmbient_base_apply_ae
        (n := n) (p := p) (Ω := Ω) i U
  filter_upwards [hactual] with y hy
  by_cases hyKT : y ∈ KT
  · exact Set.indicator_of_mem hyKT _
  · rw [Set.indicator_of_notMem hyKT]
    change 0 = flat y
    rw [hy]
    symm
    by_contra hne
    exact hyKT
      (support_preparedFlattenBaseRepresentative_subset
        (n := n) (p := p) (Ω := Ω) i U hne)

/-- Every first-derivative coordinate of a localized flattened Sobolev field
vanishes almost everywhere off `boundarySupportInTarget`. -/
theorem flattenCLM_deriv_boundarySupportInTarget_indicator_ae
    (i : Fin hΩ.N)
    (U : W^{1,p}(Ω))
    (k : Fin n) :
    (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
        (derivativeCoordinate (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U) k) =ᵐ[
      domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        derivativeCoordinate (n := n) (p := p)
          (flattenCLM (n := n) (p := p) (Ω := Ω) i U) k := by
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  let deriv := derivativeCoordinate (n := n) (p := p)
    (flattenCLM (n := n) (p := p) (Ω := Ω) i U) k
  have hactual : deriv =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
      preparedFlattenDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i U k := by
    simpa [deriv, derivativeCoordinate, flattenCLM_apply_coe] using
      preparedFlattenAmbient_derivative_apply_ae
        (n := n) (p := p) (Ω := Ω) i U k
  filter_upwards [hactual] with y hy
  by_cases hyKT : y ∈ KT
  · exact Set.indicator_of_mem hyKT _
  · rw [Set.indicator_of_notMem hyKT]
    change 0 = deriv y
    rw [hy]
    symm
    by_contra hne
    exact hyKT
      (support_preparedFlattenDerivativeRepresentative_subset
        (n := n) (p := p) (Ω := Ω) i U k hne)

end BoundaryPiece

end C1

end Extension

end SobolevSpace
