/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.Polyconvexity.Densities
public import PDE.Examples.CalculusOfVariations.Polyconvexity.GraphBound

/-!
# Lower semicontinuity of signed polyconvex energies

The weighted determinant square has quartic gradient growth, and the exponent is
`q = 3`. The second density is bounded below only on the determinant graph. The
conclusions concern the signed energy in `EReal`, including the value `+∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CalculusOfVariations
open scoped ENNReal Topology Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Polyconvexity

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (5 / 2 : ℝ)) := ⟨by norm_num⟩

/-- The weighted determinant energy, of quartic growth in the gradient, is weakly lower
semicontinuous on `W^{1,3}`. -/
theorem weighted_energy_three
    {Ω : Set (ℝ^2)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {u : ℕ → Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)}
    {U : Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)) U))) :
    vectorWkpIntegral (determinantDensity weightedDeterminantDensity) U ≤
      liminf (fun k ↦ vectorWkpIntegral (determinantDensity weightedDeterminantDensity)
        (u k)) atTop :=
  vectorWkpIntegral_le_liminf_of_contDiffOn_convex_determinant hopen hbounded hgraph
    (by norm_num) weightedDeterminantDensity_contDiff.contDiffOn
    (fun x _ s ↦ weightedDeterminantDensity_convex x s)
    (fun x _ s P ↦ weightedDeterminantDensity_lower x s P) hu

/-- The lower semicontinuity theorem holds for the graph-bounded density, which has no
global lower bound. -/
theorem graph_bound_energy
    {Ω : Set (ℝ^2)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {u : ℕ → Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)}
    {U : Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)) U))) :
    vectorWkpIntegral (determinantDensity graphBoundDensity) U ≤
      liminf (fun k ↦ vectorWkpIntegral (determinantDensity graphBoundDensity) (u k))
        atTop :=
  vectorWkpIntegral_le_liminf_of_contDiffOn_convex_determinant hopen hbounded hgraph
    (by norm_num) graphBoundDensity_contDiff.contDiffOn
    (fun x _ s ↦ graphBoundDensity_convex x s)
    (fun x _ s P ↦ graphBoundDensity_lower x s P) hu

/-- The signed energy of the graph-bound density `F` is `∫⁻ (F + 7) - 7 |Ω|`. -/
theorem graph_bound_signed_shift
    {Ω : Set (ℝ^2)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (u : Fin 2 → W^{1,ENNReal.ofReal (3 : ℝ)}(Ω)) :
    vectorWkpIntegral (determinantDensity graphBoundDensity) u =
      (vectorWkpLIntegral (determinantDensity graphBoundDensity) (fun _ ↦ 7) u : EReal) -
        ((7 * (domainMeasure 2 Ω).real univ : ℝ) : EReal) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact vectorWkpIntegral_determinantDensity_eq_lIntegral_sub hopen.measurableSet
    graphBoundDensity_contDiff.continuous.continuousOn
    (fun x _ s P ↦ graphBoundDensity_lower x s P) u

end PDE.Examples.Polyconvexity
