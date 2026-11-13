/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteEndpointFlattening
import CAS.ExactTactic

/-!
# Flattening a nonzero endpoint slope

The one-panel Hermite profile on `[0,2]` has zero endpoint values and slopes `1,-2`. Its
terminal slope is nonzero, its origin row satisfies the natural end condition, and the
weights `1/x⁴ + 1/(2-x)²` and `1/x² + 1` are singular at the ends. The odd smooth
approximants keep the origin slope `1`, so they are nonzero, and their weighted error is
arbitrarily small.
-/

noncomputable section

@[expose] public section

namespace PDE.Examples.Analysis.EndpointFlattening

open Set
open CAS.Splines PDE.Analysis.Calculus
open scoped NNReal ENNReal Topology

private def testMesh : StrictKnotMesh 1 :=
  ⟨fun i ↦ 2 * (i.val : ℝ), by
    intro i j hij
    exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hij) (by norm_num)⟩

private def testData : HermiteData 1 := ⟨![0, 0], ![1, -2]⟩

private abbrev profile : ℝ → ℝ := testData.compactOddProfile testMesh

private def valueWeight (x : ℝ) : ℝ := 1 / x ^ 4 + 1 / (2 - x) ^ 2

private def derivativeWeight (x : ℝ) : ℝ := 1 / x ^ 2 + 1

private theorem test_mesh_zero : testMesh.knot 0 = 0 := by
  norm_num [testMesh, StrictKnotMesh.knot]

private theorem test_natural : testData.NaturalOriginRow testMesh := by
  norm_num [HermiteData.NaturalOriginRow, testData, testMesh, StrictKnotMesh.panelLeft,
    StrictKnotMesh.panelRight, StrictKnotMesh.knot]

private theorem test_interior : testData.C2SlopeEquations testMesh := by
  intro i hi
  have := i.isLt
  omega

private theorem valueWeight_endpoint_bound (x : ℝ) (hx : x ∈ Ioo (2 - 1 / 2) 2) :
    valueWeight x ≤ 2 / (2 - x) ^ 2 := by
  have hx1 : 1 ≤ x := by have := hx.1; cas
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hfour : 1 / x ^ 4 ≤ 1 :=
    (div_le_one (pow_pos hx0 _)).2 (one_le_pow₀ hx1)
  have hd : 0 < 2 - x := sub_pos.mpr hx.2
  have hd1 : (2 - x) ^ 2 ≤ 1 := by have := hx.1; cas
  have ht : 1 ≤ 1 / (2 - x) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hd)).2 (by simpa only [one_mul] using hd1)
  calc
    valueWeight x ≤ 1 + 1 / (2 - x) ^ 2 := add_le_add hfour le_rfl
    _ ≤ 1 / (2 - x) ^ 2 + 1 / (2 - x) ^ 2 := add_le_add ht le_rfl
    _ = 2 / (2 - x) ^ 2 := by rw [← add_div]; norm_num

private theorem derivativeWeight_endpoint_bound (x : ℝ) (hx : x ∈ Ioo (2 - 1 / 2) 2) :
    derivativeWeight x ≤ 2 := by
  have hx1 : 1 ≤ x := by have := hx.1; cas
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have htwo : 1 / x ^ 2 ≤ 1 :=
    (div_le_one (pow_pos hx0 _)).2 (one_le_pow₀ hx1)
  dsimp [derivativeWeight]
  cas

example : testData.slope (Fin.last 1) ≠ 0 := by norm_num [testData]

example : deriv profile 0 = 1 := by
  simpa [profile, testData] using
    testData.deriv_compactOddProfile_zero testMesh test_mesh_zero

/-- This profile has a nonzero endpoint slope and the model singular weights.
The approximating family is nonzero because its derivative at the origin equals one. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧ deriv g 0 = 1 ∧ g ≠ 0 ∧
      singularWeightedH1Error valueWeight derivativeWeight (fun x ↦ g x - profile x) 2 <
        ENNReal.ofReal ε := by
  obtain ⟨g, hg, hc, ho, _, _, hs, he⟩ :=
    testData.exists_compactOddProfile_endpoint_approximation testMesh
      test_mesh_zero rfl rfl test_interior test_natural
      (w := valueWeight) (v := derivativeWeight)
      (r := 1 / 2) (A := 2) (B := 2) (by norm_num)
      (by norm_num [testMesh, StrictKnotMesh.knot]) hε (by norm_num) (by norm_num)
      (by simpa [testMesh, StrictKnotMesh.knot] using valueWeight_endpoint_bound)
      (by simpa [testMesh, StrictKnotMesh.knot] using derivativeWeight_endpoint_bound)
  have hs' : deriv g 0 = 1 := by simpa [testData] using hs
  refine ⟨g, hg, hc, ho, hs', ?_, ?_⟩
  · intro hzero
    simp [hzero] at hs'
  · simpa [profile, testMesh, StrictKnotMesh.knot] using he

end PDE.Examples.Analysis.EndpointFlattening

-- The module holds examples and the private data they use.
set_option linter.privateModule false
