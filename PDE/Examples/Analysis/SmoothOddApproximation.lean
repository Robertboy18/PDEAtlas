/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteSmoothApproximation
import CAS.ExactTactic

/-!
# Smoothing an odd spline with singular weights

Two Hermite panels on `[0,2]`, with values `0,2/3,0` and slopes `1,0,-1`.
The first two jets match at the interior knot, while the third jets differ. The
terminal slope is nonzero. The weights have both origin and endpoint singularities.
-/

set_option linter.privateModule false

noncomputable section

@[expose] public section

namespace PDE.Examples.Analysis.SmoothOddApproximation

open Set MeasureTheory
open CAS.Splines PDE.Analysis.Calculus
open scoped Topology NNReal ENNReal ContDiff

private def smoothTestMesh : StrictKnotMesh 2 :=
  ⟨fun i ↦ (i.val : ℝ), fun _ _ hij ↦ Nat.cast_lt.mpr hij⟩

private def smoothTestData : HermiteData 2 := ⟨![0, 2 / 3, 0], ![1, 0, -1]⟩

private abbrev smoothTestProfile : ℝ → ℝ := smoothTestData.compactOddProfile smoothTestMesh

private def smoothValueWeight (x : ℝ) : ℝ := 1 / x ^ 4 + 1 / (2 - x) ^ 2

private def smoothDerivativeWeight (x : ℝ) : ℝ := 1 / x ^ 2 + 1

private theorem smooth_test_mesh_zero : smoothTestMesh.knot 0 = 0 := by
  norm_num [smoothTestMesh, StrictKnotMesh.knot]

private theorem smooth_test_natural : smoothTestData.NaturalOriginRow smoothTestMesh := by
  norm_num [HermiteData.NaturalOriginRow, smoothTestData, smoothTestMesh,
    StrictKnotMesh.panelLeft, StrictKnotMesh.panelRight, StrictKnotMesh.knot]

private theorem smooth_test_interior : smoothTestData.C2SlopeEquations smoothTestMesh := by
  intro i hi
  have hi0 : i = 0 := by apply Fin.ext; omega
  subst i
  norm_num [smoothTestData, smoothTestMesh, StrictKnotMesh.panelLeft,
    StrictKnotMesh.panelRight, StrictKnotMesh.knot, StrictKnotMesh.rightNeighbor]

/-- The interior knot is a real junction: the third jets differ there, so smoothing is needed. -/
example :
    polynomialJet 3 ((smoothTestData.polynomialData smoothTestMesh).piece 0) 1 = -2 ∧
    polynomialJet 3 ((smoothTestData.polynomialData smoothTestMesh).piece 1) 1 = 2 := by
  norm_num [polynomialJet, HermiteData.polynomialData, smoothTestData, smoothTestMesh,
    StrictKnotMesh.panelLeft, StrictKnotMesh.panelRight, StrictKnotMesh.knot,
    hermitePolynomial, Function.iterate_succ_apply, Polynomial.derivative_mul,
    Polynomial.derivative_pow]

example : smoothTestData.slope (Fin.last 2) = -1 := by norm_num [smoothTestData]

private theorem smooth_value_endpoint_bound (x : ℝ) (hx : x ∈ Ioo (2 - 1 / 2) 2) :
    smoothValueWeight x ≤ 2 / (2 - x) ^ 2 := by
  have hx1 : 1 ≤ x := by have := hx.1; cas
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hfour : 1 / x ^ 4 ≤ 1 :=
    (div_le_one (pow_pos hx0 _)).2 (one_le_pow₀ hx1)
  have hd : 0 < 2 - x := sub_pos.mpr hx.2
  have hd1 : (2 - x) ^ 2 ≤ 1 := by have := hx.1; cas
  have ht : 1 ≤ 1 / (2 - x) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hd)).2 (by simpa only [one_mul] using hd1)
  calc
    smoothValueWeight x ≤ 1 + 1 / (2 - x) ^ 2 := add_le_add hfour le_rfl
    _ ≤ 1 / (2 - x) ^ 2 + 1 / (2 - x) ^ 2 := add_le_add ht le_rfl
    _ = 2 / (2 - x) ^ 2 := by rw [← add_div]; norm_num

private theorem smooth_derivative_endpoint_bound (x : ℝ) (hx : x ∈ Ioo (2 - 1 / 2) 2) :
    smoothDerivativeWeight x ≤ 2 := by
  have hx1 : 1 ≤ x := by have := hx.1; cas
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have htwo : 1 / x ^ 2 ≤ 1 :=
    (div_le_one (pow_pos hx0 _)).2 (one_le_pow₀ hx1)
  dsimp only [smoothDerivativeWeight]
  cas

private theorem smooth_value_continuous :
    ContinuousOn smoothValueWeight (Ioo 0 2) := by
  apply ContinuousOn.add
  · exact continuousOn_const.div (continuousOn_id.pow 4)
      (fun _ hx ↦ pow_ne_zero 4 (ne_of_gt hx.1))
  · exact continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun _ hx ↦ pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hx.2)))

private theorem smooth_derivative_continuous :
    ContinuousOn smoothDerivativeWeight (Ioo 0 2) :=
  (continuousOn_const.div (continuousOn_id.pow 2)
    (fun _ hx ↦ pow_ne_zero 2 (ne_of_gt hx.1))).add continuousOn_const

/-- The output is smooth, compactly supported, odd and nonzero, with the prescribed origin
slope. Its difference from the spline has arbitrarily small singular weighted `H¹` error. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧ tsupport g ⊆ Ioo (-2) 2 ∧
      deriv g 0 = 1 ∧ g ≠ 0 ∧
      deriv (fun x ↦ g x - smoothTestProfile x) 0 = 0 ∧
      singularWeightedH1Error smoothValueWeight smoothDerivativeWeight
        (fun x ↦ g x - smoothTestProfile x) 2 < ENNReal.ofReal ε := by
  obtain ⟨g, hg, hgc, hgo, hgs, _, hgd, hqd, hE⟩ :=
    smoothTestData.exists_compactOddProfile_smooth_initialization smoothTestMesh
      smooth_test_mesh_zero rfl rfl smooth_test_interior smooth_test_natural
      (w := smoothValueWeight) (v := smoothDerivativeWeight)
      (c := 1 / 2) (A := 2) (B := 2) (by norm_num)
      (by norm_num [smoothTestMesh, StrictKnotMesh.knot]) hε (by norm_num) (by norm_num)
      (by unfold smoothValueWeight; fun_prop) (by unfold smoothDerivativeWeight; fun_prop)
      (by intros; unfold smoothValueWeight; positivity)
      (by intros; unfold smoothDerivativeWeight; positivity)
      (by simpa [smoothTestMesh, StrictKnotMesh.knot] using smooth_value_continuous)
      (by simpa [smoothTestMesh, StrictKnotMesh.knot] using smooth_derivative_continuous)
      (by simpa [smoothTestMesh, StrictKnotMesh.knot] using smooth_value_endpoint_bound)
      (by simpa [smoothTestMesh, StrictKnotMesh.knot] using smooth_derivative_endpoint_bound)
  have hs : deriv g 0 = 1 := by simpa [smoothTestData] using hgd
  refine ⟨g, hg, hgc, hgo, ?_, hs, ?_, hqd, ?_⟩
  · simpa [smoothTestMesh, StrictKnotMesh.knot] using hgs
  · exact smoothTestData.ne_zero_of_deriv_eq_slope hgd (by norm_num [smoothTestData])
  · simpa [smoothTestProfile, smoothTestMesh, StrictKnotMesh.knot] using hE

end PDE.Examples.Analysis.SmoothOddApproximation
