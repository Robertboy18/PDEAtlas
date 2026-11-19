/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.CurvatureDownBound
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Weights.CurvatureUpBound
import CAS.CEGA
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# The curvature expression for the linear fast shooting weights

At a gate level `y`, write `s = g y`, `v = deriv g y`, and
`w = deriv (deriv g) y`. The value `r` is the ratio of the upward and downward
weights. The expression below is the cancellation of the unknown constant in
the speed variation: `Q'' - (R'' / R') * Q'` for `Q = qMinus + R * qPlus`.

The scalar estimate uses the gate interval and the primitive bounds on `g`,
its first two derivatives, and `R`.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- The explicit curvature expression after cancellation of the constant part
of the upward speed variation. The scalar arguments are the level, the clock
value and its first two derivatives, and the upward/downward weight ratio. -/
def linearFastWeightCurvature (y s v w r : ℝ) : ℝ :=
  let u := s + 1
  let d := 4 - s
  let J := 4 - v
  let H := 5 * J / (u * d)
  let L := -w / J - v * (d - u) / (u * d)
  let qm1 := (J * y - d) / d ^ 2
  let qm2 := (4 - y * w) / d ^ 2 + 2 * v * (J * y - d) / d ^ 3
  let qp1 := (J * y + u) / u ^ 2
  let qp2 := (4 - y * w) / u ^ 2 - 2 * v * (J * y + u) / u ^ 3
  qm2 - (H + L) * qm1 + r * ((H - L) * qp1 + qp2)

private theorem linear_fast_up_speed_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (7 / 5)) :
    s + 1 ∈ Set.Icc (2 : ℝ) (12 / 5) := by
  cega

private theorem linear_fast_down_speed_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (7 / 5)) :
    4 - s ∈ Set.Icc (13 / 5 : ℝ) 3 := by
  cega

private theorem linear_fast_shifted_deriv_mem_Icc {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (201 / 4000)) :
    4 - v ∈ Set.Icc (15799 / 4000 : ℝ) 4 := by
  cega

-- Both factors depend on the same clock value; separate speed bounds lose this estimate.
private theorem linear_fast_passage_product_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (1 : ℝ) (7 / 5)) :
    (s + 1) * (4 - s) ∈ Set.Icc (6 : ℝ) (25 / 4) := by
  cega

private theorem linear_fast_log_slope_mem_Icc {J p : ℝ} (hJ : J ∈ Set.Icc (15799 / 4000 : ℝ) 4)
    (hp : p ∈ Set.Icc (6 : ℝ) (25 / 4)) :
    5 * J / p ∈ Set.Icc (78 / 25 : ℝ) (10 / 3) := by
  cega

private theorem linear_fast_log_correction_mem_Icc {u d J p v w : ℝ}
    (hu : u ∈ Set.Icc (2 : ℝ) (12 / 5)) (hd : d ∈ Set.Icc (13 / 5 : ℝ) 3)
    (hJ : J ∈ Set.Icc (15799 / 4000 : ℝ) 4) (hp : p ∈ Set.Icc (6 : ℝ) (25 / 4))
    (hv : v ∈ Set.Icc (0 : ℝ) (201 / 4000)) (hw : w ∈ Set.Icc (0 : ℝ) (1 / 1000000)) :
    -w / J - v * (d - u) / p ∈ Set.Icc (-9 / 1000 : ℝ) 0 := by
  cega

private theorem linear_fast_down_first_ge {y J d : ℝ} (hy : y ∈ Set.Icc (205 : ℝ) (2051 / 10))
    (hJ : J ∈ Set.Icc (15799 / 4000 : ℝ) 4) (hd : d ∈ Set.Icc (13 / 5 : ℝ) 3) :
    (88 : ℝ) ≤ (J * y - d) / d ^ 2 := by
  cega

private theorem linear_fast_up_first_mem_Icc {y J u : ℝ} (hy : y ∈ Set.Icc (205 : ℝ) (2051 / 10))
    (hJ : J ∈ Set.Icc (15799 / 4000 : ℝ) 4) (hu : u ∈ Set.Icc (2 : ℝ) (12 / 5)) :
    (J * y + u) / u ^ 2 ∈ Set.Icc (0 : ℝ) 207 := by
  cega

/-- On the gate's scalar ranges, the curvature expression is strictly
negative with a margin of at least `260`. The hypotheses bound primitive
clock data, rather than the curvature or rank being concluded. -/
theorem linear_fast_weight_curvature_lt {y s v w r : ℝ} (hy : y ∈ Set.Icc (205 : ℝ) (2051 / 10))
    (hs : s ∈ Set.Icc (1 : ℝ) (7 / 5)) (hv : v ∈ Set.Icc (0 : ℝ) (201 / 4000))
    (hw : w ∈ Set.Icc (0 : ℝ) (1 / 1000000)) (hr : r ∈ Set.Icc (0 : ℝ) (1 / 100)) :
    linearFastWeightCurvature y s v w r < -260 := by
  have hu : s + 1 ∈ Set.Icc (2 : ℝ) (12 / 5) := linear_fast_up_speed_mem_Icc hs
  have hd : 4 - s ∈ Set.Icc (13 / 5 : ℝ) 3 := linear_fast_down_speed_mem_Icc hs
  have hJ : 4 - v ∈ Set.Icc (15799 / 4000 : ℝ) 4 := linear_fast_shifted_deriv_mem_Icc hv
  -- The product bound keeps the relation between the two passage speeds.
  have hp : (s + 1) * (4 - s) ∈ Set.Icc (6 : ℝ) (25 / 4) := linear_fast_passage_product_mem_Icc hs
  unfold linearFastWeightCurvature
  dsimp only
  generalize s + 1 = u at hu hp ⊢
  generalize 4 - s = d at hd hp ⊢
  generalize 4 - v = J at hJ ⊢
  generalize u * d = p at hp ⊢
  let H : ℝ := 5 * J / p
  let L : ℝ := -w / J - v * (d - u) / p
  let qm1 : ℝ := (J * y - d) / d ^ 2
  let qm2 : ℝ := (4 - y * w) / d ^ 2 + 2 * v * (J * y - d) / d ^ 3
  let qp1 : ℝ := (J * y + u) / u ^ 2
  let qp2 : ℝ := (4 - y * w) / u ^ 2 - 2 * v * (J * y + u) / u ^ 3
  change qm2 - (H + L) * qm1 + r * ((H - L) * qp1 + qp2) < -260
  have hH : H ∈ Set.Icc (78 / 25 : ℝ) (10 / 3) := linear_fast_log_slope_mem_Icc hJ hp
  have hL : L ∈ Set.Icc (-9 / 1000 : ℝ) 0 := linear_fast_log_correction_mem_Icc hu hd hJ hp hv hw
  have hqm1 : (88 : ℝ) ≤ qm1 := linear_fast_down_first_ge hy hJ hd
  have hqm2 : qm2 ≤ (6 : ℝ) := linear_fast_down_second_le hy hJ hd hv hw
  have hqp1 : qp1 ∈ Set.Icc (0 : ℝ) 207 := linear_fast_up_first_mem_Icc hy hJ hu
  have hqp2 : qp2 ≤ (1 : ℝ) := linear_fast_up_second_le hy hJ hu hv hw
  have hsum : (311 / 100 : ℝ) ≤ H + L := by linarith only [hH.1, hL.1]
  have hdiff : H - L ≤ (3343 / 1000 : ℝ) := by linarith only [hH.2, hL.1]
  have hmain : (311 / 100 : ℝ) * 88 ≤ (H + L) * qm1 :=
    mul_le_mul hsum hqm1 (by norm_num) (by linarith only [hsum])
  have hsmall : (H - L) * qp1 + qp2 ≤ (3343 / 1000 : ℝ) * 207 + 1 := by
    have hmul := mul_le_mul hdiff hqp1.2 hqp1.1 (by norm_num)
    linarith only [hmul, hqp2]
  have hweighted : r * ((H - L) * qp1 + qp2) ≤ (1 / 100 : ℝ) * ((3343 / 1000 : ℝ) * 207 + 1) := by
    calc
      r * ((H - L) * qp1 + qp2) ≤ r * ((3343 / 1000 : ℝ) * 207 + 1) :=
        mul_le_mul_of_nonneg_left hsmall hr.1
      _ ≤ (1 / 100 : ℝ) * ((3343 / 1000 : ℝ) * 207 + 1) :=
        mul_le_mul_of_nonneg_right hr.2 (by norm_num)
  have hbound : qm2 - (H + L) * qm1 + r * ((H - L) * qp1 + qp2) ≤ 6 - (311 / 100 : ℝ) * 88 +
        (1 / 100 : ℝ) * ((3343 / 1000 : ℝ) * 207 + 1) := by
    linarith only [hqm2, hmain, hweighted]
  exact hbound.trans_lt (by norm_num)

/-- A passage-time separation of at least `8/5` makes the exponential
weight ratio smaller than `1/100`, uniformly over the clock values on the gate. -/
theorem linear_fast_weight_ratio_lt {s gap : ℝ}
    (hs : s ∈ Set.Icc (1 : ℝ) (7 / 5)) (hgap : (8 / 5 : ℝ) ≤ gap) :
    (4 - s) / (s + 1) * Real.exp (-4 * gap) < (1 / 100 : ℝ) := by
  have hratio : (4 - s) / (s + 1) ≤ (3 / 2 : ℝ) := by cega
  have hexp : Real.exp (-4 * gap) ≤ Real.exp (-32 / 5 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsmall : (3 / 2 : ℝ) * Real.exp (-32 / 5 : ℝ) < (1 / 100 : ℝ) := by cega
  calc
    (4 - s) / (s + 1) * Real.exp (-4 * gap) ≤ (3 / 2 : ℝ) * Real.exp (-4 * gap) :=
      mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
    _ ≤ (3 / 2 : ℝ) * Real.exp (-32 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ < (1 / 100 : ℝ) := hsmall

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
