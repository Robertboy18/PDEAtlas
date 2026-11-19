/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Bounds at the foot of the vertical axis

For a point `x` of the open quadrant `{y | 0 < y₀, 0 < y₁}` of the plane, its foot on the
vertical axis is `(0, x₁)`, and the points `z_s = x - (x₀ - s) e₀ = (s, x₁)`, `0 < s < x₀`, of the
horizontal segment between them lie in the quadrant. If `g` tends to `0` at the foot from the
quadrant, a Hölder bound `|g(x) - g(z_s)| ≤ A (x₀ - s)^{1/2}` passes to the limit `s → 0` and gives
`|g(x)| ≤ A x₀^{1/2}`. This is how a weighted Hölder seminorm controls a sup norm with a weight
singular like `x₀^{-1/2}` on the axis.

## Main results

* `axis_segment_mem`: `z_s` lies in the quadrant, `x₁ ≤ |z_s| ≤ |x|` and `|x - z_s| = x₀ - s`.
* `abs_le_of_tendsto_axis_foot`: `|g(x)| ≤ A x₀^{1/2}` from the limit at the foot and the Hölder
  bound against the points `z_s`.
-/

@[expose] public section

namespace PDE.Analysis

open Set Filter
open scoped Topology

/-- **The horizontal segment to the foot of the axis**: for `x` in the open quadrant and
`0 < s < x₀` the point `z = (s, x₁) = x - (x₀ - s) e₀` lies in the open quadrant,
`x₁ ≤ |z| ≤ |x|` and `|x - z| = x₀ - s`. -/
theorem axis_segment_mem {x : ℝ^2} (hx0 : 0 < x 0) (hx1 : 0 < x 1) {s : ℝ}
    (hs : s ∈ Ioo 0 (x 0)) :
    x - (x 0 - s) • EuclideanSpace.single 0 1 ∈ {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1} ∧
      x 1 ≤ ‖x - (x 0 - s) • EuclideanSpace.single 0 1‖ ∧
      ‖x - (x 0 - s) • EuclideanSpace.single 0 1‖ ≤ ‖x‖ ∧
      ‖x - (x - (x 0 - s) • EuclideanSpace.single 0 1)‖ = x 0 - s := by
  set z : ℝ^2 := x - (x 0 - s) • EuclideanSpace.single 0 1 with hz
  have hz0 : z 0 = s := by simp [hz]
  have hz1 : z 1 = x 1 := by simp [hz]
  have hn : ∀ y : ℝ^2, ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := fun y ↦ by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [sq_abs]
  have hzn := hn z
  have hxn := hn x
  rw [hz0, hz1] at hzn
  have hs2 : s ^ 2 ≤ x 0 ^ 2 := by nlinarith [hs.1, hs.2]
  refine ⟨⟨by rw [hz0]; exact hs.1, by rw [hz1]; exact hx1⟩, ?_, ?_, ?_⟩
  · nlinarith [norm_nonneg z, sq_nonneg s]
  · nlinarith [norm_nonneg z, norm_nonneg x]
  · rw [hz, sub_sub_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith [hs.2])]

/-- **The bound at the foot of the axis**: for `x` in the open quadrant, if `g` tends to `0` at the
foot `(0, x₁)` from the quadrant and `|g(x) - g(s, x₁)| ≤ A (x₀ - s)^{1/2}` for `0 < s < x₀`, then
`|g(x)| ≤ A x₀^{1/2}`. The point `(s, x₁)` is written `x - (x₀ - s) e₀`. -/
theorem abs_le_of_tendsto_axis_foot {g : ℝ^2 → ℝ} {A : ℝ} {x : ℝ^2} (hx0 : 0 < x 0)
    (hx1 : 0 < x 1)
    (hg : Tendsto g (𝓝[{y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}] (EuclideanSpace.single 1 (x 1))) (𝓝 0))
    (h : ∀ s ∈ Ioo 0 (x 0), |g x - g (x - (x 0 - s) • EuclideanSpace.single 0 1)| ≤
      A * (x 0 - s) ^ (1 / 2 : ℝ)) :
    |g x| ≤ A * x 0 ^ (1 / 2 : ℝ) := by
  set e : ℝ^2 := EuclideanSpace.single 0 1 with he
  set z : ℝ → ℝ^2 := fun s ↦ x - (x 0 - s) • e with hz
  have hz0 : ∀ s, z s 0 = s := fun s ↦ by simp [hz, he]
  have hz1 : ∀ s, z s 1 = x 1 := fun s ↦ by simp [hz, he]
  have hfoot : z 0 = EuclideanSpace.single 1 (x 1) := by
    ext i; fin_cases i <;> simp [hz, he]
  have hzc : Continuous z := by simp only [hz]; fun_prop
  have hzt : Tendsto z (𝓝[>] 0)
      (𝓝[{y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}] (EuclideanSpace.single 1 (x 1))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z ?_ ?_
    · rw [← hfoot]; exact (hzc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hx0] with s hs
      exact ⟨by rw [hz0]; exact hs.1, by rw [hz1]; exact hx1⟩
  have hlim : Tendsto (fun s ↦ |g x - g (z s)|) (𝓝[>] 0) (𝓝 |g x - 0|) :=
    (tendsto_const_nhds.sub (hg.comp hzt)).abs
  have hr : Tendsto (fun s : ℝ ↦ A * (x 0 - s) ^ (1 / 2 : ℝ)) (𝓝[>] 0)
      (𝓝 (A * (x 0 - 0) ^ (1 / 2 : ℝ))) := by
    refine (tendsto_const_nhds.mul ?_).mono_left nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub tendsto_id).rpow_const (Or.inr (by norm_num))
  have hle := le_of_tendsto_of_tendsto hlim hr (by
    filter_upwards [Ioo_mem_nhdsGT hx0] with s hs using h s hs)
  simpa using hle

end PDE.Analysis
