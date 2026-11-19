/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import PDE.FDeriv.Calculus

/-!
# Smooth weights for shrinking sublevels

The weight is `χ ((r - t - q(x)) / ε)`. Although `q` may fail to be
differentiable on its zero set, the weight is locally constant there whenever
`t < r - ε`. This is the regularity needed for compact energy integration.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter PDE.Common
open scoped Topology

variable {n : ℕ}

/-- A smooth transition across a shrinking sublevel of a continuous spatial function. -/
def sublevelCutoff (q : ℝ^n → ℝ) (r ε : ℝ) (p : ℝ^(n + 1)) : ℝ :=
  Real.smoothTransition ((r - p 0 - q (spatialPart p)) / ε)

/-- The cutoff is continuous even where its defining spatial function is not differentiable. -/
theorem continuous_sublevelCutoff {q : ℝ^n → ℝ} (hq : Continuous q) (r ε : ℝ) :
    Continuous (sublevelCutoff q r ε) :=
  Real.smoothTransition.continuous.comp
    (((continuous_const.sub (EuclideanSpace.proj 0).continuous).sub
      (hq.comp (spatialPartCLM n).continuous)).div_const ε)

/-- Shrinking-sublevel weights are nonnegative. -/
theorem sublevelCutoff_nonneg (q : ℝ^n → ℝ) (r ε : ℝ) (p : ℝ^(n + 1)) :
    0 ≤ sublevelCutoff q r ε p :=
  Real.smoothTransition.nonneg _

/-- The cutoff is positive inside its shrinking sublevel. -/
theorem sublevelCutoff_pos {q : ℝ^n → ℝ} {r ε t : ℝ} (hε : 0 < ε)
    {x : ℝ^n} (hx : q x < r - t) :
    0 < sublevelCutoff q r ε (timeSpaceCons t x) := by
  apply Real.smoothTransition.pos_of_pos
  simp only [timeSpaceCons_zero, spatialPart_timeSpaceCons]
  exact div_pos (sub_pos.mpr hx) hε

/-- The cutoff vanishes outside its shrinking sublevel. -/
theorem sublevelCutoff_eq_zero {q : ℝ^n → ℝ} {r ε t : ℝ} (hε : 0 < ε)
    {x : ℝ^n} (hx : r - t ≤ q x) :
    sublevelCutoff q r ε (timeSpaceCons t x) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  simp only [timeSpaceCons_zero, spatialPart_timeSpaceCons]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le

/-- The plateau hides any singularity on the zero set of `q`. -/
theorem sublevelCutoff_eventuallyEq_one {q : ℝ^n → ℝ}
    (hq : Continuous q) {r ε : ℝ} (hε : 0 < ε) {p : ℝ^(n + 1)}
    (ht : p 0 < r - ε) (hz : q (spatialPart p) = 0) :
    sublevelCutoff q r ε =ᶠ[𝓝 p] fun _ ↦ (1 : ℝ) := by
  have hc : Continuous (fun z : ℝ^(n + 1) ↦ (r - z 0 - q (spatialPart z)) / ε) :=
    ((continuous_const.sub (EuclideanSpace.proj 0).continuous).sub
      (hq.comp (spatialPartCLM n).continuous)).div_const ε
  have hp : 1 < (r - p 0 - q (spatialPart p)) / ε := by
    rw [hz, sub_zero, lt_div_iff₀ hε]
    linarith
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hp] with z hz'
  exact Real.smoothTransition.one_of_one_le hz'.le

/-- Away from the zero set, ordinary composition proves cutoff regularity. -/
theorem contDiffAt_sublevelCutoff_of_contDiffAt {q : ℝ^n → ℝ} {r ε : ℝ}
    {p : ℝ^(n + 1)} (hq : ContDiffAt ℝ 1 q (spatialPart p)) :
    ContDiffAt ℝ 1 (sublevelCutoff q r ε) p := by
  apply Real.smoothTransition.contDiffAt.comp
  exact ((contDiffAt_const.sub (EuclideanSpace.proj 0).contDiff.contDiffAt).sub
    (hq.comp p (spatialPartCLM n).contDiff.contDiffAt)).div_const ε

/-- The cutoff is `C¹` before its plateau reaches the zero level. -/
theorem contDiffAt_sublevelCutoff {q : ℝ^n → ℝ}
    (hq : Continuous q) (hqd : ∀ x, q x ≠ 0 → ContDiffAt ℝ 1 q x)
    {r ε : ℝ} (hε : 0 < ε) {p : ℝ^(n + 1)} (ht : p 0 < r - ε) :
    ContDiffAt ℝ 1 (sublevelCutoff q r ε) p := by
  by_cases hz : q (spatialPart p) = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (sublevelCutoff_eventuallyEq_one hq hε ht hz)
  · exact contDiffAt_sublevelCutoff_of_contDiffAt (hqd _ hz)

/-- The actual time derivative of the cutoff has the sign of a shrinking sublevel. -/
theorem partialDeriv_time_sublevelCutoff {q : ℝ^n → ℝ}
    {r ε t : ℝ} {x : ℝ^n}
    (hw : DifferentiableAt ℝ (sublevelCutoff q r ε) (timeSpaceCons t x)) :
    (∂[0] (sublevelCutoff q r ε)) (timeSpaceCons t x) =
      -deriv Real.smoothTransition ((r - t - q x) / ε) / ε := by
  have hd := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    ((r - t - q x) / ε) |>.hasDerivAt
  have hi := (((hasDerivAt_id t).const_sub r).sub_const (q x)).div_const ε
  have hc := hd.comp t hi
  have heq : (fun s ↦ sublevelCutoff q r ε (timeSpaceCons s x)) =
      (fun s ↦ Real.smoothTransition ((r - s - q x) / ε)) := by
    funext s
    simp [sublevelCutoff]
  have hh := (hasDerivAt_timeSpaceCons (sublevelCutoff q r ε) t x hw)
  rw [heq] at hh
  convert hh.unique hc using 1
  ring

/-- Each spatial derivative is the derivative of `q` times the common transition slope. -/
theorem partialDeriv_spatial_sublevelCutoff {q : ℝ^n → ℝ}
    {r ε t : ℝ} {x : ℝ^n} (hε : 0 < ε) (hq : ContDiffAt ℝ 1 q x)
    (j : Fin n) :
    (∂[j.succ] (sublevelCutoff q r ε)) (timeSpaceCons t x) =
      -deriv Real.smoothTransition ((r - t - q x) / ε) / ε * (∂[j] q) x := by
  have hq' := hq.differentiableAt one_ne_zero
  have hw : DifferentiableAt ℝ (sublevelCutoff q r ε) (timeSpaceCons t x) :=
    (contDiffAt_sublevelCutoff_of_contDiffAt (by simpa using hq)).differentiableAt
      one_ne_zero
  rw [← partialDeriv_timeSpaceCons_spatial j _ t x hw]
  have heq : (fun y ↦ sublevelCutoff q r ε (timeSpaceCons t y)) =
      fun y ↦ Real.smoothTransition ((r - t - q y) / ε) := by
    funext y
    simp [sublevelCutoff]
  have harg : DifferentiableAt ℝ (fun y ↦ (r - t - q y) / ε) x := by
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const (r - t)).sub hq').mul (differentiableAt_const _)
  rw [heq, partialDeriv_comp_real j
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _)
    harg]
  rw [partialDeriv_div j (fun y ↦ r - t - q y) (fun _ ↦ ε) x
    ((differentiableAt_const (r - t)).sub hq')
    (differentiableAt_const ε) hε.ne']
  rw [partialDeriv_sub (f := fun _ ↦ r - t) (g := q)
    (differentiableAt_const (r - t)) hq']
  simp only [partialDeriv_const, zero_sub, mul_zero, sub_zero]
  field_simp

/-- The common slope in the characteristic term is nonnegative. -/
theorem sublevelCutoff_slope_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ deriv Real.smoothTransition s / ε :=
  div_nonneg Real.smoothTransition.monotone.deriv_nonneg hε.le

end PDE.Analysis
