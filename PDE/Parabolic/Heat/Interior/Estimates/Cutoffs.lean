/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Residual
import PDE.Analysis.Calculus.LocalExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Fixed cutoffs for the unit heat cylinder

The spatial cutoff is one through radius `3/4` and supported through radius
`7/8`. The time cutoff is one after time `-1/2` and zero before `-3/4`.
Consequently the cutoff residual is supported away from a neighborhood of
the half cylinder. A single smooth compactly supported kernel, depending only
on the dimension, agrees with the Gaussian at every difference relevant to
that residual.
-/

@[expose] public noncomputable section

open PDE (laplacian)

open Filter Metric Set
open scoped Topology ContDiff

namespace HeatEquation

/-- The fixed spatial cutoff used in the unit-cylinder interior estimate. -/
def unitSpatialCutoff (n : ℕ) : ContDiffBump (0 : ℝ^n) :=
  { rIn := 3 / 4
    rOut := 7 / 8
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }

/-- The fixed time cutoff used in the unit-cylinder interior estimate. -/
def unitTimeCutoff (t : ℝ) : ℝ := Real.smoothTransition (4 * t + 3)

/-- The time cutoff is smooth to every order. -/
theorem contDiff_unitTimeCutoff {m : ℕ∞} : ContDiff ℝ m unitTimeCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- The time cutoff vanishes throughout the initial part of the unit interval. -/
theorem unitTimeCutoff_eq_zero {t : ℝ} (ht : t ≤ -3 / 4) : unitTimeCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The time cutoff is one after the transition interval. -/
theorem unitTimeCutoff_eq_one {t : ℝ} (ht : -1 / 2 ≤ t) : unitTimeCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The time cutoff has zero derivative beyond its transition interval. -/
theorem deriv_unitTimeCutoff_eq_zero {t : ℝ} (ht : -1 / 2 < t) :
    deriv unitTimeCutoff t = 0 := by
  have heq : unitTimeCutoff =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact unitTimeCutoff_eq_one hs.le
  simpa only [deriv_const] using heq.deriv_eq

/-- The spacetime cutoff residual vanishes in the inner region where
both cutoffs are constant. Only the heat identity at that point is used. -/
theorem unitCutoff_heatResidual_eq_zero
    {n : ℕ} {u : ℝ^n → ℝ} {D : ℝ} {y : ℝ^n} {s : ℝ}
    (hy : ‖y‖ < 3 / 4) (hs : -1 / 2 < s)
    (hheat : D - laplacian u y = 0) :
    deriv unitTimeCutoff s * (unitSpatialCutoff n y * u y) +
        unitTimeCutoff s * (unitSpatialCutoff n y * D -
          laplacian (fun z ↦ unitSpatialCutoff n z * u z) y) = 0 := by
  have hone : (unitSpatialCutoff n : ℝ^n → ℝ) =ᶠ[𝓝 y] fun _ ↦ 1 :=
    (unitSpatialCutoff n).eventuallyEq_one_of_mem_ball (by
      simpa only [unitSpatialCutoff, mem_ball, dist_zero_right] using hy)
  rw [deriv_unitTimeCutoff_eq_zero hs,
    spatialCutoff_heatResidual_eq_zero hone hheat, zero_mul, mul_zero, add_zero]

/-- One compact smooth kernel agrees with the Gaussian at all differences
between a neighborhood of the half cylinder and the cutoff source region.
Its choice depends on the dimension alone. -/
theorem exists_compact_heatKernel_on_unitCutoff
    (n : ℕ) :
    ∃ G : ℝ^n × ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ (x y : ℝ^n) (t s : ℝ),
        ‖x‖ < 5 / 8 → -3 / 8 < t → t ≤ 0 →
        ‖y‖ ≤ 7 / 8 → -1 ≤ s → s ≤ 0 →
        (3 / 4 ≤ ‖y‖ ∨ s ≤ -1 / 2) →
        G ((x, t) - (y, s)) = fundamentalSolutionHeat (x - y) (t - s) := by
  obtain ⟨G, hG, hc, hmatch⟩ :=
    (contDiffOn_fundamentalSolutionHeat (n := n)
      (m := (⊤ : ℕ∞))).exists_contDiff_compactSupport_eqOn_annulus
      (a := 1 / 8) (b := 3) (by norm_num) (by norm_num)
  refine ⟨G, hG, hc, fun x y t s hx ht ht0 hy hs hs0 hsource ↦ ?_⟩
  have hgap : 1 / 8 ≤ ‖(x, t) - (y, s)‖ := by
    change 1 / 8 ≤ max ‖x - y‖ ‖t - s‖
    rcases hsource with hys | hst
    · have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub x y
      have hsp : 1 / 8 ≤ ‖x - y‖ := by linarith
      exact hsp.trans (le_max_left _ _)
    · have htime : 1 / 8 ≤ ‖t - s‖ := by
        rw [Real.norm_eq_abs]
        linarith [le_abs_self (t - s)]
      exact htime.trans (le_max_right _ _)
  have hbound : ‖(x, t) - (y, s)‖ ≤ 3 := by
    change max ‖x - y‖ ‖t - s‖ ≤ 3
    apply max_le
    · linarith [norm_sub_le x y]
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  exact hmatch _ hgap hbound

end HeatEquation
