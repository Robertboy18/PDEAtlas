/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.Normalize
public import PDE.Analysis.Calculus.Rellich.Field
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Norm
import CAS.ExactTactic

/-!
# Cutting off the radial square flux at its centre

The multiplier `b(ε / ‖x - c‖)` vanishes near `c` and tends to one away from `c`.
Its differentiated contribution is bounded by a constant times
`ε * w(x)² / ‖x - c‖²`. This is the weight controlled by the ball Hardy inequality.
The cut-off vector field is C¹ even when the scalar data have no limit at the centre.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.RadialSquareFlux

open MeasureTheory Metric Set Filter NormedSpace
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- A fixed smooth bump, equal to one on `[-1,1]` and zero outside `(-2,2)`. -/
def radialBump : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The radial square flux with a deleted neighbourhood of its centre. -/
def cutoffField (ε : ℝ) (c : ℝ^n) (w : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  (radialBump (ε / ‖x - c‖) / ‖x - c‖ * w x ^ 2) • (x - c)

/-- Although the formula contains inverse radii, the field is identically zero near the centre. -/
theorem cutoffField_eq_zero {ε : ℝ} (c : ℝ^n) (w : ℝ^n → ℝ)
    {x : ℝ^n} (hx : ‖x - c‖ < ε / 2) : cutoffField ε c w x = 0 := by
  have hε : 0 < ε := by linarith [norm_nonneg (x - c)]
  by_cases hxc : x = c
  · simp [cutoffField, hxc]
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
  have hb : radialBump (ε / ‖x - c‖) = 0 := by
    apply radialBump.zero_of_le_dist
    change 2 ≤ dist (ε / ‖x - c‖) 0
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hε hn)]
    apply (le_div_iff₀ hn).mpr
    linarith
  simp [cutoffField, hb]

/-- The cutoff is C¹ at the centre regardless of the scalar data there. -/
theorem contDiffAt_cutoffField {ε : ℝ} (hε : 0 < ε) {c x : ℝ^n} {w : ℝ^n → ℝ}
    (hw : x ≠ c → ContDiffAt ℝ 1 w x) : ContDiffAt ℝ 1 (cutoffField ε c w) x := by
  by_cases hx : x = c
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ^n))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds c (by positivity : 0 < ε / 2)] with x hx
    exact cutoffField_eq_zero c w (by simpa [dist_eq_norm] using hx)
  · have hn : ContDiffAt ℝ 1 (fun y : ℝ^n ↦ ‖y - c‖) x :=
      (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)
    exact (((radialBump.contDiffAt.comp x (contDiffAt_const.div hn
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)))).div hn
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))).mul ((hw hx).pow 2)).smul
        (contDiffAt_id.sub contDiffAt_const)

/-- A punctured C¹ scalar field gives a globally C¹ cutoff flux. -/
theorem contDiff_cutoffField {ε : ℝ} (hε : 0 < ε) {c : ℝ^n} {w : ℝ^n → ℝ}
    (hw : ∀ x, x ≠ c → ContDiffAt ℝ 1 w x) : ContDiff ℝ 1 (cutoffField ε c w) :=
  contDiff_iff_contDiffAt.mpr fun x ↦ contDiffAt_cutoffField hε (hw x)

/-- Divergence of a scalar radial multiple of the dilation vector field. -/
theorem divergence_radial_smul {a : ℝ → ℝ} {a' : ℝ} {c x : ℝ^n}
    (hx : x ≠ c) (ha : HasDerivAt a a' ‖x - c‖) :
    ∇· (fun y ↦ a ‖y - c‖ • (y - c)) x =
      a' * ‖x - c‖ + (n : ℝ) * a ‖x - c‖ := by
  have hn := (contDiffAt_norm ℝ (sub_ne_zero.mpr hx)).differentiableAt
    (show (1 : WithTop ℕ∞) ≠ 0 by simp)
  have hd := hn.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  have hcomp := ha.comp_hasFDerivAt x hd
  rw [divergence_smul (a := fun y ↦ a ‖y - c‖) (F := fun y ↦ y - c)
      hcomp.differentiableAt (differentiableAt_id.sub_const c),
    show fderiv ℝ (fun y ↦ a ‖y - c‖) x = _ from hcomp.fderiv,
    divergence_sub_const]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [hn.fderiv_norm_self]
  ring

/-- The cutoff divergence has the desired radial density and an explicit inverse-square error. -/
theorem divergence_cutoffField {ε : ℝ} {c x : ℝ^n} {w : ℝ^n → ℝ}
    (hx : x ≠ c) (hw : DifferentiableAt ℝ w x) :
    ∇· (cutoffField ε c w) x =
      radialBump (ε / ‖x - c‖) *
        (((n : ℝ) - 1) * w x ^ 2 / ‖x - c‖ +
          2 * w x * fderiv ℝ w x (normalize (x - c))) -
      ε * deriv radialBump (ε / ‖x - c‖) * (w x ^ 2 / ‖x - c‖ ^ 2) := by
  let r := ‖x - c‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hb := (radialBump.contDiff.differentiable (by simp : (1 : WithTop ℕ∞) ≠ 0)
    (ε / r)).hasDerivAt
  have hi : HasDerivAt (fun s : ℝ ↦ ε / s) (-ε / r ^ 2) r := by
    cas using hr
  have ha := (hb.comp r hi).div (hasDerivAt_id r) hr
  let a : ℝ → ℝ := fun s ↦ radialBump (ε / s) / s
  have hn := (contDiffAt_norm ℝ (sub_ne_zero.mpr hx)).differentiableAt
    (show (1 : WithTop ℕ∞) ≠ 0 by simp)
  have haDiff : DifferentiableAt ℝ (fun y : ℝ^n ↦ a ‖y - c‖ • (y - c)) x :=
    (ha.differentiableAt.comp x (hn.comp x (differentiableAt_id.sub_const c))).smul
      (differentiableAt_id.sub_const c)
  have hfield : cutoffField ε c w =
      fun y ↦ w y ^ 2 • (a ‖y - c‖ • (y - c)) := by
    funext y
    simp only [cutoffField, a, smul_smul, mul_comm]
  rw [hfield, divergence_smul (a := fun y ↦ w y ^ 2) (hw.pow 2) haDiff,
    show fderiv ℝ (fun y ↦ w y ^ 2) x = _ from (hw.hasFDerivAt.pow 2).fderiv,
    divergence_radial_smul (a := a) hx ha]
  have hwRad : fderiv ℝ w x (x - c) = r * fderiv ℝ w x (normalize (x - c)) := by
    conv_lhs => rw [← norm_smul_normalize (x - c)]
    simp only [map_smul, smul_eq_mul, r]
  simp only [smul_apply, smul_eq_mul, Nat.reduceSub, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, map_smul, hwRad, a]
  change _ = radialBump (ε / r) *
    (((n : ℝ) - 1) * w x ^ 2 / r + 2 * w x * fderiv ℝ w x (normalize (x - c))) -
    ε * deriv radialBump (ε / r) * (w x ^ 2 / r ^ 2)
  simp only [Function.comp_def, id_eq]
  dsimp [r] at hr ⊢
  field_simp
  ring

/-- The derivative of the fixed bump has a uniform bound. -/
theorem exists_bound_deriv_radialBump :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖deriv radialBump s‖ ≤ C := by
  obtain ⟨C, hC⟩ := radialBump.hasCompactSupport.deriv.exists_bound_of_continuous
    ((radialBump.contDiff (n := 1)).continuous_deriv (by simp))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

end PDE.Analysis.RadialSquareFlux
