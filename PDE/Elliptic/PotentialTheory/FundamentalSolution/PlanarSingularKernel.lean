/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarPrincipalValue

/-!
# Planar singular kernels of order `-2`

A planar singular kernel (a Calderón–Zygmund kernel of order `-2`) with constant `A` is a
measurable `K : ℝ² → ℝ` with

* the size bound `|K(z)| ≤ A / |z|²`,
* the smoothness bound `|K(z) - K(w)| ≤ A |z - w| / |z|³` when `2 |z - w| ≤ |z|`,
* zero mean on every annulus `r ≤ |z| < R`.

These are the only properties of the kernel used by the Hölder estimates of singular integrals
in `PlanarSingularIntegral`. The size bound is stated at every point, so with Lean's
division by zero it forces `K 0 = 0`; the Hessian kernels have that value at the pole.
The half-plane estimates also use zero mean on horizontal lines,
`∫_ℝ K(s, h) ds = 0` for `h ≠ 0`.

The Hessian kernels `kᵢⱼ` of the planar fundamental solution are singular kernels with
constant `5`: with `w = z₀ + i z₁`, `k₀₀ - i k₀₁ = 1/(2w²)` and
`1/(2w²) - 1/(2v²) = (v - w)(v + w)/(2 w² v²)`. They have zero mean on horizontal lines:
`k₀₁(s, h)` is odd in `s` and `k₀₀(s, h) = -(1/2) ∂ₛ (s/(s² + h²))`.

## Main definitions

* `IsSingularKernel`: a planar singular kernel of order `-2` with constant `A`.
* `HasLineCancellation`: zero mean on horizontal lines, `∫_ℝ K(s, h) ds = 0` for every `h ≠ 0`.

## Main results

* `isSingularKernel_hessianKernel`: the Hessian kernels are singular kernels with constant `5`.
* `hasLineCancellation_hessianKernel`: the Hessian kernels have zero mean on horizontal lines.
* `IsSingularKernel.integral_annulus_sub`: zero mean on every annulus around any centre.
* `IsSingularKernel.integrableOn_of_le`: the kernel centred at `x` is integrable on every bounded
  set at distance at least `r > 0` from `x`.
* `HasLineCancellation.integral_sub_vec`: the kernel centred at `x` has zero integral along every
  horizontal line `y₁ = t ≠ x₁`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PotentialTheory.Planar

/-- A planar singular kernel of order `-2` with constant `A`: measurable, bounded by
`A / |z|²`, with `|K(z) - K(w)| ≤ A |z - w| / |z|³` when `2 |z - w| ≤ |z|`, and with zero mean
on every annulus centred at the pole. -/
structure IsSingularKernel (K : ℝ^2 → ℝ) (A : ℝ) : Prop where
  measurable : Measurable K
  abs_le : ∀ z, |K z| ≤ A / ‖z‖ ^ 2
  abs_sub_le : ∀ z w, 2 * ‖z - w‖ ≤ ‖z‖ → |K z - K w| ≤ A * ‖z - w‖ / ‖z‖ ^ 3
  integral_annulus : ∀ r R : ℝ, ∫ z in ball 0 R \ ball 0 r, K z = 0

/-- A kernel has zero mean on horizontal lines: `∫_ℝ K(s, h) ds = 0` for every `h ≠ 0`. -/
def HasLineCancellation (K : ℝ^2 → ℝ) : Prop :=
  ∀ h : ℝ, h ≠ 0 → ∫ s : ℝ, K !₂[s, h] = 0

variable {K : ℝ^2 → ℝ} {A : ℝ}

namespace IsSingularKernel

variable (hK : IsSingularKernel K A)
include hK

/-- The constant of a singular kernel is nonnegative. -/
theorem nonneg : 0 ≤ A := by
  have h := hK.abs_le !₂[1, 0]
  rw [norm_sq_vec] at h
  norm_num at h
  exact (abs_nonneg _).trans h

/-- The size bound at distance at least `r`. -/
theorem abs_le_of_le {r : ℝ} (hr : 0 < r) {z : ℝ^2} (hz : r ≤ ‖z‖) : |K z| ≤ A / r ^ 2 :=
  (hK.abs_le z).trans (div_le_div_of_nonneg_left hK.nonneg (by positivity) (by gcongr))

/-- Zero mean on every annulus around any centre. -/
theorem integral_annulus_sub (x : ℝ^2) (r R : ℝ) :
    ∫ y in ball x R \ ball x r, K (x - y) = 0 := by
  have hS : MeasurableSet (ball (0 : ℝ^2) R \ ball 0 r) :=
    measurableSet_ball.diff measurableSet_ball
  have hSx : MeasurableSet (ball x R \ ball x r) := measurableSet_ball.diff measurableSet_ball
  rw [← integral_indicator hSx]
  have hind : (ball x R \ ball x r).indicator (fun y ↦ K (x - y)) =
      fun y ↦ (ball (0 : ℝ^2) R \ ball 0 r).indicator K (x - y) := by
    funext y
    have hiff : y ∈ ball x R \ ball x r ↔ x - y ∈ ball (0 : ℝ^2) R \ ball 0 r := by
      simp [dist_eq_norm, norm_sub_rev y x]
    by_cases hy : y ∈ ball x R \ ball x r
    · rw [indicator_of_mem hy, indicator_of_mem (hiff.mp hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy (hiff.mpr h))]
  rw [hind, integral_sub_left_eq_self (fun z ↦ (ball (0 : ℝ^2) R \ ball 0 r).indicator K z),
    integral_indicator hS, hK.integral_annulus]

/-- The kernel centred at `x` is integrable on every bounded set at distance at least `r > 0`
from `x`. -/
theorem integrableOn_of_le (x : ℝ^2) {S : Set (ℝ^2)} (hS : MeasurableSet S)
    (hSb : volume S ≠ ⊤) {r : ℝ} (hr : 0 < r) (hSr : ∀ y ∈ S, r ≤ ‖x - y‖) :
    IntegrableOn (fun y ↦ K (x - y)) S := by
  refine Measure.integrableOn_of_bounded (M := A / r ^ 2) hSb
    (hK.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS] with y hy
  rw [Real.norm_eq_abs]
  exact hK.abs_le_of_le hr (hSr y hy)

/-- The size bound on horizontal lines: `|K(s, h)| ≤ A / (s² + h²)`. -/
theorem abs_vec_le (s h : ℝ) : |K !₂[s, h]| ≤ A / (s ^ 2 + h ^ 2) := by
  rw [← norm_sq_vec]
  exact hK.abs_le _

/-- On a horizontal line at height `h ≠ 0` the kernel is integrable. -/
theorem integrable_vec {h : ℝ} (hh : h ≠ 0) : Integrable fun s : ℝ ↦ K !₂[s, h] := by
  have hmeas : Measurable fun s : ℝ ↦ K !₂[s, h] :=
    hK.measurable.comp (by fun_prop)
  have hdom : Integrable fun s : ℝ ↦ A / h ^ 2 * (1 + (s / h) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_div hh).const_mul _
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun s ↦ ?_)
  rw [Real.norm_eq_abs]
  refine (hK.abs_vec_le s h).trans (le_of_eq ?_)
  have hh2 : 0 < h ^ 2 := by positivity
  field_simp
  ring

/-- The kernel centred at `x` is integrable along every horizontal line `y₁ = t ≠ x₁`. -/
theorem integrable_sub_vec (x : ℝ^2) {t : ℝ} (ht : t ≠ x 1) :
    Integrable fun s : ℝ ↦ K (x - !₂[s, t]) := by
  simp_rw [sub_vec]
  exact (hK.integrable_vec (sub_ne_zero.mpr (Ne.symm ht))).comp_sub_left (x 0)

end IsSingularKernel

/-- With zero mean on horizontal lines, the kernel centred at `x` has zero integral along every
horizontal line `y₁ = t ≠ x₁`. -/
theorem HasLineCancellation.integral_sub_vec {K : ℝ^2 → ℝ} (hK : HasLineCancellation K)
    (x : ℝ^2) {t : ℝ} (ht : t ≠ x 1) : ∫ s : ℝ, K (x - !₂[s, t]) = 0 := by
  simp_rw [sub_vec]
  rw [integral_sub_left_eq_self (fun s ↦ K !₂[s, x 1 - t]) volume (x 0)]
  exact hK _ (sub_ne_zero.mpr (Ne.symm ht))

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- `|1/(2w²) - 1/(2v²)| ≤ 5 |w - v| / |w|³` when `2 |w - v| ≤ |w|`. -/
private theorem norm_inv_two_sq_sub_le {w v : ℂ} (h : 2 * ‖w - v‖ ≤ ‖w‖) :
    ‖1 / (2 * w ^ 2) - 1 / (2 * v ^ 2)‖ ≤ 5 * ‖w - v‖ / ‖w‖ ^ 3 := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    obtain rfl : v = 0 :=
      norm_le_zero_iff.mp (by simp only [zero_sub, norm_neg, norm_zero] at h; linarith)
    simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hv : ‖w‖ / 2 ≤ ‖v‖ := by
    have := norm_sub_norm_le w v
    linarith
  have hvpos : 0 < ‖v‖ := by linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  have hsum : ‖v + w‖ ≤ 5 / 2 * ‖w‖ := by
    have h1 := norm_add_le (v - w) (2 * w)
    rw [show v - w + 2 * w = v + w by ring, norm_mul, Complex.norm_two, norm_sub_rev] at h1
    linarith
  have hid : 1 / (2 * w ^ 2) - 1 / (2 * v ^ 2) = (v - w) * (v + w) / (2 * w ^ 2 * v ^ 2) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_sub_rev v w,
    Complex.norm_two]
  have hden : ‖w‖ ^ 4 / 2 ≤ 2 * ‖w‖ ^ 2 * ‖v‖ ^ 2 := by
    have : (‖w‖ / 2) ^ 2 ≤ ‖v‖ ^ 2 := by gcongr
    nlinarith [sq_nonneg ‖w‖]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖w - v‖ * ‖v + w‖ * ‖w‖ ^ 3 ≤ ‖w - v‖ * (5 / 2 * ‖w‖) * ‖w‖ ^ 3 := by gcongr
    _ = 5 * ‖w - v‖ * (‖w‖ ^ 4 / 2) := by ring
    _ ≤ 5 * ‖w - v‖ * (2 * ‖w‖ ^ 2 * ‖v‖ ^ 2) := by gcongr

/-- Each difference `|kᵢⱼ(z) - kᵢⱼ(w)|` is at most `|1/(2 𝔠(z)²) - 1/(2 𝔠(w)²)|`. -/
private theorem abs_hessianKernel_sub_le_norm (i j : Fin 2) (z w : ℝ^2) :
    |hessianKernel i j z - hessianKernel i j w| ≤
      ‖1 / (2 * (𝔠 z) ^ 2) - 1 / (2 * (𝔠 w) ^ 2)‖ := by
  have h00 : |hessianKernel 0 0 z - hessianKernel 0 0 w| ≤
      ‖1 / (2 * (𝔠 z) ^ 2) - 1 / (2 * (𝔠 w) ^ 2)‖ := by
    rw [hessianKernel_zero_zero_eq_re, hessianKernel_zero_zero_eq_re, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have h01 : |hessianKernel 0 1 z - hessianKernel 0 1 w| ≤
      ‖1 / (2 * (𝔠 z) ^ 2) - 1 / (2 * (𝔠 w) ^ 2)‖ := by
    rw [hessianKernel_zero_one_eq_neg_im, hessianKernel_zero_one_eq_neg_im, neg_sub_neg,
      ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (le_of_eq (norm_sub_rev _ _))
  match i, j with
  | 0, 0 => exact h00
  | 0, 1 => exact h01
  | 1, 0 => simpa [hessianKernel_one_zero] using h01
  | 1, 1 =>
    rw [hessianKernel_one_one, hessianKernel_one_one, neg_sub_neg, abs_sub_comm]
    exact h00

/-- **The Hessian kernels are singular kernels with constant `5`.** -/
theorem isSingularKernel_hessianKernel (i j : Fin 2) : IsSingularKernel (hessianKernel i j) 5 where
  measurable := measurable_hessianKernel i j
  abs_le z := (abs_hessianKernel_le i j z).trans (by
    rcases eq_or_ne ‖z‖ 0 with hz | hz
    · simp [hz]
    · have : 0 < ‖z‖ ^ 2 := by positivity
      rw [div_le_div_iff₀ (by positivity) this]
      nlinarith)
  abs_sub_le z w h := by
    refine (abs_hessianKernel_sub_le_norm i j z w).trans ?_
    have h' : 2 * ‖𝔠 z - 𝔠 w‖ ≤ ‖𝔠 z‖ := by
      rw [← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; exact h
    have := norm_inv_two_sq_sub_le h'
    rwa [← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at this
  integral_annulus r R := by
    let S : Set (ℝ^2) := ball 0 R \ ball 0 r
    have hS : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
    rw [← integral_indicator hS]
    have hw : S.indicator (hessianKernel i j) =
        fun z ↦ S.indicator (fun _ ↦ (1 : ℝ)) z * hessianKernel i j z := by
      funext z; by_cases hz : z ∈ S <;> simp [hz]
    rw [hw]
    apply integral_mul_hessianKernel_eq_zero
    · intro z; simp [S, indicator, PDE.Common.norm_coordinateReflection]
    · intro z; simp [S, indicator]

/-- **Zero mean of the Hessian kernels on horizontal lines.** -/
theorem hasLineCancellation_hessianKernel (i j : Fin 2) :
    HasLineCancellation (hessianKernel i j) := by
  have h01 : HasLineCancellation (hessianKernel 0 1) := by
    intro h _
    have hodd : ∀ s : ℝ, hessianKernel 0 1 !₂[-s, h] = -hessianKernel 0 1 !₂[s, h] := by
      intro s
      rw [hessianKernel_zero_one, hessianKernel_zero_one,
        show ‖(!₂[-s, h] : ℝ^2)‖ = ‖(!₂[s, h] : ℝ^2)‖ by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_vec, norm_sq_vec]; ring]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
    have := integral_neg_eq_self (fun s : ℝ ↦ hessianKernel 0 1 !₂[s, h]) volume
    simp only [hodd, integral_neg] at this
    linarith
  have h00 : HasLineCancellation (hessianKernel 0 0) := by
    intro h hh
    have hh2 : 0 < h ^ 2 := by positivity
    have hpos : ∀ s : ℝ, 0 < s ^ 2 + h ^ 2 := fun s ↦ by positivity
    have heq : (fun s : ℝ ↦ hessianKernel 0 0 !₂[s, h]) =
        fun s ↦ (s ^ 2 - h ^ 2) / (2 * (s ^ 2 + h ^ 2) ^ 2) := by
      funext s
      rw [hessianKernel_zero_zero, show ‖(!₂[s, h] : ℝ^2)‖ ^ 4 =
        (‖(!₂[s, h] : ℝ^2)‖ ^ 2) ^ 2 by ring, norm_sq_vec]
      simp
    rw [heq]
    let F : ℝ → ℝ := fun s ↦ -s / (2 * (s ^ 2 + h ^ 2))
    have hderiv (s : ℝ) : HasDerivAt F ((s ^ 2 - h ^ 2) / (2 * (s ^ 2 + h ^ 2) ^ 2)) s := by
      have := hpos s
      convert (hasDerivAt_neg s).div (((hasDerivAt_pow 2 s).add_const (h ^ 2)).const_mul 2)
        (by positivity) using 1
      field_simp
      ring
    have hint : Integrable fun s : ℝ ↦ (s ^ 2 - h ^ 2) / (2 * (s ^ 2 + h ^ 2) ^ 2) := by
      have := (isSingularKernel_hessianKernel 0 0).integrable_vec hh
      rwa [heq] at this
    have hlim : Tendsto F atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_
        (tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos) : Tendsto
          (fun s : ℝ ↦ 1 / (2 * s)) atTop (𝓝 0))
      filter_upwards [eventually_gt_atTop 0] with s hs
      have := hpos s
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hs, abs_of_pos (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hbot : Tendsto F atBot (𝓝 0) := by
      simpa [F, Function.comp_def, neg_div] using (hlim.comp tendsto_neg_atBot_atTop).neg
    rw [integral_of_hasDerivAt_of_tendsto hderiv hint hbot hlim, sub_zero]
  intro h hh
  match i, j with
  | 0, 0 => exact h00 h hh
  | 0, 1 => exact h01 h hh
  | 1, 0 => simpa [hessianKernel_one_zero] using h01 h hh
  | 1, 1 =>
    simp only [hessianKernel_one_one, integral_neg]
    rw [h00 h hh, neg_zero]

end PotentialTheory.Planar
