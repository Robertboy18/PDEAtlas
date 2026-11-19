/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.SingularEndpoints
import Mathlib.MeasureTheory.Function.L2Space
import CAS.ExactTactic
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Hardy square completions at singular endpoints

Integration by parts on an open interval retains the endpoint traces even when the
weight is singular. Completing a square then gives the Hardy constants `4`
and `4/9`, together with boundary remainders of favorable sign.

The weighted `L²` hypotheses make every cross term integrable. Endpoint limits are
explicit hypotheses.

## Main results

* `integral_square_completion_with_bulk`, `integral_square_completion`: the identity for
  `∫₀^L (t v' a - v b)²` when `a b = w` and `w' = -p b²`.
* `integral_origin_square_completion` and `integral_right_square_completion`: the square
  completions (4.13) and (4.14) of Chen, Hou and Huang, with the weights `x⁻²`, `x⁻³` at the
  origin and `(x - L)⁻¹`, `(x - L)⁻²` at `L`.
* `integral_hardy_le`: `∫₀^L (v/(x - d))² ≤ 4 ∫₀^L v'²` when `x - d ≠ 0` on `(0, L)` and both
  boundary products `v²/(x - d)` tend to `0`.
* `integral_weighted_hardy_four_ninths`: `∫₀^L v²/x⁴ ≤ (4/9) ∫₀^L v'²/x² - 2 v(L)²/(3 L³)`.
* `weighted_hardy_damping_nonneg`: the nonnegative damping term in (8.20) of the supplementary
  material of Chen, Hou and Huang.

## Implementation notes

The polynomial identity behind the square completion and the derivatives of the singular weights
are discharged by the `cas` tactic of SymLean, our verified computer algebra system.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  (4.13)-(4.14), and supplementary material (in the same PDF), (8.20).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace SobolevSpace.Hardy

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Square completion with a bulk and boundary remainder when `w = a b` and `w' = -p b²`.

The cross term is integrable by `L²` Cauchy–Schwarz. Choosing `t = 1/p` cancels the
bulk term; choosing `p = 1` and `t = 2` gives the Hardy constant `4`. -/
theorem integral_square_completion_with_bulk
    {L p left right : ℝ} (t : ℝ) {v vX a b w : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hw : ∀ x ∈ Ioo 0 L, HasDerivAt w (-p * b x ^ 2) x)
    (hab : ∀ x ∈ Ioo 0 L, a x * b x = w x)
    (hA : MemLp (fun x ↦ vX x * a x) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x * b x) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ w x * v x ^ 2) (𝓝[>] 0) (𝓝 left))
    (hright : Tendsto (fun x ↦ w x * v x ^ 2) (𝓝[<] L) (𝓝 right)) :
    (∫ x in Ioo 0 L, (t * (vX x * a x) - v x * b x) ^ 2) =
      t ^ 2 * (∫ x in Ioo 0 L, (vX x * a x) ^ 2) +
        (1 - p * t) * (∫ x in Ioo 0 L, (v x * b x) ^ 2) -
        t * (right - left) := by
  have hvSq : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y ↦ v y ^ 2) (2 * v x * vX x) x := by
    intro x hx
    have hsquare : HasDerivAt (v * v) (2 * v x * vX x) x :=
      ((hv x hx).mul (hv x hx)).congr_deriv (by ring)
    exact hsquare.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun y ↦ by simp only [Pi.mul_apply, pow_two]
  have hfirst : IntegrableOn (fun x ↦ (-p * b x ^ 2) * v x ^ 2) (Ioo 0 L) := by
    refine (hB.integrable_sq.const_mul (-p)).congr ?_
    filter_upwards with x
    ring
  have hsecond : IntegrableOn (fun x ↦ w x * (2 * v x * vX x)) (Ioo 0 L) := by
    refine ((hA.integrable_mul hB).const_mul 2).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.mul_apply]
    rw [← hab x hx]
    ring
  have hparts := PDE.Analysis.integral_Ioo_deriv_mul_eq_sub_of_tendsto
    hL hw hvSq hfirst hsecond hleft hright
  have hsum : IntegrableOn
      (fun x ↦ (-p * b x ^ 2) * v x ^ 2 + w x * (2 * v x * vX x)) (Ioo 0 L) :=
    hfirst.add hsecond
  have hscalar (A B V Z : ℝ) :
      (t * (Z * A) - V * B) ^ 2 =
        t ^ 2 * (Z * A) ^ 2 + (1 - p * t) * (V * B) ^ 2 -
          t * ((-p * B ^ 2) * V ^ 2 + (A * B) * (2 * V * Z)) := by
    cas
  calc
    _ = ∫ x in Ioo 0 L,
        t ^ 2 * (vX x * a x) ^ 2 + (1 - p * t) * (v x * b x) ^ 2 -
          t * ((-p * b x ^ 2) * v x ^ 2 + w x * (2 * v x * vX x)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [← hab x hx]
      exact hscalar (a x) (b x) (v x) (vX x)
    _ = _ := by
      rw [integral_sub
        ((hA.integrable_sq.const_mul _).fun_add (hB.integrable_sq.const_mul _))
        (hsum.const_mul _),
        integral_add (hA.integrable_sq.const_mul _) (hB.integrable_sq.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, hparts]

/-- At `t = 1/p`, the bulk term cancels, leaving exactly `-(right-left)/p`. -/
theorem integral_square_completion
    {L p left right : ℝ} {v vX a b w : ℝ → ℝ}
    (hL : 0 < L) (hp : p ≠ 0)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hw : ∀ x ∈ Ioo 0 L, HasDerivAt w (-p * b x ^ 2) x)
    (hab : ∀ x ∈ Ioo 0 L, a x * b x = w x)
    (hA : MemLp (fun x ↦ vX x * a x) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x * b x) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ w x * v x ^ 2) (𝓝[>] 0) (𝓝 left))
    (hright : Tendsto (fun x ↦ w x * v x ^ 2) (𝓝[<] L) (𝓝 right)) :
    (∫ x in Ioo 0 L, (vX x * a x / p - v x * b x) ^ 2) =
      (1 / p ^ 2) * (∫ x in Ioo 0 L, (vX x * a x) ^ 2) -
        (right - left) / p := by
  have h := integral_square_completion_with_bulk (1 / p) hL hv hw hab hA hB hleft hright
  simpa [div_eq_mul_inv, inv_pow, hp, mul_comm] using h

/-- The square completion (4.13) of Chen, Hou and Huang at the origin: if `v' = vX` on `(0, L)`,
`vX/x²` and `v/x³` are in `L²`, `v²/x⁵ → 0` at `0` and `v → vL` at `L`, then
`∫₀^L (vX/(5x²) - v/x³)² = (1/25) ∫₀^L (vX/x²)² - vL²/(5 L⁵)`. -/
theorem integral_origin_square_completion
    {L vL : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / x ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / x ^ 3) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / x ^ 5) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto v (𝓝[<] L) (𝓝 vL)) :
    (∫ x in Ioo 0 L, (vX x / x ^ 2 / 5 - v x / x ^ 3) ^ 2) =
      (1 / 25 : ℝ) * (∫ x in Ioo 0 L, (vX x / x ^ 2) ^ 2) -
        vL ^ 2 / (5 * L ^ 5) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / y ^ 5) (-5 * (1 / x ^ 3) ^ 2) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    cas using hxne
  have hab : ∀ x ∈ Ioo 0 L, (1 / x ^ 2) * (1 / x ^ 3) = (1 : ℝ) / x ^ 5 := by
    intro x hx
    cas
  have hboundary :
      Tendsto (fun x ↦ v x ^ 2 / x ^ 5) (𝓝[<] L) (𝓝 (vL ^ 2 / L ^ 5)) :=
    (hright.pow 2).div
      (((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 L) (𝓝 L)).mono_left inf_le_left).pow 5)
      (pow_ne_zero _ hLne)
  have h := integral_square_completion hL (by norm_num : (5 : ℝ) ≠ 0) hv hw hab
    (by simpa only [div_eq_mul_inv, one_mul] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hleft)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hboundary)
  simp only [one_div, ← div_eq_mul_inv, sub_zero] at h
  have hscale : (vL ^ 2 / L ^ 5) / 5 = vL ^ 2 / (5 * L ^ 5) := by cas
  norm_num only [show (5 : ℝ) ^ 2 = 25 by norm_num] at h
  simpa only [hscale] using h

/-- The square completion (4.14) of Chen, Hou and Huang at `L`: if `v' = vX` on `(0, L)`,
`vX/(x - L)` and `v/(x - L)²` are in `L²`, `v → v₀` at `0` and `v²/(x - L)³ → 0` at `L`, then
`∫₀^L (vX/(3(x - L)) - v/(x - L)²)² = (1/9) ∫₀^L (vX/(x - L))² - v₀²/(3 L³)`. -/
theorem integral_right_square_completion
    {L v₀ : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / (x - L)) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / (x - L) ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto v (𝓝[>] 0) (𝓝 v₀))
    (hright : Tendsto (fun x ↦ v x ^ 2 / (x - L) ^ 3) (𝓝[<] L) (𝓝 0)) :
    (∫ x in Ioo 0 L, (vX x / (x - L) / 3 - v x / (x - L) ^ 2) ^ 2) =
      (1 / 9 : ℝ) * (∫ x in Ioo 0 L, (vX x / (x - L)) ^ 2) -
        v₀ ^ 2 / (3 * L ^ 3) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / (y - L) ^ 3)
        (-3 * (1 / (x - L) ^ 2) ^ 2) x := by
    have hinv (y : ℝ) (hy : y ≠ 0) :
        HasDerivAt (fun z : ℝ ↦ 1 / z ^ 3) (-3 * (1 / y ^ 2) ^ 2) y := by
      cas using hy
    intro x hx
    have hxne : x - L ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx.2)
    simpa only [mul_one, Function.comp_def, id_eq] using
      (hinv (x - L) hxne).comp x ((hasDerivAt_id x).sub_const L)
  have hab : ∀ x ∈ Ioo 0 L,
      (1 / (x - L)) * (1 / (x - L) ^ 2) = (1 : ℝ) / (x - L) ^ 3 := by
    intro x hx
    cas
  have hboundary :
      Tendsto (fun x ↦ v x ^ 2 / (x - L) ^ 3)
        (𝓝[>] 0) (𝓝 (v₀ ^ 2 / (-L) ^ 3)) := by
    have hb := (hleft.pow 2).div
      ((((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0)).mono_left
        inf_le_left).sub_const L).pow 3)
      (pow_ne_zero 3 (sub_ne_zero.mpr (ne_of_lt hL)))
    simp only [zero_sub] at hb
    exact Filter.Tendsto.congr' (.of_forall fun x ↦ by simp only [Pi.div_apply, id_eq]) hb
  have h := integral_square_completion hL (by norm_num : (3 : ℝ) ≠ 0) hv hw hab
    (by simpa only [div_eq_mul_inv, one_mul] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hboundary)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hright)
  simp only [one_div, ← div_eq_mul_inv, zero_sub] at h
  have hscale : -(v₀ ^ 2 / (-L) ^ 3) / 3 = v₀ ^ 2 / (3 * L ^ 3) := by cas
  norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num] at h
  simpa only [hscale] using h

/-- One-endpoint Hardy with constant `4`, derived by square completion.

The pole may be either endpoint (or outside the interval). Both boundary products
are required to vanish. Square-integrability of the quotient is explicit. -/
theorem integral_hardy_le
    {L d : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hd : ∀ x ∈ Ioo 0 L, x - d ≠ 0)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp vX 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / (x - d)) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / (x - d)) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto (fun x ↦ v x ^ 2 / (x - d)) (𝓝[<] L) (𝓝 0)) :
    (∫ x in Ioo 0 L, (v x / (x - d)) ^ 2) ≤
      4 * ∫ x in Ioo 0 L, vX x ^ 2 := by
  have hinv (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt (fun z : ℝ ↦ 1 / z) (-1 * (1 / y) ^ 2) y := by
    cas using hy
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / (y - d)) (-1 * (1 / (x - d)) ^ 2) x := by
    intro x hx
    simpa only [mul_one, Function.comp_def, id_eq] using
      (hinv (x - d) (hd x hx)).comp x ((hasDerivAt_id x).sub_const d)
  have h := integral_square_completion_with_bulk 2 hL hv hw
    (a := fun _ ↦ 1) (fun _ _ ↦ one_mul _)
    (by simpa only [mul_one] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hleft)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hright)
  have hnonneg := integral_nonneg (μ := volume.restrict (Ioo 0 L))
    (fun x ↦ sq_nonneg (2 * (vX x * 1) - v x * (1 / (x - d))))
  rw [h] at hnonneg
  simp only [mul_one, one_mul, one_div, ← div_eq_mul_inv] at hnonneg
  linarith

/-- The square completion behind the constant `4/9`, including the right endpoint. -/
theorem integral_four_ninths_square_completion
    {L vL : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / x) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / x ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / x ^ 3) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto v (𝓝[<] L) (𝓝 vL)) :
    (∫ x in Ioo 0 L, ((2 / 3 : ℝ) * (vX x / x) - v x / x ^ 2) ^ 2) =
      (4 / 9 : ℝ) * (∫ x in Ioo 0 L, vX x ^ 2 / x ^ 2) -
        (∫ x in Ioo 0 L, v x ^ 2 / x ^ 4) - 2 * vL ^ 2 / (3 * L ^ 3) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / y ^ 3) (-3 * (1 / x ^ 2) ^ 2) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    cas using hxne
  have hab : ∀ x ∈ Ioo 0 L, (1 / x) * (1 / x ^ 2) = (1 : ℝ) / x ^ 3 := by
    intro x _
    cas
  have hboundary :
      Tendsto (fun x ↦ v x ^ 2 / x ^ 3) (𝓝[<] L) (𝓝 (vL ^ 2 / L ^ 3)) :=
    (hright.pow 2).div
      (((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 L) (𝓝 L)).mono_left inf_le_left).pow 3)
      (pow_ne_zero _ hLne)
  have h := integral_square_completion_with_bulk (2 / 3) hL hv hw hab
    (by simpa only [div_eq_mul_inv, one_mul] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hleft)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hboundary)
  have hscale : (2 / 3 : ℝ) * (vL ^ 2 / L ^ 3) = 2 * vL ^ 2 / (3 * L ^ 3) := by
    cas
  rw [show (2 / 3 : ℝ) ^ 2 = 4 / 9 by cas,
    show (1 : ℝ) - 3 * (2 / 3) = -1 by cas] at h
  simpa only [one_div, ← div_eq_mul_inv, div_pow, ← pow_mul,
    show 2 * 2 = 4 from rfl, sub_zero, neg_one_mul, ← sub_eq_add_neg, hscale] using h

/-- The weighted Hardy bound with constant `4/9`, with its nonpositive endpoint correction
retained. -/
theorem integral_weighted_hardy_four_ninths
    {L vL : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / x) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / x ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / x ^ 3) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto v (𝓝[<] L) (𝓝 vL)) :
    (∫ x in Ioo 0 L, v x ^ 2 / x ^ 4) ≤
      (4 / 9 : ℝ) * (∫ x in Ioo 0 L, vX x ^ 2 / x ^ 2) -
        2 * vL ^ 2 / (3 * L ^ 3) := by
  have h := integral_four_ninths_square_completion hL hv hA hB hleft hright
  have hnonneg :
      0 ≤ ∫ x in Ioo 0 L, ((2 / 3 : ℝ) * (vX x / x) - v x / x ^ 2) ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  linarith

/-- The damping term of (8.20) in the supplementary material of Chen, Hou and Huang: under the
hypotheses of `integral_weighted_hardy_four_ninths` and `0 ≤ d`,
`0 ≤ (4d/9) ∫₀^L v'²/x² - d ∫₀^L v²/x⁴`. The right trace need not vanish, because its square has a
favorable sign. -/
theorem weighted_hardy_damping_nonneg
    {L vL d : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L) (hd : 0 ≤ d)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / x) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / x ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / x ^ 3) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto v (𝓝[<] L) (𝓝 vL)) :
    0 ≤ (4 * d / 9) * (∫ x in Ioo 0 L, vX x ^ 2 / x ^ 2) -
      d * (∫ x in Ioo 0 L, v x ^ 2 / x ^ 4) := by
  have h := integral_weighted_hardy_four_ninths hL hv hA hB hleft hright
  have hboundary : 0 ≤ 2 * vL ^ 2 / (3 * L ^ 3) := by positivity
  have hweak :
      (∫ x in Ioo 0 L, v x ^ 2 / x ^ 4) ≤
        (4 / 9 : ℝ) * (∫ x in Ioo 0 L, vX x ^ 2 / x ^ 2) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hweak hd
  nlinarith

end

end SobolevSpace.Hardy
