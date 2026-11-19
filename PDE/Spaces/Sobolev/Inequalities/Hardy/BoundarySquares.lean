/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.SingularInterval
import CAS.ExactTactic

/-!
# Singular Hardy bounds with endpoint squares

The constant `4/25` at the origin and the reflected constant `4/9` at `L`, used in (8.17)-(8.19)
of the supplementary material of Chen, Hou and Huang, follow from singular square completion. The
favorable square at the regular endpoint is retained in each estimate.

## Main results

* `integral_weighted_hardy_four_twentyfifths`:
  `∫₀^L (v/x³)² ≤ (4/25) ∫₀^L (v'/x²)² - 2 v(L)²/(5 L⁵)`.
* `integral_weighted_hardy_right_four_ninths`:
  `∫₀^L (v/(x - L)²)² ≤ (4/9) ∫₀^L (v'/(x - L))² - 2 v(0)²/(3 L³)`.

The scalar identities and the derivatives of the weights are discharged by the `cas` tactic of
SymLean, our verified computer algebra system.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  supplementary material (in the same PDF), (8.17)-(8.19).
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace SobolevSpace.Hardy

/-- If `v' = vX` on `(0, L)`, `vX/x²` and `v/x³` are in `L²`, `v²/x⁵ → 0` at `0` and `v → vL`
at `L`, then `∫₀^L (v/x³)² ≤ (4/25) ∫₀^L (vX/x²)² - 2 vL²/(5 L⁵)`. -/
theorem integral_weighted_hardy_four_twentyfifths
    {L vL : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / x ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / x ^ 3) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto (fun x ↦ v x ^ 2 / x ^ 5) (𝓝[>] 0) (𝓝 0))
    (hright : Tendsto v (𝓝[<] L) (𝓝 vL)) :
    (∫ x in Ioo 0 L, (v x / x ^ 3) ^ 2) ≤
      (4 / 25 : ℝ) * (∫ x in Ioo 0 L, (vX x / x ^ 2) ^ 2) -
        2 * vL ^ 2 / (5 * L ^ 5) := by
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / y ^ 5) (-5 * (1 / x ^ 3) ^ 2) x := by
    intro x hx
    have hxne := hx.1.ne'
    cas using hxne
  have hab : ∀ x ∈ Ioo 0 L, (1 / x ^ 2) * (1 / x ^ 3) = (1 : ℝ) / x ^ 5 := by
    intro x _
    cas
  have hb : Tendsto (fun x ↦ v x ^ 2 / x ^ 5) (𝓝[<] L) (𝓝 (vL ^ 2 / L ^ 5)) :=
    (hright.pow 2).div
      (((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 L) (𝓝 L)).mono_left
        inf_le_left).pow 5) (pow_ne_zero _ hL.ne')
  have h := integral_square_completion_with_bulk (2 / 5) hL hv hw hab
    (by simpa only [div_eq_mul_inv, one_mul] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hleft)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hb)
  rw [show (2 / 5 : ℝ) ^ 2 = 4 / 25 by cas,
    show (1 : ℝ) - 5 * (2 / 5) = -1 by cas] at h
  simp only [one_div, ← div_eq_mul_inv, sub_zero, neg_one_mul] at h
  have hn : 0 ≤ ∫ x in Ioo 0 L,
      ((2 / 5 : ℝ) * (vX x / x ^ 2) - v x / x ^ 3) ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hscale : (2 / 5 : ℝ) * (vL ^ 2 / L ^ 5) = 2 * vL ^ 2 / (5 * L ^ 5) := by cas
  rw [hscale] at h
  linarith

/-- If `v' = vX` on `(0, L)`, `vX/(x - L)` and `v/(x - L)²` are in `L²`, `v → v0` at `0` and
`v²/(x - L)³ → 0` at `L`, then
`∫₀^L (v/(x - L)²)² ≤ (4/9) ∫₀^L (vX/(x - L))² - 2 v0²/(3 L³)`. -/
theorem integral_weighted_hardy_right_four_ninths
    {L v0 : ℝ} {v vX : ℝ → ℝ}
    (hL : 0 < L)
    (hv : ∀ x ∈ Ioo 0 L, HasDerivAt v (vX x) x)
    (hA : MemLp (fun x ↦ vX x / (x - L)) 2 (volume.restrict (Ioo 0 L)))
    (hB : MemLp (fun x ↦ v x / (x - L) ^ 2) 2 (volume.restrict (Ioo 0 L)))
    (hleft : Tendsto v (𝓝[>] 0) (𝓝 v0))
    (hright : Tendsto (fun x ↦ v x ^ 2 / (x - L) ^ 3) (𝓝[<] L) (𝓝 0)) :
    (∫ x in Ioo 0 L, (v x / (x - L) ^ 2) ^ 2) ≤
      (4 / 9 : ℝ) * (∫ x in Ioo 0 L, (vX x / (x - L)) ^ 2) -
        2 * v0 ^ 2 / (3 * L ^ 3) := by
  have hw : ∀ x ∈ Ioo 0 L,
      HasDerivAt (fun y : ℝ ↦ 1 / (y - L) ^ 3)
        (-3 * (1 / (x - L) ^ 2) ^ 2) x := by
    have hinv (y : ℝ) (hy : y ≠ 0) :
        HasDerivAt (fun z : ℝ ↦ 1 / z ^ 3) (-3 * (1 / y ^ 2) ^ 2) y := by
      cas using hy
    intro x hx
    simpa only [mul_one, Function.comp_def, id_eq] using
      (hinv (x - L) (sub_ne_zero.mpr hx.2.ne)).comp x ((hasDerivAt_id x).sub_const L)
  have hab : ∀ x ∈ Ioo 0 L,
      (1 / (x - L)) * (1 / (x - L) ^ 2) = (1 : ℝ) / (x - L) ^ 3 := by
    intro x _
    cas
  have hb : Tendsto (fun x ↦ v x ^ 2 / (x - L) ^ 3) (𝓝[>] 0)
      (𝓝 (v0 ^ 2 / (0 - L) ^ 3)) :=
    (hleft.pow 2).div
      ((((tendsto_id : Tendsto (fun x : ℝ ↦ x) (𝓝 0) (𝓝 0)).mono_left
        inf_le_left).sub_const L).pow 3)
      (pow_ne_zero _ (sub_ne_zero.mpr hL.ne))
  have h := integral_square_completion_with_bulk (2 / 3) hL hv hw hab
    (by simpa only [div_eq_mul_inv, one_mul] using hA)
    (by simpa only [div_eq_mul_inv, one_mul] using hB)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hb)
    (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hright)
  rw [show (2 / 3 : ℝ) ^ 2 = 4 / 9 by cas,
    show (1 : ℝ) - 3 * (2 / 3) = -1 by cas] at h
  simp only [one_div, ← div_eq_mul_inv, zero_sub, neg_one_mul] at h
  have hn : 0 ≤ ∫ x in Ioo 0 L,
      ((2 / 3 : ℝ) * (vX x / (x - L)) - v x / (x - L) ^ 2) ^ 2 :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hscale : (2 / 3 : ℝ) * -(v0 ^ 2 / (-L) ^ 3) =
      2 * v0 ^ 2 / (3 * L ^ 3) := by cas
  rw [hscale] at h
  linarith

end SobolevSpace.Hardy
