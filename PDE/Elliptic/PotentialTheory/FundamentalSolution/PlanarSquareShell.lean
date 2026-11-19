/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarRectangleIntegrals
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The strain kernel with a power weight on a square shell

Chen and Hou II, Supplementary material II, Section 7.1.1, bound the far-field error of `L₁₂` by
the integral of `4 y₁ y₂ / |y|^{4+α}` (with `α = a_n` the far-field power of the weight) over the
square shell `[0,d]² \ [0,c]²`:

`J(c, d) = C_α |d^{-α} - c^{-α}|`,  `C_α = 8 (1 - 2^{-(2+α)/2}) / ((2 + α) |α|)`

for `0 < c ≤ d`, `α > -2`, `α ≠ 0`. The shell is the union of the rectangles `[c, d] × [0, d]`
and `[0, c] × [c, d]`, which meet on a segment; on each the kernel is the mixed derivative of
`4 (y₁² + y₂²)^{-α/2} / (α (α + 2))`, so the integrals are corner sums.

## Main definitions

* `shellKernel`: the kernel `4 y₁ y₂ / |y|^{4+α}`.
* `shellConstant`: `C_α = 8 (1 - 2^{-(2+α)/2}) / ((2 + α) |α|)`.

## Main results

* `integral_shellKernel_add`: for `0 < c ≤ d`, `α > -2` and `α ≠ 0`, the integrals of
  `shellKernel α` over `[c,d] × [0,d]` and `[0,c] × [c,d]` add up to `C_α |d^{-α} - c^{-α}|`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Section 7.1.1.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Interval

namespace PotentialTheory.Planar

/-- The kernel `4 y₁ y₂ / |y|^{4+α}` of Supp. 7.1. -/
def shellKernel (α : ℝ) (y : ℝ^2) : ℝ := 4 * y 0 * y 1 * (‖y‖ ^ 2) ^ (-(4 + α) / 2)

/-- `C_α = 8 (1 - 2^{-(2+α)/2}) / ((2 + α) |α|)`. -/
def shellConstant (α : ℝ) : ℝ := 8 * (1 - 2 ^ (-(2 + α) / 2)) / ((2 + α) * |α|)

/-- The kernel at the point `(p, q)` is `4 p q (p² + q²)^{-(4+α)/2}`. -/
private theorem shellKernel_toLp (α p q : ℝ) :
    shellKernel α !₂[p, q] = 4 * p * q * (p ^ 2 + q ^ 2) ^ (-(4 + α) / 2) := by
  simp [shellKernel, norm_sq_vec]

/-- The corner function `4 (u² + v²)^{-α/2} / (α (α + 2))`. -/
private def shellCorner (α u v : ℝ) : ℝ := 4 / (α * (α + 2)) * (u ^ 2 + v ^ 2) ^ (-α / 2)

/-- Its `u`-derivative `-4 u (u² + v²)^{-(α+2)/2} / (α + 2)`. -/
private def shellEdge (α u v : ℝ) : ℝ := -(4 / (α + 2)) * u * (u ^ 2 + v ^ 2) ^ (-(α + 2) / 2)

/-- For `α ≠ 0, -2` and `u² + v² ≠ 0`, the `u`-derivative of the corner function is
`shellEdge α u v`. -/
private theorem hasDerivAt_shellCorner {α u v : ℝ} (hα : α ≠ 0) (hα2 : α + 2 ≠ 0)
    (h : u ^ 2 + v ^ 2 ≠ 0) :
    HasDerivAt (fun u ↦ shellCorner α u v) (shellEdge α u v) u := by
  have h1 : HasDerivAt (fun u ↦ u ^ 2 + v ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (v ^ 2)
  have h2 := (h1.rpow_const (p := -α / 2) (Or.inl h)).const_mul (4 / (α * (α + 2)))
  refine h2.congr_deriv ?_
  simp only [shellEdge]
  rw [show -α / 2 - 1 = -(α + 2) / 2 by ring]
  field_simp

/-- For `α ≠ -2` and `u² + v² ≠ 0`, the `v`-derivative of `shellEdge α u v` is the kernel
`4 u v (u² + v²)^{-(4+α)/2}`. -/
private theorem hasDerivAt_shellEdge {α u v : ℝ} (hα2 : α + 2 ≠ 0) (h : u ^ 2 + v ^ 2 ≠ 0) :
    HasDerivAt (fun v ↦ shellEdge α u v) (4 * u * v * (u ^ 2 + v ^ 2) ^ (-(4 + α) / 2)) v := by
  have h1 : HasDerivAt (fun v ↦ u ^ 2 + v ^ 2) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).const_add (u ^ 2)
  have h2 := (h1.rpow_const (p := -(α + 2) / 2) (Or.inl h)).const_mul (-(4 / (α + 2)) * u)
  refine h2.congr_deriv ?_
  rw [show -(α + 2) / 2 - 1 = -(4 + α) / 2 by ring]
  field_simp

/-- The kernel is continuous on a product set `{y₁ ∈ s, y₂ ∈ t}` avoiding the pole. -/
private theorem continuous_shell {α : ℝ} {s t : Set ℝ} (h : ∀ p ∈ s, ∀ q ∈ t, p ^ 2 + q ^ 2 ≠ 0) :
    ContinuousOn (fun y : ℝ^2 ↦ shellKernel α y) {y | y 0 ∈ s ∧ y 1 ∈ t} := by
  intro y hy
  have hn : ‖y‖ ^ 2 ≠ 0 := by rw [EuclideanSpace.norm_sq_fin_two]; exact h _ hy.1 _ hy.2
  refine ContinuousAt.continuousWithinAt ?_
  unfold shellKernel
  exact (((continuous_const.mul (by fun_prop)).mul (by fun_prop)).continuousAt).mul
    ((continuous_norm.pow 2).continuousAt.rpow_const (Or.inl hn))

/-- The slice `y ↦ 4 x y (x² + y²)^{-(4+α)/2}` is continuous on `[c, d]` when it avoids the pole. -/
private theorem continuousOn_kernel_slice {α x c d : ℝ}
    (h : ∀ y ∈ Icc c d, x ^ 2 + y ^ 2 ≠ 0) :
    ContinuousOn (fun y ↦ 4 * x * y * (x ^ 2 + y ^ 2) ^ (-(4 + α) / 2)) (Icc c d) := fun y hy ↦
  (((continuous_const.mul continuous_id).continuousAt).mul
    (((continuous_const.add (continuous_pow 2)).continuousAt).rpow_const
      (Or.inl (h y hy)))).continuousWithinAt

/-- The slice `x ↦ shellEdge α x v` is continuous on `[a, b]` when it avoids the pole. -/
private theorem continuousOn_shellEdge {α a b v : ℝ} (h : ∀ x ∈ Icc a b, x ^ 2 + v ^ 2 ≠ 0) :
    ContinuousOn (fun x ↦ shellEdge α x v) (Icc a b) := fun x hx ↦
  (((continuous_const.mul continuous_id).continuousAt).mul
    ((((continuous_pow 2).add continuous_const).continuousAt).rpow_const
      (Or.inl (h x hx)))).continuousWithinAt

/-- The corner sums of one rectangle avoiding the pole. -/
private theorem integral_rectangle_shellKernel {α a b c d : ℝ} (hα : α ≠ 0) (hα2 : α + 2 ≠ 0)
    (hab : a ≤ b) (hcd : c ≤ d) (h : ∀ p ∈ Icc a b, ∀ q ∈ Icc c d, p ^ 2 + q ^ 2 ≠ 0) :
    ∫ y in coordinateRectangle a b c d, shellKernel α y = cornerSum (shellCorner α) a b c d := by
  rw [setIntegral_coordinateRectangle hab hcd (continuous_shell h)]
  simp only [shellKernel_toLp]
  refine integral_integral_eq_cornerSum (k₁ := shellEdge α) (fun x hx y hy ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_ ?_
  · rw [uIcc_of_le hab] at hx; rw [uIcc_of_le hcd] at hy
    exact hasDerivAt_shellEdge hα2 (h x hx y hy)
  · rw [uIcc_of_le hab] at hx
    exact (continuousOn_kernel_slice fun y hy ↦ h x hx y hy).intervalIntegrable_of_Icc hcd
  · rw [uIcc_of_le hab] at hx
    exact hasDerivAt_shellCorner hα hα2 (h x hx c ⟨le_rfl, hcd⟩)
  · rw [uIcc_of_le hab] at hx
    exact hasDerivAt_shellCorner hα hα2 (h x hx d ⟨hcd, le_rfl⟩)
  · exact (continuousOn_shellEdge fun x hx ↦ h x hx c ⟨le_rfl, hcd⟩).intervalIntegrable_of_Icc hab
  · exact (continuousOn_shellEdge fun x hx ↦ h x hx d ⟨hcd, le_rfl⟩).intervalIntegrable_of_Icc hab

/-- **The square shell of Supp. 7.1.1**: for `0 < c ≤ d`, `α > -2` and `α ≠ 0`,
`∫_{[c,d] × [0,d]} 4y₁y₂/|y|^{4+α} + ∫_{[0,c] × [c,d]} 4y₁y₂/|y|^{4+α} = C_α |d^{-α} - c^{-α}|`. -/
theorem integral_shellKernel_add {α c d : ℝ} (hα : -2 < α) (hα0 : α ≠ 0) (hc : 0 < c)
    (hcd : c ≤ d) :
    (∫ y in coordinateRectangle c d 0 d, shellKernel α y) +
        ∫ y in coordinateRectangle 0 c c d, shellKernel α y =
      shellConstant α * |d ^ (-α) - c ^ (-α)| := by
  have hα2 : α + 2 ≠ 0 := by linarith
  have hd : 0 < d := hc.trans_le hcd
  rw [integral_rectangle_shellKernel hα0 hα2 hcd hd.le (fun p hp q _ ↦ by
      have : 0 < p := hc.trans_le hp.1; positivity),
    integral_rectangle_shellKernel hα0 hα2 hc.le hcd (fun p _ q hq ↦ by
      have : 0 < q := hc.trans_le hq.1; positivity)]
  simp only [cornerSum, shellCorner]
  -- the corner values
  have hpow : ∀ x : ℝ, 0 < x → (x ^ 2 + 0 ^ 2) ^ (-α / 2) = x ^ (-α) := fun x hx ↦ by
    rw [zero_pow two_ne_zero, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; ring_nf
  have hpow0 : ∀ x : ℝ, 0 < x → ((0 : ℝ) ^ 2 + x ^ 2) ^ (-α / 2) = x ^ (-α) := fun x hx ↦ by
    rw [zero_pow two_ne_zero, zero_add, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; ring_nf
  have hdiag : ∀ x : ℝ, 0 < x → (x ^ 2 + x ^ 2) ^ (-α / 2) = 2 ^ (-α / 2) * x ^ (-α) := by
    intro x hx
    rw [show x ^ 2 + x ^ 2 = 2 * x ^ 2 by ring, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    ring_nf
  rw [hpow d hd, hpow c hc, hpow0 d hd, hpow0 c hc, hdiag d hd, hdiag c hc]
  have h2 : (2 : ℝ) ^ (-(2 + α) / 2) = 2 ^ (-α / 2) / 2 := by
    rw [show -(2 + α) / 2 = -α / 2 - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
  rw [shellConstant, h2]
  have hα2' : 2 + α ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hα0 with hneg | hpos
  · -- `α < 0`: `d^{-α} ≥ c^{-α}`
    have hmono : c ^ (-α) ≤ d ^ (-α) := Real.rpow_le_rpow hc.le hcd (by linarith)
    rw [abs_of_nonneg (show 0 ≤ d ^ (-α) - c ^ (-α) by linarith), abs_of_neg hneg]
    field_simp
    ring
  · have hmono : d ^ (-α) ≤ c ^ (-α) := Real.rpow_le_rpow_of_nonpos hc hcd (by linarith)
    rw [abs_of_nonpos (show d ^ (-α) - c ^ (-α) ≤ 0 by linarith), abs_of_pos hpos]
    field_simp
    ring

end PotentialTheory.Planar
