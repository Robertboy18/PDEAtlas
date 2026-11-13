/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarKernelOneHalfPower
public import PDE.Analysis.Integration.Rectangle.Tonelli

/-!
# Moments of the strain kernel on a square

The commutator terms of Chen and Hou II, Section 4.2.1 (`I₃₁`) and Supplementary material II,
Section 7.1.2 (`III₁`), need `∫_{[-a,a]²} |K₁(s) s₁^i s₂^j| ds = 4 ∫_{[0,a]²} K₁(s) s₁^i s₂^j ds`
for `K₁ = s₁ s₂/|s|⁴ = hessianKernel 0 1` and `1 ≤ i + j ≤ 2`; on the first quadrant `K₁ ≥ 0`.
With the `(i + j)`-homogeneity these are `a^{i+j}` times the moments on `[0,1]²`.

They are stated as set integrals over the closed square (the integrands are bounded there but not
continuous at the corner), through the Tonelli lemma for nonnegative integrands.

## Main results

* `integral_square_hessianKernel_zero_one_mul_fst`: `∫_{[0,a]²} K₁ s₁ = a π/8` (also for `s₂`, by
  the symmetry of `K₁`).
* `integral_square_hessianKernel_zero_one_mul_fst_sq`: `∫_{[0,a]²} K₁ s₁² = a² log 2/4` (and
  `s₂²`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.2.1, and
  Supplementary material II, Section 7.1.2.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Interval

namespace PotentialTheory.Planar

/-- The common Tonelli step for `K₁(s) g(s₁)` on `[0, a]²` with `g ≥ 0` continuous. -/
private theorem setIntegral_square_mul_fst {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u)
    (hout : IntervalIntegrable (fun u ↦ (1 / (2 * u) - u / (2 * (u ^ 2 + a ^ 2))) * g u)
      volume 0 a) :
    ∫ y in coordinateRectangle 0 a 0 a, hessianKernel 0 1 y * g (y 0) =
      ∫ u in (0 : ℝ)..a, (1 / (2 * u) - u / (2 * (u ^ 2 + a ^ 2))) * g u := by
  have hinner : ∀ p, ∫ q in (0 : ℝ)..a, hessianKernel 0 1 !₂[p, q] * g ((!₂[p, q] : ℝ^2) 0) =
      (1 / (2 * p) - p / (2 * (p ^ 2 + a ^ 2))) * g p := fun p ↦ by
    have e : (fun q ↦ hessianKernel 0 1 !₂[p, q] * g ((!₂[p, q] : ℝ^2) 0)) =
        fun q ↦ hessianKernel 0 1 !₂[p, q] * g p := rfl
    rw [e, intervalIntegral.integral_mul_const, integral_hessianKernel_zero_one_right_zero ha]
  have hmeas : Measurable fun y : ℝ^2 ↦ hessianKernel 0 1 y * g (y 0) :=
    (measurable_hessianKernel 0 1).mul (hg.measurable.comp
      (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable)
  have hnn : ∀ y ∈ coordinateRectangle 0 a 0 a, 0 ≤ hessianKernel 0 1 y * g (y 0) := by
    intro y hy
    have hK : 0 ≤ hessianKernel 0 1 y := by
      rw [hessianKernel_zero_one]
      exact div_nonneg (mul_nonneg hy.1.1 hy.2.1) (by positivity)
    exact mul_nonneg hK (hg0 _ hy.1.1)
  have hin : ∀ p ∈ Ioo 0 a, IntervalIntegrable
      (fun q ↦ hessianKernel 0 1 !₂[p, q] * g ((!₂[p, q] : ℝ^2) 0)) volume 0 a := by
    intro p hp
    have e : (fun q ↦ hessianKernel 0 1 !₂[p, q] * g ((!₂[p, q] : ℝ^2) 0)) =
        fun q ↦ hessianKernel 0 1 !₂[p, q] * g p := rfl
    rw [e]
    exact ((continuous_hessianKernel_zero_one_slice hp.1.ne').mul
        continuous_const).intervalIntegrable _ _
  rw [setIntegral_coordinateRectangle_of_nonneg ha.le ha.le hmeas hnn hin
    (by simp_rw [hinner]; exact hout)]
  simp_rw [hinner]

/-- Two functions that agree on `(0, ∞)` have the same integral over `[0, a]`. -/
private theorem integral_congr_pos {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℝ}
    (h : ∀ u, 0 < u → f u = g u) : ∫ u in (0 : ℝ)..a, f u = ∫ u in (0 : ℝ)..a, g u := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu ↦ ?_)
  rw [uIoc_of_le ha] at hu
  exact h u hu.1

/-- A function that agrees on `(0, ∞)` with a function integrable on `[0, a]` is integrable on
`[0, a]`. -/
private theorem intervalIntegrable_congr_pos {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℝ}
    (h : ∀ u, 0 < u → f u = g u) (hg : IntervalIntegrable g volume 0 a) :
    IntervalIntegrable f volume 0 a := by
  refine hg.congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun u hu ↦ ?_
  rw [uIoc_of_le ha] at hu
  exact (h u hu.1).symm

/-- **`∫_{[0,a]²} K₁(s) s₁ ds = a π / 8`**. -/
theorem integral_square_hessianKernel_zero_one_mul_fst {a : ℝ} (ha : 0 < a) :
    ∫ y in coordinateRectangle 0 a 0 a, hessianKernel 0 1 y * y 0 = a * Real.pi / 8 := by
  have hpt : ∀ u, 0 < u → (1 / (2 * u) - u / (2 * (u ^ 2 + a ^ 2))) * u =
      a ^ 2 / (2 * (u ^ 2 + a ^ 2)) := by
    intro u hu
    have : u ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hcont : Continuous fun u : ℝ ↦ a ^ 2 / (2 * (u ^ 2 + a ^ 2)) :=
    continuous_const.div (by fun_prop) fun u ↦ by positivity
  have h := setIntegral_square_mul_fst ha continuous_id (fun u hu ↦ hu)
    (intervalIntegrable_congr_pos ha.le hpt (hcont.intervalIntegrable _ _))
  simp only [id] at h
  rw [h, integral_congr_pos ha.le hpt]
  have hd : ∀ u, HasDerivAt (fun u ↦ a / 2 * Real.arctan (u / a))
      (a ^ 2 / (2 * (u ^ 2 + a ^ 2))) u := fun u ↦ by
    have := ((Real.hasDerivAt_arctan (u / a)).comp u ((hasDerivAt_id' u).div_const a)).const_mul
      (a / 2)
    refine this.congr_deriv ?_
    have : u ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
    (hcont.intervalIntegrable _ _), div_self ha.ne', Real.arctan_one, zero_div, Real.arctan_zero]
  ring

/-- **`∫_{[0,a]²} K₁(s) s₁² ds = a² log 2 / 4`**. -/
theorem integral_square_hessianKernel_zero_one_mul_fst_sq {a : ℝ} (ha : 0 < a) :
    ∫ y in coordinateRectangle 0 a 0 a, hessianKernel 0 1 y * y 0 ^ 2 =
      a ^ 2 * Real.log 2 / 4 := by
  have hpt : ∀ u, 0 < u → (1 / (2 * u) - u / (2 * (u ^ 2 + a ^ 2))) * u ^ 2 =
      a ^ 2 * u / (2 * (u ^ 2 + a ^ 2)) := by
    intro u hu
    have : u ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hcont : Continuous fun u : ℝ ↦ a ^ 2 * u / (2 * (u ^ 2 + a ^ 2)) :=
    (continuous_const.mul continuous_id).div (by fun_prop) fun u ↦ by positivity
  rw [setIntegral_square_mul_fst ha (continuous_pow 2) (fun u _ ↦ sq_nonneg u)
    (intervalIntegrable_congr_pos ha.le hpt (hcont.intervalIntegrable _ _)),
    integral_congr_pos ha.le hpt]
  have hd : ∀ u, HasDerivAt (fun u ↦ a ^ 2 / 4 * Real.log (u ^ 2 + a ^ 2))
      (a ^ 2 * u / (2 * (u ^ 2 + a ^ 2))) u := fun u ↦ by
    have h1 : HasDerivAt (fun u ↦ u ^ 2 + a ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow 2 u).add_const (a ^ 2)
    refine ((h1.log (by positivity)).const_mul (a ^ 2 / 4)).congr_deriv ?_
    have : u ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
    (hcont.intervalIntegrable _ _)]
  rw [show a ^ 2 + a ^ 2 = 2 * a ^ 2 by ring, Real.log_mul (by norm_num) (by positivity)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  ring

end PotentialTheory.Planar
