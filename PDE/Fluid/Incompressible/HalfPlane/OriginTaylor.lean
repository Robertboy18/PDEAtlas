/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.OriginStrain
import PDE.Analysis.Calculus.EvenTaylor
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds

/-!
# Cubic vanishing of the corrected velocity at the origin

Let `ω` be continuous, compactly supported, odd in the tangential coordinate and cubically
small at the origin, `|ω(y)| ≤ M |y|³`. With
`c = -(4/π) ∫_{ℝ²₊₊} y₀ y₁ / |y|⁴ ω(y) dy`, which is `u_x(0)` by Part I (5.67) when `ω` is
`C²`, the corrected velocity of Chen and Hou, Part I, (4.8),

`ũ = u - c x₀`, `ṽ = v + c x₁`,

is `O(|x|³)` at the origin. The bound is explicit:
`|ũ(x)|, |ṽ(x)| ≤ (32/π)(2π M + ‖W‖₁) |x|³ + 28 M |x|⁴`.

## Main definitions

* `evenOddKernel`: a kernel against a density even in `y₀` and odd in `y₁`, folded onto the
  quadrant.

## Main results

* `norm_sub_neg_sub_two_mul_le`: the odd third-order Taylor bound
  `‖F(w) - F(-w) - 2 w F'(0)‖ ≤ |w|³ M / 3` when `‖F'''‖ ≤ M` on the segment.
* `abs_symmetrizedKernel_gradientKernel_one_sub_le`: for `2|x| ≤ |y|`,
  `|g₁ₛ(x, y) - (4/π) x₀ K₁(y)| ≤ (32/π) |x|³/|y|⁴`; the kernel of `v` satisfies the same bound
  with `x₁` (`abs_symmetrizedKernel_gradientKernel_zero_sub_le`).
* `abs_integral_gradientKernel_sub_le`: the cubic estimate of the corrected Biot–Savart integral
  of an odd density with `|W(y)| ≤ M |y|³`.
* `abs_halfPlaneVelocity_zero_sub_le`: `|ũ(x)| ≤ (32/π)(2π M + ‖W‖₁) |x|³ + 28 M |x|⁴`; the bound
  of `ṽ` is `abs_halfPlaneVelocity_one_add_le`.
* `halfPlaneVelocity_zero_sub_isBigO`: `ũ = O(|x|³)` at the origin.
* `halfPlaneVelocity_one_add_isBigO`: `ṽ = O(|x|³)` at the origin.
* `halfPlaneVelocity_sub_strain_isBigO`: Part I, after (4.8), for compactly supported `C²` vorticity
  `u - u_x(0) x₀ = O(|x|³)` and `v + u_x(0) x₁ = O(|x|³)`.

## How it works

We split the Biot–Savart integral at `|y| = 2|x|` (`abs_integral_gradientKernel_sub_le`). Far from
the origin the four reflected gradient kernels are folded onto the quadrant; in complex notation
`2π(g₀ - i g₁)(z) = -1/z` (`gradientKernel_one_eq_im`, `gradientKernel_zero_eq_neg_re`), and with
`f(w) = 1/(w - y)` the symmetrized kernels are imaginary and real parts of
`f(x) - f(-x) ± (f(x̄) - f(-x̄))` (`symmetrizedKernel_gradientKernel_one_eq`,
`symmetrizedKernel_gradientKernel_zero_eq`). The odd Taylor bound `norm_sub_neg_sub_two_mul_le`
gives the linear part `(4/π) xₖ K₁(y)` and the cubic remainder `≤ (32/π) |x|³/|y|⁴`
(`abs_symmetrizedKernel_gradientKernel_one_sub_le`). Near the origin the cubic smallness of `ω`
controls the integrable singularity `|x - y|⁻¹` directly, through its integral over a disc
(`integral_ball_norm_sub_inv`). Folding the strain integral onto the quadrant turns the linear part
into `c x₀` and `-c x₁`, and for `C²` vorticity `c = u_x(0)` by `cOmega_eq`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2, (4.8) and the display
  after it, pp. 39-40, and Section 5.6, (5.67), p. 78.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Complex
open GreenFunction PotentialTheory.Planar SobolevSpace
open scoped ComplexConjugate

namespace IncompressibleFlow

/-- **Even second-order Taylor bound** along a segment: if `‖F''‖ ≤ M` on `{t w : |t| ≤ 1}`,
then `‖F(w) + F(-w) - 2 F(0)‖ ≤ |w|² M`. -/
theorem norm_add_neg_sub_two_mul_le {F F₁ F₂ : ℂ → ℂ} {w : ℂ} {M : ℝ}
    (hF : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt F (F₁ (t * w)) (t * w))
    (hF₁ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt F₁ (F₂ (t * w)) (t * w))
    (hM : ∀ t ∈ Icc (-1 : ℝ) 1, ‖F₂ (t * w)‖ ≤ M) :
    ‖F w + F (-w) - 2 * F 0‖ ≤ ‖w‖ ^ 2 * M := by
  have hline (G G' : ℂ → ℂ) (hG : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt G (G' (t * w)) (t * w)) :
      ∀ r ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun r : ℝ ↦ G (r * w)) (G' (r * w) * w) r := by
    intro r hr
    have h := PDE.Analysis.hasDerivAt_comp_affineLine (G := G) (G' := G') 0 w (t := r)
      (by simpa using hG r hr)
    simpa using h
  have h := PDE.Analysis.Calculus.norm_add_neg_sub_two_smul_le (E := ℂ) (x := 1)
    (M := ‖w‖ ^ 2 * M) zero_le_one (f := fun r : ℝ ↦ F (r * w))
    (f₁ := fun r : ℝ ↦ F₁ (r * w) * w) (f₂ := fun r : ℝ ↦ F₂ (r * w) * w * w)
    (by simpa using hline F F₁ hF)
    (fun r hr ↦ by simpa using (hline F₁ F₂ hF₁ r (by simpa using hr)).mul_const w)
    (fun r hr ↦ by
      have hr' : r ∈ Icc (-1 : ℝ) 1 := by simpa using hr
      rw [norm_mul, norm_mul, mul_assoc, ← sq, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM r hr') (by positivity))
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul, ofReal_zero, zero_mul, two_smul,
    one_pow] at h
  rw [two_mul]
  exact h

/-- **Odd third-order Taylor bound** along a segment: if `‖F'''‖ ≤ M` on `{t w : |t| ≤ 1}`, then
`‖F(w) - F(-w) - 2 w F'(0)‖ ≤ |w|³ M / 3`. -/
theorem norm_sub_neg_sub_two_mul_le {F F₁ F₂ F₃ : ℂ → ℂ} {w : ℂ} {M : ℝ}
    (hF : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt F (F₁ (t * w)) (t * w))
    (hF₁ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt F₁ (F₂ (t * w)) (t * w))
    (hF₂ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt F₂ (F₃ (t * w)) (t * w))
    (hM : ∀ t ∈ Icc (-1 : ℝ) 1, ‖F₃ (t * w)‖ ≤ M) :
    ‖F w - F (-w) - 2 * w * F₁ 0‖ ≤ ‖w‖ ^ 3 / 3 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
  -- the even second-order bound for `F₁` along the shorter segment `[-s w, s w]`
  have heven : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖F₁ (s * w) + F₁ (-(s * w)) - 2 * F₁ 0‖ ≤ (s * ‖w‖) ^ 2 * M := by
    intro s hs
    have hmem {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) : r * s ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith [hr.1, hr.2, hs.1, hs.2]
    have h := norm_add_neg_sub_two_mul_le (F := F₁) (F₁ := F₂) (F₂ := F₃) (w := s * w) (M := M)
      (fun t ht ↦ by simpa [mul_assoc] using hF₁ (t * s) (hmem ht))
      (fun t ht ↦ by simpa [mul_assoc] using hF₂ (t * s) (hmem ht))
      (fun t ht ↦ by simpa [mul_assoc] using hM (t * s) (hmem ht))
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at h
  -- integrate the odd part
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ ↦ F (t * w) - F (-(t * w)) - 2 * (t * w) * F₁ 0)
      (w * (F₁ (t * w) + F₁ (-(t * w)) - 2 * F₁ 0)) t := by
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have htn : -t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 := PDE.Analysis.hasDerivAt_comp_affineLine (G := F) (G' := F₁) 0 w (t := t)
      (by simpa using hF t ht')
    have h2 := PDE.Analysis.hasDerivAt_comp_affineLine (G := F) (G' := F₁) 0 (-w) (t := t)
      (by simpa using hF (-t) htn)
    have h3 : HasDerivAt (fun t : ℝ ↦ 2 * ((t : ℂ) * w) * F₁ 0) (2 * w * F₁ 0) t := by
      have := (((hasDerivAt_id (t : ℂ)).mul_const w).const_mul 2).mul_const (F₁ 0)
      simpa using this.comp_ofReal
    have h := (h1.sub h2).sub h3
    simp only [zero_add, mul_neg] at h
    exact h.congr_deriv (by ring)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖w * (F₁ (t * w) + F₁ (-(t * w)) - 2 * F₁ 0)‖ ≤ ‖w‖ ^ 3 * M * t ^ 2 := by
    intro t ht
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heven t ht) (norm_nonneg _)).trans_eq (by ring)
  have h := PDE.Analysis.Calculus.norm_le_of_norm_deriv_le_pow
    (g := fun t : ℝ ↦ F (t * w) - F (-(t * w)) - 2 * (t * w) * F₁ 0) (c := ‖w‖ ^ 3 * M) 2
    zero_le_one (by simp) hderiv hbound
  simp only [ofReal_one, one_mul] at h
  exact h.trans_eq (by push_cast; ring)

section VelocityKernel

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)
local notation "𝐑" => PDE.Common.coordinateReflection

/-- `|𝔠 z|² = |z|²`. -/
private theorem normSq_cx (z : ℝ^2) : Complex.normSq (𝔠 z) = ‖z‖ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map]

/-- `g₁(z) = (2π)⁻¹ Im(1/w)` with `w = z₀ + i z₁`. -/
theorem gradientKernel_one_eq_im (z : ℝ^2) :
    gradientKernel 1 z = 1 / (2 * Real.pi) * (1 / 𝔠 z).im := by
  rw [gradientKernel_eq_div, one_div (𝔠 z), inv_im, normSq_cx, orthonormalBasisOneI_repr_symm_im]
  ring

/-- `g₀(z) = -(2π)⁻¹ Re(1/w)` with `w = z₀ + i z₁`. -/
theorem gradientKernel_zero_eq_neg_re (z : ℝ^2) :
    gradientKernel 0 z = -(1 / (2 * Real.pi)) * (1 / 𝔠 z).re := by
  rw [gradientKernel_eq_div, one_div (𝔠 z), inv_re, normSq_cx, orthonormalBasisOneI_repr_symm_re]
  ring

/-- `1 / conj u = conj (1 / u)`. -/
private theorem inv_conj (u : ℂ) : 1 / conj u = conj (1 / u) := by
  simp only [one_div, map_inv₀]

/-- The complex form of the symmetrized kernel `g₁ₛ`, with `f(w) = 1/(w - Y)`. -/
theorem symmetrizedKernel_gradientKernel_one_eq (x y : ℝ^2) :
    symmetrizedKernel (gradientKernel 1) x y = 1 / (2 * Real.pi) *
      (1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) + 1 / (conj (𝔠 x) - 𝔠 y) -
        1 / (-conj (𝔠 x) - 𝔠 y)).im := by
  unfold symmetrizedKernel
  simp only [gradientKernel_one_eq_im, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e2 : 1 / (𝔠 x - -conj (𝔠 y)) = -conj (1 / (-conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, map_neg, Complex.conj_conj,
      show -𝔠 x - conj (𝔠 y) = -(𝔠 x - -conj (𝔠 y)) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  have e3 : 1 / (𝔠 x - conj (𝔠 y)) = conj (1 / (conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, Complex.conj_conj]
  have e4 : 1 / (𝔠 x + 𝔠 y) = -(1 / (-𝔠 x - 𝔠 y)) := by
    rw [show -𝔠 x - 𝔠 y = -(𝔠 x + 𝔠 y) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  rw [e2, e3, e4]
  simp only [sub_im, add_im, neg_im, conj_im]
  ring

/-- The complex form of the symmetrized kernel `g₀ₛ`. -/
theorem symmetrizedKernel_gradientKernel_zero_eq (x y : ℝ^2) :
    symmetrizedKernel (gradientKernel 0) x y = -(1 / (2 * Real.pi)) *
      (1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) - (1 / (conj (𝔠 x) - 𝔠 y) -
        1 / (-conj (𝔠 x) - 𝔠 y))).re := by
  unfold symmetrizedKernel
  simp only [gradientKernel_zero_eq_neg_re, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e2 : 1 / (𝔠 x - -conj (𝔠 y)) = -conj (1 / (-conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, map_neg, Complex.conj_conj,
      show -𝔠 x - conj (𝔠 y) = -(𝔠 x - -conj (𝔠 y)) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  have e3 : 1 / (𝔠 x - conj (𝔠 y)) = conj (1 / (conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, Complex.conj_conj]
  have e4 : 1 / (𝔠 x + 𝔠 y) = -(1 / (-𝔠 x - 𝔠 y)) := by
    rw [show -𝔠 x - 𝔠 y = -(𝔠 x + 𝔠 y) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  rw [e2, e3, e4]
  simp only [sub_re, neg_re, conj_re]
  ring

/-- The kernel against a density even in `y₀` and odd in `y₁`, folded onto the quadrant:
`k(x - y) + k(x - R₀ y) - k(x - R₁ y) - k(x + y)`. -/
def evenOddKernel (k : ℝ^2 → ℝ) (x y : ℝ^2) : ℝ :=
  k (x - y) + k (x - 𝐑 0 y) - k (x - 𝐑 1 y) - k (x + y)

/-- The complex form of `evenOddKernel g₁`, with `f(w) = 1/(w - Y)`: the even part of `f` at `X`
and at `X̄`. -/
theorem evenOddKernel_gradientKernel_one_eq (x y : ℝ^2) :
    evenOddKernel (gradientKernel 1) x y = 1 / (2 * Real.pi) *
      (1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) + 1 / (conj (𝔠 x) - 𝔠 y) +
        1 / (-conj (𝔠 x) - 𝔠 y)).im := by
  unfold evenOddKernel
  simp only [gradientKernel_one_eq_im, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e2 : 1 / (𝔠 x - -conj (𝔠 y)) = -conj (1 / (-conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, map_neg, Complex.conj_conj,
      show -𝔠 x - conj (𝔠 y) = -(𝔠 x - -conj (𝔠 y)) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  have e3 : 1 / (𝔠 x - conj (𝔠 y)) = conj (1 / (conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, Complex.conj_conj]
  have e4 : 1 / (𝔠 x + 𝔠 y) = -(1 / (-𝔠 x - 𝔠 y)) := by
    rw [show -𝔠 x - 𝔠 y = -(𝔠 x + 𝔠 y) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  rw [e2, e3, e4]
  simp only [add_im, neg_im, conj_im]
  ring

/-- The complex form of `evenOddKernel g₀`: the difference of the even parts of `f` at `X` and
at `X̄`. -/
theorem evenOddKernel_gradientKernel_zero_eq (x y : ℝ^2) :
    evenOddKernel (gradientKernel 0) x y = -(1 / (2 * Real.pi)) *
      (1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) - (1 / (conj (𝔠 x) - 𝔠 y) +
        1 / (-conj (𝔠 x) - 𝔠 y))).re := by
  unfold evenOddKernel
  simp only [gradientKernel_zero_eq_neg_re, map_sub, map_add,
    orthonormalBasisOneI_repr_symm_coordinateReflection_zero,
    orthonormalBasisOneI_repr_symm_coordinateReflection_one]
  have e2 : 1 / (𝔠 x - -conj (𝔠 y)) = -conj (1 / (-conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, map_neg, Complex.conj_conj,
      show -𝔠 x - conj (𝔠 y) = -(𝔠 x - -conj (𝔠 y)) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  have e3 : 1 / (𝔠 x - conj (𝔠 y)) = conj (1 / (conj (𝔠 x) - 𝔠 y)) := by
    rw [← inv_conj, map_sub, Complex.conj_conj]
  have e4 : 1 / (𝔠 x + 𝔠 y) = -(1 / (-𝔠 x - 𝔠 y)) := by
    rw [show -𝔠 x - 𝔠 y = -(𝔠 x + 𝔠 y) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  rw [e2, e3, e4]
  simp only [sub_re, add_re, neg_re, conj_re]
  ring

end VelocityKernel

/-- For `2 |w| ≤ |Y|` and `|t| ≤ 1`, `|-Y + t w| ≥ |Y|/2`. -/
private theorem half_norm_le_norm_neg_add {Y w : ℂ} (hw : 2 * ‖w‖ ≤ ‖Y‖) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : ‖Y‖ / 2 ≤ ‖-Y + t * w‖ := by
  have htw : ‖(t : ℂ) * w‖ ≤ ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨ht.1, ht.2⟩)
  rw [show -Y + t * w = -(Y - t * w) by ring, norm_neg]
  linarith [norm_sub_norm_le Y ((t : ℂ) * w)]

/-- The odd Taylor remainder of `w ↦ 1/(w - Y)` for `|w| ≤ |Y|/2`. -/
private theorem norm_inv_sub_odd_le {Y w : ℂ} (hY : Y ≠ 0) (hw : 2 * ‖w‖ ≤ ‖Y‖) :
    ‖1 / (w - Y) - 1 / (-w - Y) - 2 * w * (-1 / Y ^ 2)‖ ≤ ‖w‖ ^ 3 / 3 * (96 / ‖Y‖ ^ 4) := by
  have hYpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hlow (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) := half_norm_le_norm_neg_add hw ht
  have hne (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -Y + t * w ≠ 0 :=
    norm_pos_iff.1 ((half_pos hYpos).trans_le (hlow t ht))
  have h := norm_sub_neg_sub_two_mul_le (w := w) (M := 96 / ‖Y‖ ^ 4)
    (F := fun u ↦ 1 * (-Y + u) ^ (-1 : ℤ)) (F₁ := fun u ↦ -1 * (-Y + u) ^ (-2 : ℤ))
    (F₂ := fun u ↦ 2 * (-Y + u) ^ (-3 : ℤ)) (F₃ := fun u ↦ -6 * (-Y + u) ^ (-4 : ℤ))
    (fun t ht ↦ by
      convert hasDerivAt_const_mul_add_zpow 1 (-Y) (-1) (hne t ht) using 1; norm_num)
    (fun t ht ↦ by
      convert hasDerivAt_const_mul_add_zpow (-1) (-Y) (-2) (hne t ht) using 1; norm_num)
    (fun t ht ↦ by
      convert hasDerivAt_const_mul_add_zpow 2 (-Y) (-3) (hne t ht) using 1; norm_num)
    (fun t ht ↦ by
      have hl := hlow t ht
      have hpos : 0 < ‖-Y + t * w‖ := lt_of_lt_of_le (by positivity) hl
      rw [norm_mul, norm_zpow, zpow_neg, zpow_ofNat, norm_neg, norm_ofNat]
      rw [show (96 : ℝ) / ‖Y‖ ^ 4 = 6 * (16 / ‖Y‖ ^ 4) by ring]
      gcongr
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      calc ‖Y‖ ^ 4 / 16 = (‖Y‖ / 2) ^ 4 := by ring
        _ ≤ _ := by gcongr)
  have e1 : ∀ u : ℂ, 1 * (-Y + u) ^ (-1 : ℤ) = 1 / (u - Y) := by
    intro u; rw [one_mul, zpow_neg_one, one_div]; ring_nf
  have e2 : -1 * (-Y + 0) ^ (-2 : ℤ) = -1 / Y ^ 2 := by
    rw [add_zero, zpow_neg, zpow_ofNat, neg_sq]; ring
  simp only [e1, e2] at h
  rwa [show -w - Y = -w - Y from rfl] at h

/-- The even Taylor remainder of `w ↦ 1/(w - Y)` for `|w| ≤ |Y|/2`. -/
private theorem norm_inv_sub_even_le {Y w : ℂ} (hY : Y ≠ 0) (hw : 2 * ‖w‖ ≤ ‖Y‖) :
    ‖1 / (w - Y) + 1 / (-w - Y) - 2 * (1 / -Y)‖ ≤ ‖w‖ ^ 2 * (16 / ‖Y‖ ^ 3) := by
  have hYpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY
  have hlow (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) := half_norm_le_norm_neg_add hw ht
  have hne (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -Y + t * w ≠ 0 :=
    norm_pos_iff.1 ((half_pos hYpos).trans_le (hlow t ht))
  have h := norm_add_neg_sub_two_mul_le (w := w) (M := 16 / ‖Y‖ ^ 3)
    (F := fun u ↦ 1 * (-Y + u) ^ (-1 : ℤ)) (F₁ := fun u ↦ -1 * (-Y + u) ^ (-2 : ℤ))
    (F₂ := fun u ↦ 2 * (-Y + u) ^ (-3 : ℤ))
    (fun t ht ↦ by
      convert hasDerivAt_const_mul_add_zpow 1 (-Y) (-1) (hne t ht) using 1; norm_num)
    (fun t ht ↦ by
      convert hasDerivAt_const_mul_add_zpow (-1) (-Y) (-2) (hne t ht) using 1; norm_num)
    (fun t ht ↦ by
      have hl := hlow t ht
      have hpos : 0 < ‖-Y + t * w‖ := lt_of_lt_of_le (by positivity) hl
      rw [norm_mul, norm_zpow, zpow_neg, zpow_ofNat, norm_ofNat]
      rw [show (16 : ℝ) / ‖Y‖ ^ 3 = 2 * (8 / ‖Y‖ ^ 3) by ring]
      gcongr
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      calc ‖Y‖ ^ 3 / 8 = (‖Y‖ / 2) ^ 3 := by ring
        _ ≤ _ := by gcongr)
  have e1 : ∀ u : ℂ, 1 * (-Y + u) ^ (-1 : ℤ) = 1 / (u - Y) := by
    intro u; rw [one_mul, zpow_neg_one, one_div]; ring_nf
  simp only [e1] at h
  rwa [zero_sub] at h

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- `𝔠 y ≠ 0`, and `w = 𝔠 x`, `w = conj (𝔠 x)` have `|w| = |x|`; `|𝔠 y| = |y|`. -/
private theorem norm_repr_eq {x y : ℝ^2} (hy : y ≠ 0) {w : ℂ} (hw : w = 𝔠 x ∨ w = conj (𝔠 x)) :
    𝔠 y ≠ 0 ∧ ‖w‖ = ‖x‖ ∧ ‖𝔠 y‖ = ‖y‖ := by
  refine ⟨by rw [← norm_pos_iff, LinearIsometryEquiv.norm_map]; exact norm_pos_iff.mpr hy, ?_,
    LinearIsometryEquiv.norm_map _ y⟩
  rcases hw with rfl | rfl
  exacts [LinearIsometryEquiv.norm_map _ x,
    (Complex.norm_conj _).trans (LinearIsometryEquiv.norm_map _ x)]

/-- `norm_inv_sub_odd_le` at `Y = 𝔠 y` and `w = 𝔠 x` or `w = conj (𝔠 x)`. -/
private theorem norm_inv_sub_odd_le_of_le {x y : ℝ^2} (hy : y ≠ 0) (hxy : 2 * ‖x‖ ≤ ‖y‖)
    {w : ℂ} (hw : w = 𝔠 x ∨ w = conj (𝔠 x)) :
    ‖1 / (w - 𝔠 y) - 1 / (-w - 𝔠 y) - 2 * w * (-1 / 𝔠 y ^ 2)‖ ≤
      ‖x‖ ^ 3 / 3 * (96 / ‖y‖ ^ 4) := by
  obtain ⟨hY, hnx, hny⟩ := norm_repr_eq hy hw
  exact (norm_inv_sub_odd_le hY (by rw [hnx, hny]; exact hxy)).trans_eq (by rw [hnx, hny])

/-- `norm_inv_sub_even_le` at `Y = 𝔠 y` and `w = 𝔠 x` or `w = conj (𝔠 x)`. -/
private theorem norm_inv_sub_even_le_of_le {x y : ℝ^2} (hy : y ≠ 0) (hxy : 2 * ‖x‖ ≤ ‖y‖)
    {w : ℂ} (hw : w = 𝔠 x ∨ w = conj (𝔠 x)) :
    ‖1 / (w - 𝔠 y) + 1 / (-w - 𝔠 y) - 2 * (1 / -𝔠 y)‖ ≤ ‖x‖ ^ 2 * (16 / ‖y‖ ^ 3) := by
  obtain ⟨hY, hnx, hny⟩ := norm_repr_eq hy hw
  exact (norm_inv_sub_even_le hY (by rw [hnx, hny]; exact hxy)).trans_eq (by rw [hnx, hny])

/-- `K₁(y) = Im(-1/𝔠(y)²)/2`. -/
private theorem hessianKernel_zero_one_eq_im (y : ℝ^2) :
    hessianKernel 0 1 y = (-1 / (𝔠 y) ^ 2).im / 2 := by
  rw [hessianKernel_zero_one_eq_neg_im, show -1 / (𝔠 y) ^ 2 =
    ((-2 : ℝ) : ℂ) * (1 / (2 * (𝔠 y) ^ 2)) by push_cast; field_simp, im_ofReal_mul]
  ring

/-- **The symmetrized kernel of `u` far from the pole**: for `2|x| ≤ |y|`, `y ≠ 0`,
`|g₁ₛ(x, y) - (4/π) x₀ K₁(y)| ≤ (32/π) |x|³/|y|⁴`. -/
theorem abs_symmetrizedKernel_gradientKernel_one_sub_le {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |symmetrizedKernel (gradientKernel 1) x y - 4 / Real.pi * x 0 * hessianKernel 0 1 y| ≤
      32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 := by
  have hR1 := norm_inv_sub_odd_le_of_le hy hxy (Or.inl rfl)
  have hR2 := norm_inv_sub_odd_le_of_le hy hxy (Or.inr rfl)
  have hsum : 𝔠 x + conj (𝔠 x) = ((2 * x 0 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [add_re, conj_re, ofReal_re, orthonormalBasisOneI_repr_symm_re x]; ring
    · rw [add_im, conj_im, ofReal_im]; ring
  rw [symmetrizedKernel_gradientKernel_one_eq, hessianKernel_zero_one_eq_im]
  set A := 1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) - 2 * 𝔠 x * (-1 / 𝔠 y ^ 2)
  set B := 1 / (conj (𝔠 x) - 𝔠 y) - 1 / (-conj (𝔠 x) - 𝔠 y) - 2 * conj (𝔠 x) * (-1 / 𝔠 y ^ 2)
  have hdecomp : 1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) + 1 / (conj (𝔠 x) - 𝔠 y) -
      1 / (-conj (𝔠 x) - 𝔠 y) = A + B + 2 * (𝔠 x + conj (𝔠 x)) * (-1 / 𝔠 y ^ 2) := by
    simp only [A, B]; ring
  rw [hdecomp, hsum, add_im, add_im]
  have hlin : (2 * (((2 * x 0 : ℝ) : ℂ)) * (-1 / 𝔠 y ^ 2)).im = 4 * x 0 * (-1 / 𝔠 y ^ 2).im := by
    rw [show (2 * (((2 * x 0 : ℝ) : ℂ)) * (-1 / 𝔠 y ^ 2)) =
      ((4 * x 0 : ℝ) : ℂ) * (-1 / 𝔠 y ^ 2) by push_cast; ring, im_ofReal_mul]
  rw [hlin]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcalc : 1 / (2 * Real.pi) * (A.im + B.im + 4 * x 0 * (-1 / 𝔠 y ^ 2).im) -
      4 / Real.pi * x 0 * ((-1 / 𝔠 y ^ 2).im / 2) = 1 / (2 * Real.pi) * (A.im + B.im) := by
    field_simp; ring
  rw [hcalc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hAB : |A.im + B.im| ≤ ‖x‖ ^ 3 / 3 * (96 / ‖y‖ ^ 4) * 2 :=
    calc |A.im + B.im| ≤ |A.im| + |B.im| := abs_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ := add_le_add (Complex.abs_im_le_norm A) (Complex.abs_im_le_norm B)
      _ ≤ _ := by linarith
  calc 1 / (2 * Real.pi) * |A.im + B.im|
        ≤ 1 / (2 * Real.pi) * (‖x‖ ^ 3 / 3 * (96 / ‖y‖ ^ 4) * 2) := by gcongr
    _ = 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 := by field_simp; ring

/-- **The symmetrized kernel of `v` far from the pole**: for `2|x| ≤ |y|`, `y ≠ 0`,
`|g₀ₛ(x, y) - (4/π) x₁ K₁(y)| ≤ (32/π) |x|³/|y|⁴`. -/
theorem abs_symmetrizedKernel_gradientKernel_zero_sub_le {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |symmetrizedKernel (gradientKernel 0) x y - 4 / Real.pi * x 1 * hessianKernel 0 1 y| ≤
      32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 := by
  have hR1 := norm_inv_sub_odd_le_of_le hy hxy (Or.inl rfl)
  have hR2 := norm_inv_sub_odd_le_of_le hy hxy (Or.inr rfl)
  have hdiff : 𝔠 x - conj (𝔠 x) = ((2 * x 1 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [sub_re, conj_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring
    · rw [sub_im, conj_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        orthonormalBasisOneI_repr_symm_im x]; ring
  rw [symmetrizedKernel_gradientKernel_zero_eq, hessianKernel_zero_one_eq_im]
  set A := 1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) - 2 * 𝔠 x * (-1 / 𝔠 y ^ 2)
  set B := 1 / (conj (𝔠 x) - 𝔠 y) - 1 / (-conj (𝔠 x) - 𝔠 y) - 2 * conj (𝔠 x) * (-1 / 𝔠 y ^ 2)
  have hdecomp : 1 / (𝔠 x - 𝔠 y) - 1 / (-𝔠 x - 𝔠 y) - (1 / (conj (𝔠 x) - 𝔠 y) -
      1 / (-conj (𝔠 x) - 𝔠 y)) = A - B + 2 * (𝔠 x - conj (𝔠 x)) * (-1 / 𝔠 y ^ 2) := by
    simp only [A, B]; ring
  rw [hdecomp, hdiff, add_re, sub_re]
  have hlin : (2 * (((2 * x 1 : ℝ) : ℂ) * I) * (-1 / 𝔠 y ^ 2)).re =
      -(4 * x 1 * (-1 / 𝔠 y ^ 2).im) := by
    rw [show 2 * (((2 * x 1 : ℝ) : ℂ) * I) * (-1 / 𝔠 y ^ 2) =
      ((4 * x 1 : ℝ) : ℂ) * (I * (-1 / 𝔠 y ^ 2)) by push_cast; ring, re_ofReal_mul,
      I_mul_re]
    ring
  rw [hlin]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcalc : -(1 / (2 * Real.pi)) * (A.re - B.re + -(4 * x 1 * (-1 / 𝔠 y ^ 2).im)) -
      4 / Real.pi * x 1 * ((-1 / 𝔠 y ^ 2).im / 2) = -(1 / (2 * Real.pi)) * (A.re - B.re) := by
    field_simp; ring
  rw [hcalc, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hAB : |A.re - B.re| ≤ ‖x‖ ^ 3 / 3 * (96 / ‖y‖ ^ 4) * 2 :=
    calc |A.re - B.re| ≤ |A.re| + |B.re| := abs_sub _ _
      _ ≤ ‖A‖ + ‖B‖ := add_le_add (Complex.abs_re_le_norm A) (Complex.abs_re_le_norm B)
      _ ≤ _ := by linarith
  calc 1 / (2 * Real.pi) * |A.re - B.re|
        ≤ 1 / (2 * Real.pi) * (‖x‖ ^ 3 / 3 * (96 / ‖y‖ ^ 4) * 2) := by gcongr
    _ = 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 := by field_simp; ring

/-- **The even-odd kernel of `u_x` far from the pole**: for `2|x| ≤ |y|`, `y ≠ 0`, the kernel
`evenOddKernel g₁` moves by at most `(16/π) |x|²/|y|³` from its value at `x = 0`. -/
theorem abs_evenOddKernel_gradientKernel_one_sub_le {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |evenOddKernel (gradientKernel 1) x y - evenOddKernel (gradientKernel 1) 0 y| ≤
      16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3 := by
  have hR1 := norm_inv_sub_even_le_of_le hy hxy (Or.inl rfl)
  have hR2 := norm_inv_sub_even_le_of_le hy hxy (Or.inr rfl)
  rw [evenOddKernel_gradientKernel_one_eq, evenOddKernel_gradientKernel_one_eq 0 y]
  simp only [map_zero, neg_zero, zero_sub]
  set A := 1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) - 2 * (1 / -𝔠 y)
  set B := 1 / (conj (𝔠 x) - 𝔠 y) + 1 / (-conj (𝔠 x) - 𝔠 y) - 2 * (1 / -𝔠 y)
  have hdecomp : 1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) + 1 / (conj (𝔠 x) - 𝔠 y) +
      1 / (-conj (𝔠 x) - 𝔠 y) =
        A + B + (1 / -𝔠 y + 1 / -𝔠 y + 1 / -𝔠 y + 1 / -𝔠 y) := by
    simp only [A, B]; ring
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hdecomp, add_im, add_im, show ∀ a b c : ℝ, 1 / (2 * Real.pi) * (a + b + c) -
    1 / (2 * Real.pi) * c = 1 / (2 * Real.pi) * (a + b) from fun a b c ↦ by ring, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hAB : |A.im + B.im| ≤ ‖x‖ ^ 2 * (16 / ‖y‖ ^ 3) * 2 :=
    calc |A.im + B.im| ≤ |A.im| + |B.im| := abs_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ := add_le_add (Complex.abs_im_le_norm A) (Complex.abs_im_le_norm B)
      _ ≤ _ := by linarith
  calc 1 / (2 * Real.pi) * |A.im + B.im|
        ≤ 1 / (2 * Real.pi) * (‖x‖ ^ 2 * (16 / ‖y‖ ^ 3) * 2) := by gcongr
    _ = 16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3 := by field_simp

/-- **The even-odd kernel of `v_x` far from the pole**: for `2|x| ≤ |y|`, `y ≠ 0`, the kernel
`evenOddKernel g₀` moves by at most `(16/π) |x|²/|y|³` from its value at `x = 0`. -/
theorem abs_evenOddKernel_gradientKernel_zero_sub_le {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖) :
    |evenOddKernel (gradientKernel 0) x y - evenOddKernel (gradientKernel 0) 0 y| ≤
      16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3 := by
  have hR1 := norm_inv_sub_even_le_of_le hy hxy (Or.inl rfl)
  have hR2 := norm_inv_sub_even_le_of_le hy hxy (Or.inr rfl)
  rw [evenOddKernel_gradientKernel_zero_eq, evenOddKernel_gradientKernel_zero_eq 0 y]
  simp only [map_zero, neg_zero, zero_sub, sub_self, zero_re, mul_zero, sub_zero]
  set A := 1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) - 2 * (1 / -𝔠 y)
  set B := 1 / (conj (𝔠 x) - 𝔠 y) + 1 / (-conj (𝔠 x) - 𝔠 y) - 2 * (1 / -𝔠 y)
  have hdecomp : 1 / (𝔠 x - 𝔠 y) + 1 / (-𝔠 x - 𝔠 y) - (1 / (conj (𝔠 x) - 𝔠 y) +
      1 / (-conj (𝔠 x) - 𝔠 y)) = A - B := by
    simp only [A, B]; ring
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hdecomp, sub_re, abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hAB : |A.re - B.re| ≤ ‖x‖ ^ 2 * (16 / ‖y‖ ^ 3) * 2 :=
    calc |A.re - B.re| ≤ |A.re| + |B.re| := abs_sub _ _
      _ ≤ ‖A‖ + ‖B‖ := add_le_add (Complex.abs_re_le_norm A) (Complex.abs_re_le_norm B)
      _ ≤ _ := by linarith
  calc 1 / (2 * Real.pi) * |A.re - B.re|
        ≤ 1 / (2 * Real.pi) * (‖x‖ ^ 2 * (16 / ‖y‖ ^ 3) * 2) := by gcongr
    _ = 16 / Real.pi * ‖x‖ ^ 2 / ‖y‖ ^ 3 := by field_simp

section Estimate

local notation "𝐑" => PDE.Common.coordinateReflection

/-- The inverse distance has integral `2πρ` on the disc `B(x, ρ)`. -/
theorem integral_ball_norm_sub_inv (x : ℝ^2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ y in Metric.ball x ρ, ‖x - y‖⁻¹ = 2 * Real.pi * ρ := by
  rw [← integral_ball_norm_inv_two ρ hρ, ← integral_indicator measurableSet_ball,
    ← integral_indicator measurableSet_ball]
  rw [← integral_sub_left_eq_self (fun z ↦ (Metric.ball (0 : ℝ^2) ρ).indicator
    (fun z ↦ ‖z‖⁻¹) z) volume x]
  congr 1
  funext y
  by_cases hy : y ∈ Metric.ball x ρ
  · have hy' : x - y ∈ Metric.ball (0 : ℝ^2) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_sub_rev]
      rwa [Metric.mem_ball, dist_eq_norm] at hy
    rw [indicator_of_mem hy, indicator_of_mem hy']
  · have hy' : x - y ∉ Metric.ball (0 : ℝ^2) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_sub_rev]
      rwa [Metric.mem_ball, dist_eq_norm] at hy
    rw [indicator_of_notMem hy, indicator_of_notMem hy']

/-- The function `y ↦ |x - y|⁻¹` is integrable on the disc `B(x, ρ)`. -/
theorem integrableOn_ball_norm_sub_inv (x : ℝ^2) (ρ : ℝ) :
    IntegrableOn (fun y : ℝ^2 ↦ ‖x - y‖⁻¹) (Metric.ball x ρ) := by
  have h := ((integrableOn_ball_norm_inv_two ρ).integrable_indicator
    measurableSet_ball).comp_sub_left x
  rw [← integrable_indicator_iff measurableSet_ball]
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ Metric.ball x ρ
  · have hy' : x - y ∈ Metric.ball (0 : ℝ^2) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_sub_rev]
      rwa [Metric.mem_ball, dist_eq_norm] at hy
    simp only [indicator_of_mem hy, indicator_of_mem hy']
  · have hy' : x - y ∉ Metric.ball (0 : ℝ^2) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_sub_rev]
      rwa [Metric.mem_ball, dist_eq_norm] at hy
    simp only [indicator_of_notMem hy, indicator_of_notMem hy']

/-- **The cubic estimate.** Let `W` be integrable, odd in both coordinates, with
`|W(y)| ≤ M |y|³`, and let the symmetrized kernel of `gⱼ` satisfy the far-field bound with
linear coefficient `(4/π) xₖ K₁(y)`. Then
`|∫ (gⱼ(x - y) - π⁻¹ xₖ K₁(y)) W(y) dy| ≤ (32/π)(2π M + ‖W‖₁) |x|³ + 28 M |x|⁴`. -/
theorem abs_integral_gradientKernel_sub_le (j k : Fin 2) {W : ℝ^2 → ℝ} (hW : Integrable W)
    (hW₀ : ∀ y, W (𝐑 0 y) = -W y) (hW₁ : ∀ y, W (𝐑 1 y) = -W y) {M : ℝ}
    (hM : ∀ y, |W y| ≤ M * ‖y‖ ^ 3) (x : ℝ^2)
    (hker : ∀ y, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4)
    (hgint : Integrable fun y ↦ gradientKernel j (x - y) * W y)
    (hKint : Integrable fun y ↦ hessianKernel 0 1 y * W y) :
    |∫ y, (gradientKernel j (x - y) - 1 / Real.pi * x k * hessianKernel 0 1 y) * W y| ≤
      32 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 3 + 28 * M * ‖x‖ ^ 4 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 ≤ M := (abs_nonneg _).trans ((hM (EuclideanSpace.single 0 1)).trans_eq
    (by rw [PiLp.norm_single, norm_one, one_pow, mul_one]))
  set F : ℝ^2 → ℝ := fun y ↦ (gradientKernel j (x - y) - 1 / Real.pi * x k *
    hessianKernel 0 1 y) * W y with hFdef
  have hF : Integrable F := (hgint.sub (hKint.const_mul (1 / Real.pi * x k))).congr
    (Eventually.of_forall fun y ↦ by simp only [hFdef, Pi.sub_apply]; ring)
  have hnm : Measurable fun y : ℝ^2 ↦ ‖y‖ := measurable_norm
  set A : Set (ℝ^2) := {y | 2 * ‖x‖ ≤ ‖y‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const hnm
  rw [← integral_add_compl hA hF]
  -- the far part, folded onto the quadrant
  have hfar : |∫ y in A, F y| ≤ 32 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 3 := by
    have hAi (i : Fin 2) (y : ℝ^2) : 𝐑 i y ∈ A ↔ y ∈ A := by
      simp only [A, mem_ofPred_eq, PDE.Common.norm_coordinateReflection]
    rw [setIntegral_eq_setIntegral_inter_quadrant hA (hAi 0) (hAi 1) hF.integrableOn]
    have hfold : ∀ y, F y + F (𝐑 0 y) + F (𝐑 1 y) + F (-y) =
        (symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y) *
          W y := by
      intro y
      have hneg : W (-y) = W y := by rw [← coordinateReflection_zero_one, hW₀, hW₁, neg_neg]
      simp only [hFdef, hW₀, hW₁, hneg, hessianKernel_zero_one_coordinateReflection,
        hessianKernel_neg, symmetrizedKernel, sub_neg_eq_add]
      ring
    simp_rw [hfold]
    set G : ℝ^2 → ℝ := fun y ↦ 32 / Real.pi * ‖x‖ ^ 3 *
      ((Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹) y + |W y|)
    have hind : Integrable ((Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹)) :=
      IntegrableOn.integrable_indicator ((integrableOn_ball_norm_inv_two 1).const_mul M)
        measurableSet_ball
    have hGi : Integrable G := (hind.add hW.abs).const_mul _
    have hG0 : 0 ≤ᵐ[volume] G := Eventually.of_forall fun y ↦ mul_nonneg (by positivity)
      (add_nonneg (indicator_nonneg (fun z _ ↦ by positivity) y) (abs_nonneg _))
    have hGint : ∫ y, G y = 32 / Real.pi * (2 * Real.pi * M + ∫ y, |W y|) * ‖x‖ ^ 3 := by
      simp only [G]
      rw [integral_const_mul, integral_add hind hW.abs,
        integral_indicator measurableSet_ball, integral_const_mul,
        integral_ball_norm_inv_two 1 one_pos]
      ring
    rw [← hGint, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hGi.integrableOn) ?_).trans
      (setIntegral_le_integral hGi hG0)
    filter_upwards [ae_restrict_mem (hA.inter measurableSet_quadrant)] with y hy
    have hy0 : y ≠ 0 := by
      intro h; have := hy.2.1; rw [h] at this; simp at this
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [Real.norm_eq_abs, abs_mul]
    have hk := hker y hy0 hy.1
    simp only [G]
    have hb' : |W y| / ‖y‖ ^ 4 ≤
        (Metric.ball (0 : ℝ^2) 1).indicator (fun y ↦ M * ‖y‖⁻¹) y + |W y| := by
      by_cases hb : y ∈ Metric.ball (0 : ℝ^2) 1
      · rw [indicator_of_mem hb]
        have hWy := hM y
        calc |W y| / ‖y‖ ^ 4 ≤ M * ‖y‖ ^ 3 / ‖y‖ ^ 4 := by gcongr
          _ = M * ‖y‖⁻¹ := by field_simp
          _ ≤ M * ‖y‖⁻¹ + |W y| := le_add_of_nonneg_right (abs_nonneg _)
      · rw [indicator_of_notMem hb, zero_add]
        have hge : 1 ≤ ‖y‖ := by simpa using hb
        rw [div_le_iff₀ (by positivity)]
        calc |W y| = |W y| * 1 := (mul_one _).symm
          _ ≤ |W y| * ‖y‖ ^ 4 := by gcongr; exact one_le_pow₀ hge
    calc _ ≤ 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 * |W y| :=
          mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      _ = 32 / Real.pi * ‖x‖ ^ 3 * (|W y| / ‖y‖ ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb' (by positivity)
  -- the near part
  have hnear : |∫ y in Aᶜ, F y| ≤ 28 * M * ‖x‖ ^ 4 := by
    by_cases hx : x = 0
    · have hempty : Aᶜ = ∅ := by
        ext y; simp [A, hx]
      rw [hempty, Measure.restrict_empty, integral_zero_measure, abs_zero]
      positivity
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set G : ℝ^2 → ℝ := fun y ↦ 4 * M * ‖x‖ ^ 3 / Real.pi *
      (Metric.ball x (3 * ‖x‖)).indicator (fun y ↦ ‖x - y‖⁻¹) y +
        M / Real.pi * ‖x‖ ^ 2 * (Metric.ball (0 : ℝ^2) (2 * ‖x‖)).indicator (fun _ ↦ (1 : ℝ)) y
    have hGi : Integrable G :=
      (((integrableOn_ball_norm_sub_inv x _).integrable_indicator
        measurableSet_ball).const_mul _).add
          (((integrableOn_const measure_ball_lt_top.ne).integrable_indicator
            measurableSet_ball).const_mul _)
    have hG0 : 0 ≤ᵐ[volume] G := Eventually.of_forall fun y ↦ add_nonneg
      (mul_nonneg (by positivity) (indicator_nonneg (fun z _ ↦ by positivity) y))
      (mul_nonneg (by positivity) (indicator_nonneg (fun z _ ↦ zero_le_one) y))
    have hGint : ∫ y, G y = 28 * M * ‖x‖ ^ 4 := by
      simp only [G]
      rw [integral_add (((integrableOn_ball_norm_sub_inv x _).integrable_indicator
        measurableSet_ball).const_mul _)
        (((integrableOn_const measure_ball_lt_top.ne).integrable_indicator
          measurableSet_ball).const_mul _),
        integral_const_mul, integral_const_mul, integral_indicator measurableSet_ball,
        integral_ball_norm_sub_inv x (by positivity : (0 : ℝ) < 3 * ‖x‖),
        integral_indicator_const _ measurableSet_ball, smul_eq_mul, mul_one, measureReal_def,
        EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hpi.le]
      field_simp
      ring
    rw [← hGint, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hGi.integrableOn) ?_).trans
      (setIntegral_le_integral hGi hG0)
    filter_upwards [ae_restrict_mem hA.compl] with y hy
    have hy' : ‖y‖ < 2 * ‖x‖ := by simpa [A] using hy
    have hball : y ∈ Metric.ball x (3 * ‖x‖) :=
      mem_ball_iff_norm.2 ((norm_sub_le _ _).trans_lt (by linarith))
    have hball' : y ∈ Metric.ball (0 : ℝ^2) (2 * ‖x‖) := by simpa using hy'
    simp only [G, indicator_of_mem hball, indicator_of_mem hball', mul_one]
    have hWy : |W y| ≤ 8 * M * ‖x‖ ^ 3 :=
      (hM y).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy'.le 3)
        hM0).trans_eq (by ring))
    have hxk : |x k| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x k
    have hKW : |hessianKernel 0 1 y * W y| ≤ M * ‖x‖ := by
      by_cases hy0 : y = 0
      · have h0 : hessianKernel 0 1 (0 : ℝ^2) = 0 := by simp [hessianKernel]
        rw [hy0, h0, zero_mul, abs_zero]; positivity
      have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      rw [abs_mul]
      calc |hessianKernel 0 1 y| * |W y| ≤ 1 / (2 * ‖y‖ ^ 2) * (M * ‖y‖ ^ 3) :=
            mul_le_mul (abs_hessianKernel_le 0 1 y) (hM y) (abs_nonneg _) (by positivity)
        _ = M * ‖y‖ / 2 := by field_simp
        _ ≤ M * ‖x‖ := by nlinarith
    have hg : |gradientKernel j (x - y) * W y| ≤ 4 * M * ‖x‖ ^ 3 / Real.pi * ‖x - y‖⁻¹ := by
      rw [abs_mul]
      by_cases hxy : x - y = 0
      · rw [hxy, gradientKernel_zero, abs_zero, zero_mul]
        positivity
      calc |gradientKernel j (x - y)| * |W y| ≤ 1 / (2 * Real.pi * ‖x - y‖) * (8 * M * ‖x‖ ^ 3) :=
            mul_le_mul (abs_gradientKernel_le j (x - y)) hWy (abs_nonneg _) (by positivity)
        _ = 4 * M * ‖x‖ ^ 3 / Real.pi * ‖x - y‖⁻¹ := by field_simp; ring
    rw [Real.norm_eq_abs]
    simp only [hFdef]
    rw [sub_mul, mul_assoc]
    calc _ ≤ |gradientKernel j (x - y) * W y| +
          |1 / Real.pi * x k * (hessianKernel 0 1 y * W y)| := abs_sub _ _
      _ ≤ 4 * M * ‖x‖ ^ 3 / Real.pi * ‖x - y‖⁻¹ + 1 / Real.pi * ‖x‖ * (M * ‖x‖) := by
        gcongr
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
        gcongr
      _ = _ := by ring
  calc _ ≤ |∫ y in A, F y| + |∫ y in Aᶜ, F y| := abs_add_le _ _
    _ ≤ _ := add_le_add hfar hnear

end Estimate

/-- A bound `|f(y)| ≤ M |y|ⁿ` on the closed upper half-plane forces `M ≥ 0`. -/
theorem nonneg_of_abs_le_mul_pow {f : ℝ^2 → ℝ} {M : ℝ} {n : ℕ}
    (hM : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * ‖y‖ ^ n) : 0 ≤ M := by
  have hy : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by
    rw [PiLp.norm_single, norm_one]
  have := hM (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (by simp)
  rw [hy, one_pow, mul_one] at this
  exact (abs_nonneg _).trans this

/-- The odd extension keeps a bound `|f(y)| ≤ M |y|ⁿ` from the closed upper half-plane. -/
theorem abs_oddHalfSpaceExtension_le_mul_pow {f : ℝ^2 → ℝ} {M : ℝ} {n : ℕ}
    (hM : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * ‖y‖ ^ n) (y : ℝ^2) :
    |oddHalfSpaceExtension f y| ≤ M * ‖y‖ ^ n := by
  have hM0 : 0 ≤ M * ‖y‖ ^ n := mul_nonneg (nonneg_of_abs_le_mul_pow hM) (by positivity)
  have hn : ‖HalfSpace.reflect 2 y‖ = ‖y‖ := HalfSpace.norm_reflect (n := 2) y
  unfold oddHalfSpaceExtension
  simp only [Pi.sub_apply, indicator]
  split_ifs with h1 h2 h2
  · exact absurd h2 (fun h ↦ by
      have a : (0 : ℝ) < y PDE.Common.lastIndex := h1
      have b : y PDE.Common.lastIndex < 0 := h
      linarith)
  · rw [sub_zero]; exact hM y (le_of_lt h1)
  · rw [zero_sub, abs_neg]
    have hrl : 0 ≤ (HalfSpace.reflect 2 y) 1 := by
      have : (0 : ℝ) < (HalfSpace.reflect 2 y) PDE.Common.lastIndex := by
        rw [HalfSpace.reflect_apply_last]; have : y PDE.Common.lastIndex < 0 := h2; linarith
      exact this.le
    have := hM (HalfSpace.reflect 2 y) hrl; rwa [hn] at this
  · rw [sub_zero, abs_zero]; exact hM0

section Expansion

local notation "𝐑" => PDE.Common.coordinateReflection

variable {ω : ℝ^2 → ℝ} (hω : Continuous ω) (hc : HasCompactSupport ω)
  (hodd : ∀ y, 0 ≤ y 1 → ω (𝐑 0 y) = -ω y) {M : ℝ} (hM : ∀ y, 0 ≤ y 1 → |ω y| ≤ M * ‖y‖ ^ 3)
include hω hc hodd hM

omit hodd in
/-- For `|ω(y)| ≤ M |y|³` on the closed upper half-plane the strain integrand `K₁ W` is
integrable on the plane, `W` the odd extension of `ω`. -/
private theorem integrable_strain :
    Integrable fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y := by
  have hWi := integrable_oddHalfSpaceExtension hω hc
  have hm : AEStronglyMeasurable (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y) :=
    (measurable_hessianKernel 0 1).aestronglyMeasurable.mul hWi.aestronglyMeasurable
  have hnear : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y)
      (Metric.ball (0 : ℝ^2) 1) := by
    refine Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne hm ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hlt : ‖y‖ < 1 := by simpa using hy
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy0 : y = 0
    · have h0 : hessianKernel 0 1 (0 : ℝ^2) = 0 := by simp [hessianKernel]
      rw [hy0, h0, abs_zero, zero_mul]
      exact nonneg_of_abs_le_mul_pow hM
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hM0 : 0 ≤ M := nonneg_of_abs_le_mul_pow hM
    calc |hessianKernel 0 1 y| * |oddHalfSpaceExtension ω y| ≤
          1 / (2 * ‖y‖ ^ 2) * (M * ‖y‖ ^ 3) :=
        mul_le_mul (abs_hessianKernel_le 0 1 y) (abs_oddHalfSpaceExtension_le_mul_pow hM y)
          (abs_nonneg _) (by positivity)
      _ = M * ‖y‖ / 2 := by field_simp
      _ ≤ M := by nlinarith
  have hfar : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension ω y)
      (Metric.ball (0 : ℝ^2) 1)ᶜ := by
    refine hWi.integrableOn.bdd_mul (c := 1 / 2)
      (measurable_hessianKernel 0 1).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hy
    rw [Real.norm_eq_abs]
    refine (abs_hessianKernel_le 0 1 y).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at this

/-- For `ω` odd in `x₀`, folding onto the quadrant gives
`-π⁻¹ ∫ K₁ W = -(4/π) ∫_{ℝ²₊₊} K₁ ω`, `W` the odd extension of `ω`. -/
private theorem strain_fold :
    -(1 / Real.pi) * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension ω y =
      -(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y := by
  rw [integral_eq_four_mul_setIntegral_quadrant (integrable_strain hω hc hM)]
  · have : ∫ y in quadrant, hessianKernel 0 1 y * oddHalfSpaceExtension ω y =
        ∫ y in quadrant, hessianKernel 0 1 y * ω y :=
      setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ by
        rw [oddHalfSpaceExtension_eqOn ω (show y ∈ HalfSpace.upper 2 from hy.2)]
    rw [this]; ring
  · intro y
    rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_zero hodd]
    ring
  · intro y
    rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_one]
    ring

/-- **Cubic vanishing of `ũ = u - c x₀`** with the explicit constant, where
`c = -(4/π) ∫_{ℝ²₊₊} K₁ ω` is the strain of Part I (5.67). -/
theorem abs_halfPlaneVelocity_zero_sub_le (x : ℝ^2) :
    |halfPlaneVelocity ω x 0 -
        (-(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y) * x 0| ≤
      32 / Real.pi * (2 * Real.pi * M + ∫ y, |oddHalfSpaceExtension ω y|) * ‖x‖ ^ 3 +
        28 * M * ‖x‖ ^ 4 := by
  have hW := integrable_oddHalfSpaceExtension hω hc
  have hK := integrable_strain hω hc hM
  have hg := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hω hc 1 x
  have h := abs_integral_gradientKernel_sub_le 1 0 hW (oddHalfSpaceExtension_reflect_zero hodd)
    (oddHalfSpaceExtension_reflect_one ω) (abs_oddHalfSpaceExtension_le_mul_pow hM) x
    (fun y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_one_sub_le hy hxy) hg hK
  have hu : halfPlaneVelocity ω x 0 = -∫ y, gradientKernel 1 (x - y) * oddHalfSpaceExtension ω y :=
    by
      have := congrFun (halfPlaneVelocity_zero ω) x
      rw [this, Pi.neg_apply, partialDeriv_halfSpaceGreenPotential_eq_integral hω hc 1 x]
  rw [hu, ← strain_fold hω hc hodd hM]
  have hsplit : (∫ y, (gradientKernel 1 (x - y) - 1 / Real.pi * x 0 * hessianKernel 0 1 y) *
      oddHalfSpaceExtension ω y) = (∫ y, gradientKernel 1 (x - y) * oddHalfSpaceExtension ω y) -
        1 / Real.pi * x 0 * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension ω y := by
    rw [← integral_const_mul, ← integral_sub hg (hK.const_mul _)]
    congr 1; funext y; ring
  rw [hsplit] at h
  calc _ = |(∫ y, gradientKernel 1 (x - y) * oddHalfSpaceExtension ω y) -
        1 / Real.pi * x 0 * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension ω y| := by
          rw [← abs_neg]; congr 1; ring
    _ ≤ _ := h

/-- **Cubic vanishing of `ṽ = v + c x₁`** with the explicit constant. -/
theorem abs_halfPlaneVelocity_one_add_le (x : ℝ^2) :
    |halfPlaneVelocity ω x 1 +
        (-(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y) * x 1| ≤
      32 / Real.pi * (2 * Real.pi * M + ∫ y, |oddHalfSpaceExtension ω y|) * ‖x‖ ^ 3 +
        28 * M * ‖x‖ ^ 4 := by
  have hW := integrable_oddHalfSpaceExtension hω hc
  have hK := integrable_strain hω hc hM
  have hg := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hω hc 0 x
  have h := abs_integral_gradientKernel_sub_le 0 1 hW (oddHalfSpaceExtension_reflect_zero hodd)
    (oddHalfSpaceExtension_reflect_one ω) (abs_oddHalfSpaceExtension_le_mul_pow hM) x
    (fun y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_zero_sub_le hy hxy) hg hK
  have hv : halfPlaneVelocity ω x 1 = ∫ y, gradientKernel 0 (x - y) * oddHalfSpaceExtension ω y :=
    by
      have := congrFun (halfPlaneVelocity_one ω) x
      rw [this, partialDeriv_halfSpaceGreenPotential_eq_integral hω hc 0 x]
  rw [hv, ← strain_fold hω hc hodd hM]
  have hsplit : (∫ y, (gradientKernel 0 (x - y) - 1 / Real.pi * x 1 * hessianKernel 0 1 y) *
      oddHalfSpaceExtension ω y) = (∫ y, gradientKernel 0 (x - y) * oddHalfSpaceExtension ω y) -
        1 / Real.pi * x 1 * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension ω y := by
    rw [← integral_const_mul, ← integral_sub hg (hK.const_mul _)]
    congr 1; funext y; ring
  rw [hsplit] at h
  calc _ = |(∫ y, gradientKernel 0 (x - y) * oddHalfSpaceExtension ω y) -
        1 / Real.pi * x 1 * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension ω y| := by
          congr 1; ring
    _ ≤ _ := h

/-- **`ũ = O(|x|³)` at the origin.** -/
theorem halfPlaneVelocity_zero_sub_isBigO :
    (fun x ↦ halfPlaneVelocity ω x 0 -
        (-(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y) * x 0) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 3 := by
  set C₁ := 32 / Real.pi * (2 * Real.pi * M + ∫ y, |oddHalfSpaceExtension ω y|)
  refine Asymptotics.IsBigO.of_bound (|C₁| + 28 * |M|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^2) one_pos] with x hx
  have hlt : ‖x‖ < 1 := by simpa using hx
  have h := abs_halfPlaneVelocity_zero_sub_le hω hc hodd hM x
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  have h4 : ‖x‖ ^ 4 ≤ ‖x‖ ^ 3 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hlt.le
  calc _ ≤ C₁ * ‖x‖ ^ 3 + 28 * M * ‖x‖ ^ 4 := h
    _ ≤ |C₁| * ‖x‖ ^ 3 + 28 * |M| * ‖x‖ ^ 3 := by
        gcongr
        · exact le_abs_self _
        · nlinarith [abs_nonneg M, le_abs_self M, pow_nonneg (norm_nonneg x) 3,
            pow_nonneg (norm_nonneg x) 4]
    _ = (|C₁| + 28 * |M|) * ‖x‖ ^ 3 := by ring

/-- **`ṽ = O(|x|³)` at the origin.** -/
theorem halfPlaneVelocity_one_add_isBigO :
    (fun x ↦ halfPlaneVelocity ω x 1 +
        (-(4 / Real.pi) * ∫ y in quadrant, hessianKernel 0 1 y * ω y) * x 1) =O[𝓝 0]
      fun x ↦ ‖x‖ ^ 3 := by
  set C₁ := 32 / Real.pi * (2 * Real.pi * M + ∫ y, |oddHalfSpaceExtension ω y|)
  refine Asymptotics.IsBigO.of_bound (|C₁| + 28 * |M|) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^2) one_pos] with x hx
  have hlt : ‖x‖ < 1 := by simpa using hx
  have h := abs_halfPlaneVelocity_one_add_le hω hc hodd hM x
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  have h4 : ‖x‖ ^ 4 ≤ ‖x‖ ^ 3 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hlt.le
  calc _ ≤ C₁ * ‖x‖ ^ 3 + 28 * M * ‖x‖ ^ 4 := h
    _ ≤ |C₁| * ‖x‖ ^ 3 + 28 * |M| * ‖x‖ ^ 3 := by
        gcongr
        · exact le_abs_self _
        · nlinarith [abs_nonneg M, le_abs_self M, pow_nonneg (norm_nonneg x) 3,
            pow_nonneg (norm_nonneg x) 4]
    _ = (|C₁| + 28 * |M|) * ‖x‖ ^ 3 := by ring

end Expansion

/-- **Cubic vanishing with the strain `u_x(0)`** (Part I, after (4.8)): for compactly supported `C²`
vorticity odd in `x₀` with `|ω(y)| ≤ M |y|³`, `u - u_x(0) x₀ = O(|x|³)` and
`v + u_x(0) x₁ = O(|x|³)`, where `u_x(0)` is the tangential component of the derivative of `u` at
the origin within the closed half-plane. -/
theorem halfPlaneVelocity_sub_strain_isBigO {ω : ℝ^2 → ℝ} (hω : ContDiff ℝ 2 ω)
    (hc : HasCompactSupport ω)
    (hodd : ∀ y, 0 ≤ y 1 → ω (PDE.Common.coordinateReflection 0 y) = -ω y)
    {M : ℝ} (hM : ∀ y, 0 ≤ y 1 → |ω y| ≤ M * ‖y‖ ^ 3) :
    (fun x ↦ halfPlaneVelocity ω x 0 -
        (-normalDerivativeFDeriv ω 0) (EuclideanSpace.single 0 1) * x 0) =O[𝓝 0]
        (fun x ↦ ‖x‖ ^ 3) ∧
      (fun x ↦ halfPlaneVelocity ω x 1 +
        (-normalDerivativeFDeriv ω 0) (EuclideanSpace.single 0 1) * x 1) =O[𝓝 0]
        (fun x ↦ ‖x‖ ^ 3) := by
  rw [cOmega_eq hω hc hodd]
  exact ⟨halfPlaneVelocity_zero_sub_isBigO hω.continuous hc hodd hM,
    halfPlaneVelocity_one_add_isBigO hω.continuous hc hodd hM⟩

end IncompressibleFlow
