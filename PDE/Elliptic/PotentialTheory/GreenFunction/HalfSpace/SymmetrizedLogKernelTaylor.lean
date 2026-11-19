/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.SymmetrizedLogKernel
import PDE.Analysis.Complex.PlanarRealPart
import Mathlib.Analysis.Complex.Liouville
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Fourth-order expansion of the symmetrized velocity-gradient kernels

For a density odd in both coordinates, the velocity gradient of its grouped stream function is
`π⁻¹ ∫_{ℝ²₊₊} kₖₗₛ(x, y) ω(y) dy` with the four-image kernels `kₖₗₛ = symmetrizedKernel
(hessianKernel k l)`. With `z = 𝔠 x`, `w = 𝔠 y`, `kₖₗₛ(x, y) = π Re(H''(z, w) eₖ eₗ)` and
`H''(z, w) = π⁻¹ (f_w(z²) - f_{w̄}(z²))`, `f_a(u) = (a² + u)/(a² - u)²`. The expansion
`f_a(u) = a⁻² + 3u a⁻⁴ + u²(5a² - 3u)/(a⁴(a² - u)²)` with
`1/w² - 1/w̄² = -4i K₁(y)` and `3(1/w⁴ - 1/w̄⁴) = -2i q(y)`, `q = quarticKernel`, gives for
`2|x| ≤ |y|`

`kₖₗₛ(x, y) = 4 K₁(y) mₖₗ + 4 q(y) ∂ₖ∂ₗG(x) + O(|x|⁴/|y|⁶)`,
`G(x) = (x₀³ x₁ - x₀ x₁³)/6`, `mₖₗ = ∂ₖ∂ₗ(x₀ x₁)`.

These are the expansions (C.13) and (C.14) of Chen and Hou I, Appendix C.3.1, behind their
stream expansion in Lemma 6.11 and Appendix C.3.3: `∫ 4 K₁ ω` and `∫ 4 q ω` are `π ∂₁₂Ψ(0)`
and `π ∂₁₁₁₂Ψ(0)`.

The remainder is holomorphic in `z` on `|z| < |w|`. The Cauchy estimate on circles of radius
`max(|a|, |b|)` and the mean value theorem give its Lipschitz bound in the evaluation point with
a scale-adapted constant, and the same argument for `H''` itself gives the Lipschitz bound of the
kernels.

## Main definitions

* `quarticKernel`: `q(y) = 12 y₀ y₁ (y₀² - y₁²)/|y|⁸`.
* `quarticHessian`: the Hessian entries `∂ₖ∂ₗG` of `G(x) = (x₀³ x₁ - x₀ x₁³)/6`.

## Main results

* `abs_symmetrizedKernel_hessianKernel_remainder_le`: for `y ≠ 0` and `2|x| ≤ |y|`,
  `|kₖₗₛ(x, y) - 4 K₁(y) mₖₗ - 4 q(y) ∂ₖ∂ₗG(x)| ≤ (184/9) |x|⁴/|y|⁶`.
* `abs_symmetrizedKernel_hessianKernel_le`: `|kₖₗₛ(x, y)| ≤ 2π/|y|²` for `2|x| ≤ |y|`.
* `abs_symmetrizedKernel_hessianKernel_sub_le`: `|kₖₗₛ(a, y) - kₖₗₛ(b, y)| ≤ 8π |a - b|/|y|³`
  for `4|a|, 4|b| ≤ |y|`.
* `abs_symmetrizedKernel_hessianKernel_remainder_sub_le`: for `4|a|, 4|b| ≤ |y|` the fourth-order
  remainder is Lipschitz in the evaluation point with constant `(2944/9) max(|a|, |b|)³/|y|⁶`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, Lemma 6.11,
  Appendix C.3.1, (C.13)-(C.14), and Appendix C.3.3.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set Metric Complex PotentialTheory PotentialTheory.Planar
open scoped ComplexConjugate
open PDE.Analysis (norm_orthonormalBasisOneI_repr_symm_single)

namespace GreenFunction

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- The quartic kernel `q(y) = 12 y₀ y₁ (y₀² - y₁²)/|y|⁸`. -/
def quarticKernel (y : ℝ^2) : ℝ :=
  12 * y 0 * y 1 * (y 0 ^ 2 - y 1 ^ 2) / ‖y‖ ^ 8

/-- The Hessian entries of `G(x) = (x₀³ x₁ - x₀ x₁³)/6`. -/
def quarticHessian (k l : Fin 2) (x : ℝ^2) : ℝ :=
  if k = l then (if k = 0 then x 0 * x 1 else -(x 0 * x 1)) else (x 0 ^ 2 - x 1 ^ 2) / 2

section Algebra

variable {z w : ℂ}

/-- The polynomial part `π⁻¹ ((1/w² - 1/w̄²) + 3 z² (1/w⁴ - 1/w̄⁴))` of `H''(z, w)`. -/
private def polyPart (z w : ℂ) : ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) *
    ((1 / w ^ 2 - 1 / conj w ^ 2) + 3 * z ^ 2 * (1 / w ^ 4 - 1 / conj w ^ 4))

/-- The remainder `H''(z, w) - polyPart z w`. -/
private def rem (z w : ℂ) : ℂ :=
  symmetrizedLogKernelSecondDeriv z w - polyPart z w

/-- The remainder of `(a² + u)/(a² - u)²` after its linear Taylor polynomial in `u`. -/
private def remTerm (a u : ℂ) : ℂ :=
  u ^ 2 * (5 * a ^ 2 - 3 * u) / (a ^ 4 * (a ^ 2 - u) ^ 2)

/-- For `a ≠ 0` and `a² ≠ u`, `(a² + u)/(a² - u)² = a⁻² + 3u a⁻⁴ + remTerm a u`. -/
private theorem decomp (a u : ℂ) (ha : a ≠ 0) (hau : a ^ 2 - u ≠ 0) :
    (a ^ 2 + u) / (a ^ 2 - u) ^ 2 = 1 / a ^ 2 + 3 * u / a ^ 4 + remTerm a u := by
  unfold remTerm
  field_simp
  ring

/-- For `|z| < |w|`, the remainder of `H''(z, w)` is `π⁻¹ (remTerm w z² - remTerm (conj w) z²)`. -/
private theorem rem_eq (h : ‖z‖ < ‖w‖) :
    rem z w = ((1 / Real.pi : ℝ) : ℂ) * (remTerm w (z ^ 2) - remTerm (conj w) (z ^ 2)) := by
  have hw : w ≠ 0 := by
    rintro rfl; simp at h; linarith [norm_nonneg z]
  have hw' : conj w ≠ 0 := by rwa [map_ne_zero]
  have h' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  unfold rem polyPart symmetrizedLogKernelSecondDeriv
  rw [decomp w _ hw (sq_sub_sq_ne_zero_of_norm_lt h), decomp (conj w) _ hw'
      (sq_sub_sq_ne_zero_of_norm_lt h')]
  ring

/-- For `a ≠ 0` and `|u| ≤ |a|²/4`, `|remTerm a u| ≤ (92/9) |u|²/|a|⁶`. -/
private theorem norm_remTerm_le {a u : ℂ} (ha : a ≠ 0) (hu : ‖u‖ ≤ ‖a‖ ^ 2 / 4) :
    ‖remTerm a u‖ ≤ 92 / 9 * (‖u‖ ^ 2 / ‖a‖ ^ 6) := by
  have hap : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hden : 3 / 4 * ‖a‖ ^ 2 ≤ ‖a ^ 2 - u‖ := by
    have := norm_sub_norm_le (a ^ 2) u
    rw [norm_pow] at this
    linarith
  have hnum : ‖5 * a ^ 2 - 3 * u‖ ≤ 23 / 4 * ‖a‖ ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, show ‖(5 : ℂ)‖ = 5 by norm_num,
      show ‖(3 : ℂ)‖ = 3 by norm_num]
    linarith
  have hd0 : 0 < ‖a ^ 2 - u‖ := lt_of_lt_of_le (by positivity) hden
  unfold remTerm
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, div_le_iff₀ (by positivity)]
  calc ‖u‖ ^ 2 * ‖5 * a ^ 2 - 3 * u‖ ≤ ‖u‖ ^ 2 * (23 / 4 * ‖a‖ ^ 2) := by gcongr
    _ = 92 / 9 * (‖u‖ ^ 2 / ‖a‖ ^ 6) * (‖a‖ ^ 4 * (3 / 4 * ‖a‖ ^ 2) ^ 2) := by
        field_simp; ring
    _ ≤ 92 / 9 * (‖u‖ ^ 2 / ‖a‖ ^ 6) * (‖a‖ ^ 4 * ‖a ^ 2 - u‖ ^ 2) := by gcongr

/-- For `w ≠ 0` and `2|z| ≤ |w|`, the remainder of `H''(z, w)` after its polynomial part is at most
`(184/(9π)) |z|⁴/|w|⁶`. -/
private theorem norm_rem_le (hw : w ≠ 0) (h : 2 * ‖z‖ ≤ ‖w‖) :
    ‖rem z w‖ ≤ 184 / (9 * Real.pi) * (‖z‖ ^ 4 / ‖w‖ ^ 6) := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hlt : ‖z‖ < ‖w‖ := by nlinarith [norm_nonneg z]
  have hu : ‖z ^ 2‖ ≤ ‖w‖ ^ 2 / 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have h1 := norm_remTerm_le hw hu
  have h2 := norm_remTerm_le (a := conj w) (u := z ^ 2) (by rwa [map_ne_zero])
    (by rw [norm_conj]; exact hu)
  rw [norm_conj, norm_pow] at h2
  rw [norm_pow] at h1
  rw [rem_eq hlt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  calc 1 / Real.pi * ‖remTerm w (z ^ 2) - remTerm (conj w) (z ^ 2)‖
      ≤ 1 / Real.pi *
          (92 / 9 * ((‖z‖ ^ 2) ^ 2 / ‖w‖ ^ 6) + 92 / 9 * ((‖z‖ ^ 2) ^ 2 / ‖w‖ ^ 6)) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = 184 / (9 * Real.pi) * (‖z‖ ^ 4 / ‖w‖ ^ 6) := by ring

/-- `H''` is holomorphic in `z` for `|z| < |w|`. -/
private theorem differentiableAt_secondDeriv (h : ‖z‖ < ‖w‖) :
    DifferentiableAt ℂ (fun z ↦ symmetrizedLogKernelSecondDeriv z w) z := by
  have h' : ‖z‖ < ‖conj w‖ := by rwa [norm_conj]
  have h1 := pow_ne_zero 2 (sq_sub_sq_ne_zero_of_norm_lt h)
  have h2 := pow_ne_zero 2 (sq_sub_sq_ne_zero_of_norm_lt h')
  unfold symmetrizedLogKernelSecondDeriv
  refine DifferentiableAt.const_mul (DifferentiableAt.sub ?_ ?_) _
  · exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ w ^ 2 + z ^ 2) z).div
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ (w ^ 2 - z ^ 2) ^ 2) z) h1
  · exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ conj w ^ 2 + z ^ 2) z).div
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ (conj w ^ 2 - z ^ 2) ^ 2) z) h2

/-- The remainder is holomorphic in `z` for `|z| < |w|`. -/
private theorem differentiableAt_rem (h : ‖z‖ < ‖w‖) :
    DifferentiableAt ℂ (fun z ↦ rem z w) z := by
  unfold rem polyPart
  exact (differentiableAt_secondDeriv h).sub (by fun_prop)

/-- **Lipschitz bound from a bound on a larger disc** (Cauchy estimate and mean value theorem):
if `f` is holomorphic with `|f| ≤ C` on `|ξ| ≤ m + ρ`, then `|f a - f b| ≤ (C/ρ) |a - b|` for
`|a|, |b| ≤ m`. -/
private theorem norm_sub_le_of_disc {f : ℂ → ℂ} {m ρ C : ℝ} (hρ : 0 < ρ)
    (hd : ∀ ξ : ℂ, ‖ξ‖ ≤ m + ρ → DifferentiableAt ℂ f ξ)
    (hC : ∀ ξ : ℂ, ‖ξ‖ ≤ m + ρ → ‖f ξ‖ ≤ C) {a b : ℂ} (ha : ‖a‖ ≤ m) (hb : ‖b‖ ≤ m) :
    ‖f a - f b‖ ≤ C / ρ * ‖a - b‖ := by
  have hin : ∀ ζ ∈ closedBall (0 : ℂ) m, ∀ ξ ∈ closedBall ζ ρ, ‖ξ‖ ≤ m + ρ := by
    intro ζ hζ ξ hξ
    rw [mem_closedBall, dist_zero_right] at hζ
    rw [mem_closedBall, dist_eq_norm] at hξ
    calc ‖ξ‖ ≤ ‖ξ - ζ‖ + ‖ζ‖ := norm_le_norm_sub_add ξ ζ
      _ ≤ ρ + m := add_le_add hξ hζ
      _ = m + ρ := add_comm _ _
  have hderiv : ∀ ζ ∈ closedBall (0 : ℂ) m, ‖deriv f ζ‖ ≤ C / ρ := by
    intro ζ hζ
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ fun ξ hξ ↦
      hC ξ (hin ζ hζ ξ (sphere_subset_closedBall hξ))
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball ζ hρ.ne']
    exact fun ξ hξ ↦ (hd ξ (hin ζ hζ ξ hξ)).differentiableWithinAt
  have hdm : ∀ ζ ∈ closedBall (0 : ℂ) m, DifferentiableAt ℂ f ζ := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    exact hd ζ (by linarith)
  exact (convex_closedBall (0 : ℂ) m).norm_image_sub_le_of_norm_deriv_le hdm hderiv
    (by rwa [mem_closedBall, dist_zero_right]) (by rwa [mem_closedBall, dist_zero_right])

/-- The remainder is Lipschitz with the scale-adapted constant: for `4|a|, 4|b| ≤ |w|`,
`|rem(a) - rem(b)| ≤ 2944/(9π) max(|a|, |b|)³ |a - b|/|w|⁶`. -/
private theorem norm_rem_sub_le (hw : w ≠ 0) {a b : ℂ} (ha : 4 * ‖a‖ ≤ ‖w‖)
    (hb : 4 * ‖b‖ ≤ ‖w‖) :
    ‖rem a w - rem b w‖ ≤
      2944 / (9 * Real.pi) * (max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖ / ‖w‖ ^ 6) := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set m := max ‖a‖ ‖b‖ with hm
  have ham : ‖a‖ ≤ m := le_max_left _ _
  have hbm : ‖b‖ ≤ m := le_max_right _ _
  have h4m : 4 * m ≤ ‖w‖ := by
    have : m ≤ ‖w‖ / 4 := max_le (by linarith) (by linarith)
    linarith
  rcases (norm_nonneg a).trans ham |>.eq_or_lt with hm0 | hm0
  · have ha0 : a = 0 := norm_eq_zero.mp (le_antisymm (hm0 ▸ ham) (norm_nonneg a))
    have hb0 : b = 0 := norm_eq_zero.mp (le_antisymm (hm0 ▸ hbm) (norm_nonneg b))
    subst ha0 hb0
    simp only [sub_self, norm_zero, mul_zero, zero_div, le_refl]
  have hC : ∀ ξ : ℂ, ‖ξ‖ ≤ m + m →
      ‖rem ξ w‖ ≤ 184 / (9 * Real.pi) * ((2 * m) ^ 4 / ‖w‖ ^ 6) := by
    intro ξ hξ
    refine (norm_rem_le hw (by linarith)).trans ?_
    gcongr
    linarith
  have hd : ∀ ξ : ℂ, ‖ξ‖ ≤ m + m → DifferentiableAt ℂ (fun z ↦ rem z w) ξ :=
    fun ξ hξ ↦ differentiableAt_rem (by linarith)
  refine (norm_sub_le_of_disc hm0 hd hC ham hbm).trans (le_of_eq ?_)
  field_simp
  ring

/-- `H''` is Lipschitz near the origin: for `4|a|, 4|b| ≤ |w|`,
`|H''(a, w) - H''(b, w)| ≤ 8 |a - b|/|w|³`. -/
private theorem norm_secondDeriv_sub_le (hw : w ≠ 0) {a b : ℂ} (ha : 4 * ‖a‖ ≤ ‖w‖)
    (hb : 4 * ‖b‖ ≤ ‖w‖) :
    ‖symmetrizedLogKernelSecondDeriv a w - symmetrizedLogKernelSecondDeriv b w‖ ≤
      8 * ‖a - b‖ / ‖w‖ ^ 3 := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hd : ∀ ξ : ℂ, ‖ξ‖ ≤ ‖w‖ / 4 + ‖w‖ / 4 →
      DifferentiableAt ℂ (fun z ↦ symmetrizedLogKernelSecondDeriv z w) ξ :=
    fun ξ hξ ↦ differentiableAt_secondDeriv (by linarith)
  have hC : ∀ ξ : ℂ, ‖ξ‖ ≤ ‖w‖ / 4 + ‖w‖ / 4 →
      ‖symmetrizedLogKernelSecondDeriv ξ w‖ ≤ 2 / ‖w‖ ^ 2 :=
    fun ξ hξ ↦ norm_symmetrizedLogKernelSecondDeriv_le hw (by linarith)
  refine (norm_sub_le_of_disc (by positivity) hd hC (by linarith) (by linarith)).trans
    (le_of_eq ?_)
  field_simp
  ring

end Algebra

section RealPart

variable {x y : ℝ^2}

/-- `conj (𝔠 y) = y₀ - y₁ i`. -/
private theorem conj_cx_eq (y : ℝ^2) : conj (𝔠 y) = (y 0 : ℂ) - (y 1 : ℂ) * I := by
  rw [orthonormalBasisOneI_repr_symm_apply, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

/-- `𝔠 y conj (𝔠 y) = y₀² + y₁²`. -/
private theorem cx_mul_conj (y : ℝ^2) : 𝔠 y * conj (𝔠 y) = ((y 0 ^ 2 + y 1 ^ 2 : ℝ) : ℂ) := by
  rw [conj_cx_eq, orthonormalBasisOneI_repr_symm_apply]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `1/w² - 1/w̄² = -4i K₁(y)` for `w = 𝔠 y ≠ 0`. -/
private theorem inv_sq_sub (hy : y ≠ 0) :
    1 / 𝔠 y ^ 2 - 1 / conj (𝔠 y) ^ 2 = -4 * I * (hessianKernel 0 1 y : ℂ) := by
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  have hw' : conj (𝔠 y) ≠ 0 := by rwa [map_ne_zero]
  have hN : (y 0 ^ 2 + y 1 ^ 2 : ℝ) ≠ 0 := by
    rw [← EuclideanSpace.norm_sq_fin_two]; positivity
  have h1 : 1 / 𝔠 y ^ 2 - 1 / conj (𝔠 y) ^ 2 =
      (conj (𝔠 y) - 𝔠 y) * (conj (𝔠 y) + 𝔠 y) / (𝔠 y * conj (𝔠 y)) ^ 2 := by
    field_simp; ring
  have hm : conj (𝔠 y) - 𝔠 y = -2 * (y 1 : ℂ) * I := by
    rw [conj_cx_eq, orthonormalBasisOneI_repr_symm_apply]; ring
  have hp : conj (𝔠 y) + 𝔠 y = 2 * (y 0 : ℂ) := by
    rw [conj_cx_eq, orthonormalBasisOneI_repr_symm_apply]; ring
  rw [h1, hm, hp, cx_mul_conj, hessianKernel_zero_one,
    show ‖y‖ ^ 4 = (y 0 ^ 2 + y 1 ^ 2) ^ 2 by rw [← EuclideanSpace.norm_sq_fin_two]; ring]
  have hNc : ((y 0 ^ 2 + y 1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast at hNc ⊢
  field_simp
  ring

/-- `3 (1/w⁴ - 1/w̄⁴) = -2i q(y)` for `w = 𝔠 y ≠ 0`. -/
private theorem inv_pow_four_sub (hy : y ≠ 0) :
    3 * (1 / 𝔠 y ^ 4 - 1 / conj (𝔠 y) ^ 4) = -2 * I * (quarticKernel y : ℂ) := by
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  have hw' : conj (𝔠 y) ≠ 0 := by rwa [map_ne_zero]
  have hN : (y 0 ^ 2 + y 1 ^ 2 : ℝ) ≠ 0 := by
    rw [← EuclideanSpace.norm_sq_fin_two]; positivity
  have h1 : 1 / 𝔠 y ^ 4 - 1 / conj (𝔠 y) ^ 4 =
      (conj (𝔠 y) - 𝔠 y) * (conj (𝔠 y) + 𝔠 y) *
        ((conj (𝔠 y) + 𝔠 y) ^ 2 - 2 * (𝔠 y * conj (𝔠 y))) / (𝔠 y * conj (𝔠 y)) ^ 4 := by
    field_simp; ring
  have hm : conj (𝔠 y) - 𝔠 y = -2 * (y 1 : ℂ) * I := by
    rw [conj_cx_eq, orthonormalBasisOneI_repr_symm_apply]; ring
  have hp : conj (𝔠 y) + 𝔠 y = 2 * (y 0 : ℂ) := by
    rw [conj_cx_eq, orthonormalBasisOneI_repr_symm_apply]; ring
  rw [h1, hm, hp, cx_mul_conj, quarticKernel,
    show ‖y‖ ^ 8 = (y 0 ^ 2 + y 1 ^ 2) ^ 4 by rw [← EuclideanSpace.norm_sq_fin_two]; ring]
  have hNc : ((y 0 ^ 2 + y 1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast at hNc ⊢
  field_simp
  ring

/-- The polynomial part of the kernel: `π Re(polyPart(𝔠 x, 𝔠 y) eₖ eₗ)` is
`4 K₁(y) mₖₗ + 4 q(y) ∂ₖ∂ₗG(x)`. -/
private theorem re_polyPart (k l : Fin 2) (hy : y ≠ 0) :
    Real.pi * (polyPart (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single k 1) *
        𝔠 (EuclideanSpace.single l 1)).re =
      4 * hessianKernel 0 1 y * (if k = l then 0 else 1) +
        4 * quarticKernel y * quarticHessian k l x := by
  have hpoly : polyPart (𝔠 x) (𝔠 y) = ((1 / Real.pi : ℝ) : ℂ) *
      (-4 * I * (hessianKernel 0 1 y : ℂ) + (𝔠 x) ^ 2 * (-2 * I * (quarticKernel y : ℂ))) := by
    unfold polyPart
    rw [inv_sq_sub hy, ← inv_pow_four_sub hy]
    ring
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hpoly, mul_assoc, mul_assoc, re_ofReal_mul, ← mul_assoc, mul_one_div_cancel hπ, one_mul]
  rw [orthonormalBasisOneI_repr_symm_apply x]
  fin_cases k <;> fin_cases l <;>
    simp [quarticHessian, sq, mul_re, mul_im, ofReal_re, ofReal_im] <;> ring

/-- `kₖₗₛ(x, y) = π Re(H''(𝔠 x, 𝔠 y) eₖ eₗ)` split into its polynomial part and the remainder. -/
private theorem symmetrizedKernel_eq (k l : Fin 2) (hy : y ≠ 0) (h : ‖x‖ < ‖y‖) :
    symmetrizedKernel (hessianKernel k l) x y =
      4 * hessianKernel 0 1 y * (if k = l then 0 else 1) +
        4 * quarticKernel y * quarticHessian k l x +
          Real.pi * (rem (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single k 1) *
            𝔠 (EuclideanSpace.single l 1)).re := by
  have hre := re_symmetrizedLogKernelSecondDeriv_mul_mul k l h
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hks : symmetrizedKernel (hessianKernel k l) x y =
      Real.pi * (symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single k 1) *
        𝔠 (EuclideanSpace.single l 1)).re := by
    rw [hre]; field_simp
  rw [hks, ← re_polyPart k l hy, ← mul_add, ← add_re]
  congr 2
  unfold rem
  ring

/-- `|π Re(c eₖ eₗ)| ≤ π |c|`. -/
private theorem abs_pi_re_le (k l : Fin 2) (c : ℂ) :
    |Real.pi * (c * 𝔠 (EuclideanSpace.single k 1) * 𝔠 (EuclideanSpace.single l 1)).re| ≤
      Real.pi * ‖c‖ := by
  rw [abs_mul, abs_of_pos Real.pi_pos]
  gcongr
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_orthonormalBasisOneI_repr_symm_single,
      norm_orthonormalBasisOneI_repr_symm_single, mul_one, mul_one]

/-- **Fourth-order expansion of the symmetrized velocity-gradient kernels.** For `y ≠ 0` and
`2|x| ≤ |y|`,
`|kₖₗₛ(x, y) - 4 K₁(y) mₖₗ - 4 q(y) ∂ₖ∂ₗG(x)| ≤ (184/9) |x|⁴/|y|⁶`, where `mₖₗ = 1` for `k ≠ l`
and `0` otherwise, `q = quarticKernel` and `G(x) = (x₀³x₁ - x₀x₁³)/6`. -/
theorem abs_symmetrizedKernel_hessianKernel_remainder_le (k l : Fin 2) (hy : y ≠ 0)
    (h : 2 * ‖x‖ ≤ ‖y‖) :
    |symmetrizedKernel (hessianKernel k l) x y -
        (4 * hessianKernel 0 1 y * (if k = l then 0 else 1) +
          4 * quarticKernel y * quarticHessian k l x)| ≤ 184 / 9 * (‖x‖ ^ 4 / ‖y‖ ^ 6) := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hlt : ‖x‖ < ‖y‖ := by nlinarith [norm_nonneg x]
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  rw [symmetrizedKernel_eq k l hy hlt, add_sub_cancel_left]
  refine (abs_pi_re_le k l _).trans ?_
  have hb := norm_rem_le (z := 𝔠 x) hw (by simpa only [LinearIsometryEquiv.norm_map])
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hb
  calc Real.pi * ‖rem (𝔠 x) (𝔠 y)‖ ≤ Real.pi * (184 / (9 * Real.pi) * (‖x‖ ^ 4 / ‖y‖ ^ 6)) := by
        gcongr
    _ = 184 / 9 * (‖x‖ ^ 4 / ‖y‖ ^ 6) := by field_simp

/-- **Size of the symmetrized velocity-gradient kernels**: `|kₖₗₛ(x, y)| ≤ 2π/|y|²` for `y ≠ 0`
and `2|x| ≤ |y|`. -/
theorem abs_symmetrizedKernel_hessianKernel_le (k l : Fin 2) (hy : y ≠ 0)
    (h : 2 * ‖x‖ ≤ ‖y‖) :
    |symmetrizedKernel (hessianKernel k l) x y| ≤ 2 * Real.pi / ‖y‖ ^ 2 := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hlt : ‖x‖ < ‖y‖ := by nlinarith [norm_nonneg x]
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  have hre := re_symmetrizedLogKernelSecondDeriv_mul_mul k l hlt
  have hks : symmetrizedKernel (hessianKernel k l) x y =
      Real.pi * (symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single k 1) *
        𝔠 (EuclideanSpace.single l 1)).re := by
    rw [hre]; field_simp
  rw [hks]
  refine (abs_pi_re_le k l _).trans ?_
  have hb := norm_symmetrizedLogKernelSecondDeriv_le (z := 𝔠 x) hw
    (by simpa only [LinearIsometryEquiv.norm_map])
  rw [LinearIsometryEquiv.norm_map] at hb
  calc Real.pi * ‖symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y)‖ ≤ Real.pi * (2 / ‖y‖ ^ 2) := by
        gcongr
    _ = 2 * Real.pi / ‖y‖ ^ 2 := by ring

/-- **Lipschitz bound of the symmetrized velocity-gradient kernels** in the evaluation point:
`|kₖₗₛ(a, y) - kₖₗₛ(b, y)| ≤ 8π |a - b|/|y|³` for `y ≠ 0` and `4|a|, 4|b| ≤ |y|`. -/
theorem abs_symmetrizedKernel_hessianKernel_sub_le (k l : Fin 2) {a b : ℝ^2} (hy : y ≠ 0)
    (ha : 4 * ‖a‖ ≤ ‖y‖) (hb : 4 * ‖b‖ ≤ ‖y‖) :
    |symmetrizedKernel (hessianKernel k l) a y - symmetrizedKernel (hessianKernel k l) b y| ≤
      8 * Real.pi * ‖a - b‖ / ‖y‖ ^ 3 := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  have hks (x : ℝ^2) (hx : 4 * ‖x‖ ≤ ‖y‖) : symmetrizedKernel (hessianKernel k l) x y =
      Real.pi * (symmetrizedLogKernelSecondDeriv (𝔠 x) (𝔠 y) * 𝔠 (EuclideanSpace.single k 1) *
        𝔠 (EuclideanSpace.single l 1)).re := by
    rw [re_symmetrizedLogKernelSecondDeriv_mul_mul k l (by nlinarith [norm_nonneg x])]
    field_simp
  rw [hks a ha, hks b hb, ← mul_sub, ← sub_re, ← sub_mul, ← sub_mul]
  refine (abs_pi_re_le k l _).trans ?_
  have h := norm_secondDeriv_sub_le (a := 𝔠 a) (b := 𝔠 b) hw
    (by simpa only [LinearIsometryEquiv.norm_map])
    (by simpa only [LinearIsometryEquiv.norm_map])
  rw [← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  calc Real.pi * ‖symmetrizedLogKernelSecondDeriv (𝔠 a) (𝔠 y) -
        symmetrizedLogKernelSecondDeriv (𝔠 b) (𝔠 y)‖ ≤ Real.pi * (8 * ‖a - b‖ / ‖y‖ ^ 3) := by
        gcongr
    _ = 8 * Real.pi * ‖a - b‖ / ‖y‖ ^ 3 := by ring

/-- **Lipschitz bound of the fourth-order remainder** of the symmetrized velocity-gradient
kernels: with `Tₖₗ(x, y) = 4 K₁(y) mₖₗ + 4 q(y) ∂ₖ∂ₗG(x)`, for `y ≠ 0` and `4|a|, 4|b| ≤ |y|`,
`|(kₖₗₛ - Tₖₗ)(a, y) - (kₖₗₛ - Tₖₗ)(b, y)| ≤ (2944/9) max(|a|, |b|)³ |a - b|/|y|⁶`. -/
theorem abs_symmetrizedKernel_hessianKernel_remainder_sub_le (k l : Fin 2) {a b : ℝ^2}
    (hy : y ≠ 0) (ha : 4 * ‖a‖ ≤ ‖y‖) (hb : 4 * ‖b‖ ≤ ‖y‖) :
    |(symmetrizedKernel (hessianKernel k l) a y -
        (4 * hessianKernel 0 1 y * (if k = l then 0 else 1) +
          4 * quarticKernel y * quarticHessian k l a)) -
      (symmetrizedKernel (hessianKernel k l) b y -
        (4 * hessianKernel 0 1 y * (if k = l then 0 else 1) +
          4 * quarticKernel y * quarticHessian k l b))| ≤
      2944 / 9 * (max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖ / ‖y‖ ^ 6) := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hw : 𝔠 y ≠ 0 := by rwa [ne_eq, LinearIsometryEquiv.map_eq_zero_iff]
  rw [symmetrizedKernel_eq k l hy (by nlinarith [norm_nonneg a]),
    symmetrizedKernel_eq k l hy (by nlinarith [norm_nonneg b]), add_sub_cancel_left,
    add_sub_cancel_left, ← mul_sub, ← sub_re, ← sub_mul, ← sub_mul]
  refine (abs_pi_re_le k l _).trans ?_
  have h := norm_rem_sub_le (a := 𝔠 a) (b := 𝔠 b) hw (by simpa only [LinearIsometryEquiv.norm_map])
    (by simpa only [LinearIsometryEquiv.norm_map])
  rw [← map_sub] at h
  simp only [LinearIsometryEquiv.norm_map] at h
  calc Real.pi * ‖rem (𝔠 a) (𝔠 y) - rem (𝔠 b) (𝔠 y)‖ ≤
        Real.pi * (2944 / (9 * Real.pi) * (max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖ / ‖y‖ ^ 6)) := by
        gcongr
    _ = 2944 / 9 * (max ‖a‖ ‖b‖ ^ 3 * ‖a - b‖ / ‖y‖ ^ 6) := by field_simp

end RealPart

end GreenFunction
