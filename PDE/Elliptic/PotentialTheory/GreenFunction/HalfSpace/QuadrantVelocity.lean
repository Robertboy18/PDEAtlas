/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavartKernel
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The four-image velocity kernel of the quadrant in complex form

For a vorticity odd in both coordinates, the velocity `(u, v) = ∇^⊥ψ` at `x` of a unit point
vortex at `y` in the open quadrant, together with its three images `-ȳ`, `ȳ`, `-y` (signs
`+, -, -, +`), is `π⁻¹` times the complex number

`V(z, w) = -(1/2) ((z - w)⁻¹ - (z + w̄)⁻¹ - (z - w̄)⁻¹ + (z + w)⁻¹)`

with `z = x₀ + i x₁`, `w = y₀ + i y₁`, in the form `V = π (v + i u)`: the real part is `π` times
the symmetrized gradient kernel `∂₀Φ` and the imaginary part is `-π` times that of `∂₁Φ`.

In the far-field expansion of `V` the even powers of `z` cancel between the images, the linear
term is the strain part and the cubic term the first far-field correction. The derivatives along
lines, with the target or the source moving, are the inputs of the trapezoidal rule and of the
interpolation in the target of Chen and Hou II, Lemmas 4.2 and 4.4, for the combined velocity
kernels.

## Main definitions

* `quadrantVelocity`: the four-image velocity kernel `V(z, w)`, without `1/π`.
* `quadrantImage`, `quadrantSign`: the four images `w, -w̄, w̄, -w` and their signs `+, -, -, +`.
* `cancelledKernel`: `(z - w)⁻³ + (z + w)⁻³ + 6 z w⁻⁴`, the second `w`-derivative of the pair of
  images `w, -w` with the strain part removed.

## Main results

* `quadrantVelocity_re`, `quadrantVelocity_im`: `Re V = π v` and `Im V = π u`.
* `strainKernel_eq_neg_half_im`: `y₀ y₁ / |y|⁴ = -(1/2) Im(w⁻²)`, the kernel of the strain
  `u_x(0)`; `inv_sq_sub_conj_inv_sq`: `w⁻² - w̄⁻² = 2 i Im(w⁻²)`.
* `norm_quadrantVelocity_sub_le`: for `|z| < |w|`,
  `|V(z, w) - z (w⁻² - w̄⁻²) - z³ (w⁻⁴ - w̄⁻⁴)| ≤ 2 |z|⁵ / (|w|⁵ (|w| - |z|))`.
* `hasDerivAt_re_mul_inv_pow_line`: along a real line `s ↦ z₀ + s d`,
  `(c (z₀ + s d)⁻ⁿ)' = Re(-n c d (z₀ + s d)⁻⁽ⁿ⁺¹⁾)`.
* `hasDerivAt_quadrantVelocity_target`, `abs_quadrantVelocity_target_second_le`: the second
  derivative of `Re(c V(z + s d, w))` and the bound `|f''| ≤ |c| |d|² Σₖ |z - uₖ|⁻³`.
* `hasDerivAt_quadrantVelocity_source`, `abs_quadrantVelocity_source_second_le`: the same with
  the source moving.
* `hasDerivAt_strainTerm_line`, `abs_strainTerm_second_le`: for the strain term
  `Re(c z (w + s d)⁻²)`, `|h''| ≤ 6 |c| |z| |d|² / |w + t d|⁴`.
* `norm_cancelledKernel_le`: for `|z| < |w|`,
  `|cancelledKernel z w| ≤ |z|³ (6ρ² + 18ρ + 20)/(|w|² - |z|²)³` with `ρ = |z|²/|w|²`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.1.3,
  Lemmas 4.2 and 4.4.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Complex PotentialTheory.Planar
open scoped ComplexConjugate

namespace GreenFunction

set_option linter.missingDocs true

/-- The four-image velocity kernel of the quadrant in complex form, without `1/π`:
`V(z, w) = -(1/2) ((z - w)⁻¹ - (z + w̄)⁻¹ - (z - w̄)⁻¹ + (z + w)⁻¹)`, so that
`V(z, w) = π (v + i u)` for the velocity at `z` of a unit vortex at `w` with its images. -/
def quadrantVelocity (z w : ℂ) : ℂ :=
  -(1 / 2) * ((z - w)⁻¹ - (z + conj w)⁻¹ - (z - conj w)⁻¹ + (z + w)⁻¹)

/-! ### The real form -/

/-- `|s|² = normSq (s₀ + i s₁)`. -/
private theorem norm_sq_eq_normSq (s : ℝ^2) : ‖s‖ ^ 2 = normSq (⟨s 0, s 1⟩ : ℂ) := by
  rw [EuclideanSpace.norm_sq_fin_two, normSq_apply]
  ring

/-- `∂₀Φ(s) = -(1/(2π)) Re(1/(s₀ + i s₁))`, also at the pole. -/
theorem gradientKernel_zero_eq_neg_re_inv (s : ℝ^2) :
    gradientKernel 0 s = -(1 / (2 * Real.pi)) * ((⟨s 0, s 1⟩ : ℂ)⁻¹).re := by
  rw [gradientKernel_eq_div, inv_re, ← norm_sq_eq_normSq]
  ring

/-- `∂₁Φ(s) = (1/(2π)) Im(1/(s₀ + i s₁))`, also at the pole. -/
theorem gradientKernel_one_eq_im_inv (s : ℝ^2) :
    gradientKernel 1 s = 1 / (2 * Real.pi) * ((⟨s 0, s 1⟩ : ℂ)⁻¹).im := by
  rw [gradientKernel_eq_div, inv_im, ← norm_sq_eq_normSq]
  ring

/-- The complex form of `x - y` is `(x₀ + i x₁) - (y₀ + i y₁)`. -/
private theorem cpt_sub (x y : ℝ^2) :
    (⟨(x - y) 0, (x - y) 1⟩ : ℂ) = ⟨x 0, x 1⟩ - ⟨y 0, y 1⟩ := by
  apply Complex.ext <;> simp

/-- The complex form of `x + y` is `(x₀ + i x₁) + (y₀ + i y₁)`. -/
private theorem cpt_add (x y : ℝ^2) :
    (⟨(x + y) 0, (x + y) 1⟩ : ℂ) = ⟨x 0, x 1⟩ + ⟨y 0, y 1⟩ := by
  apply Complex.ext <;> simp

/-- The complex form of `x - R₀ y` is `(x₀ + i x₁) + conj (y₀ + i y₁)`. -/
private theorem cpt_sub_reflect_zero (x y : ℝ^2) :
    (⟨(x - PDE.Common.coordinateReflection 0 y) 0, (x - PDE.Common.coordinateReflection 0 y) 1⟩ :
      ℂ) = ⟨x 0, x 1⟩ + conj ⟨y 0, y 1⟩ := by
  apply Complex.ext
  · simp [PDE.Common.coordinateReflection_apply_same]
  · simp
    ring

/-- The complex form of `x - R₁ y` is `(x₀ + i x₁) - conj (y₀ + i y₁)`. -/
private theorem cpt_sub_reflect_one (x y : ℝ^2) :
    (⟨(x - PDE.Common.coordinateReflection 1 y) 0, (x - PDE.Common.coordinateReflection 1 y) 1⟩ :
      ℂ) = ⟨x 0, x 1⟩ - conj ⟨y 0, y 1⟩ := by
  apply Complex.ext
  · simp
  · simp [PDE.Common.coordinateReflection_apply_same]

/-- `Re(-(1/2) X) = -(1/2) Re X`. -/
private theorem re_neg_half_mul (X : ℂ) : (-(1 / 2) * X).re = -(1 / 2) * X.re := by simp

/-- `Im(-(1/2) X) = -(1/2) Im X`. -/
private theorem im_neg_half_mul (X : ℂ) : (-(1 / 2) * X).im = -(1 / 2) * X.im := by simp

/-- The real part of `V` is `π` times the symmetrized kernel of `∂₀Φ`: `Re V = π v`. -/
theorem quadrantVelocity_re (x y : ℝ^2) :
    (quadrantVelocity ⟨x 0, x 1⟩ ⟨y 0, y 1⟩).re =
      Real.pi * symmetrizedKernel (gradientKernel 0) x y := by
  unfold symmetrizedKernel
  simp only [gradientKernel_zero_eq_neg_re_inv]
  rw [cpt_sub_reflect_zero, cpt_sub_reflect_one, cpt_sub, cpt_add, quadrantVelocity,
    re_neg_half_mul]
  simp only [sub_re, add_re]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The imaginary part of `V` is `-π` times the symmetrized kernel of `∂₁Φ`: `Im V = π u`. -/
theorem quadrantVelocity_im (x y : ℝ^2) :
    (quadrantVelocity ⟨x 0, x 1⟩ ⟨y 0, y 1⟩).im =
      -(Real.pi * symmetrizedKernel (gradientKernel 1) x y) := by
  unfold symmetrizedKernel
  simp only [gradientKernel_one_eq_im_inv]
  rw [cpt_sub_reflect_zero, cpt_sub_reflect_one, cpt_sub, cpt_add, quadrantVelocity,
    im_neg_half_mul]
  simp only [sub_im, add_im]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### The strain kernel -/

/-- The kernel `y₀ y₁ / |y|⁴` of the strain `u_x(0)` is `-(1/2) Im(w⁻²)` for `w = y₀ + i y₁`,
also at the origin. -/
theorem strainKernel_eq_neg_half_im (y : ℝ^2) :
    y 0 * y 1 / ‖y‖ ^ 4 = -(1 / 2) * ((⟨y 0, y 1⟩ : ℂ)⁻¹ ^ 2).im := by
  have h4 : ‖y‖ ^ 4 = (normSq (⟨y 0, y 1⟩ : ℂ)) ^ 2 := by
    rw [← norm_sq_eq_normSq]; ring
  rw [h4, inv_pow, inv_im, map_pow]
  simp only [pow_two, mul_im, normSq_apply]
  ring

/-- `w⁻² - w̄⁻² = 2 i Im(w⁻²)`. -/
theorem inv_sq_sub_conj_inv_sq (w : ℂ) :
    w⁻¹ ^ 2 - (conj w)⁻¹ ^ 2 = 2 * I * (w⁻¹ ^ 2).im := by
  have h : (conj w)⁻¹ ^ 2 = conj (w⁻¹ ^ 2) := by simp
  rw [h, sub_conj]
  push_cast
  ring

/-! ### The far-field expansion -/

/-- The geometric expansion of `(z - u)⁻¹` to order four with its exact remainder. -/
private theorem inv_sub_eq_expansion {z u : ℂ} (hu : u ≠ 0) (hzu : z - u ≠ 0) :
    (z - u)⁻¹ = -(u⁻¹ + z * u⁻¹ ^ 2 + z ^ 2 * u⁻¹ ^ 3 + z ^ 3 * u⁻¹ ^ 4 + z ^ 4 * u⁻¹ ^ 5) +
      z ^ 5 * u⁻¹ ^ 5 * (z - u)⁻¹ := by
  field_simp
  ring

/-- For `|u| = r` and `|z| < r`, the remainder `z⁵ u⁻⁵ (z - u)⁻¹` of the geometric expansion is at
most `|z|⁵/(r⁵ (r - |z|))`. -/
private theorem norm_remainder_le {z u : ℂ} {r : ℝ} (hu : ‖u‖ = r) (hz : ‖z‖ < r) :
    ‖z ^ 5 * u⁻¹ ^ 5 * (z - u)⁻¹‖ ≤ ‖z‖ ^ 5 / (r ^ 5 * (r - ‖z‖)) := by
  have hr : 0 < r := (norm_nonneg z).trans_lt hz
  have hd : r - ‖z‖ ≤ ‖z - u‖ := by
    have := norm_sub_norm_le u z
    rw [norm_sub_rev] at this
    linarith
  have hd0 : 0 < r - ‖z‖ := by linarith
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, hu, div_eq_mul_inv,
    mul_inv, inv_pow]
  have h1 : ‖z - u‖⁻¹ ≤ (r - ‖z‖)⁻¹ := inv_anti₀ hd0 hd
  have h2 : 0 ≤ ‖z‖ ^ 5 * (r ^ 5)⁻¹ := by positivity
  calc ‖z‖ ^ 5 * (r ^ 5)⁻¹ * ‖z - u‖⁻¹ ≤ ‖z‖ ^ 5 * (r ^ 5)⁻¹ * (r - ‖z‖)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = ‖z‖ ^ 5 * ((r ^ 5)⁻¹ * (r - ‖z‖)⁻¹) := by ring

/-- **The far-field expansion of `V`.** For `|z| < |w|`, the even powers of `z` cancel between
the four images, and
`|V(z, w) - z (w⁻² - w̄⁻²) - z³ (w⁻⁴ - w̄⁻⁴)| ≤ 2 |z|⁵ / (|w|⁵ (|w| - |z|))`. -/
theorem norm_quadrantVelocity_sub_le {z w : ℂ} (h : ‖z‖ < ‖w‖) :
    ‖quadrantVelocity z w - z * (w⁻¹ ^ 2 - (conj w)⁻¹ ^ 2) -
        z ^ 3 * (w⁻¹ ^ 4 - (conj w)⁻¹ ^ 4)‖ ≤
      2 * ‖z‖ ^ 5 / (‖w‖ ^ 5 * (‖w‖ - ‖z‖)) := by
  have hw : w ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    exact (not_lt.mpr (norm_nonneg z)) h
  have hcw : conj w ≠ 0 := by simpa using hw
  have hne : ∀ u : ℂ, ‖u‖ = ‖w‖ → z - u ≠ 0 := fun u hu h0 ↦ by
    rw [sub_eq_zero] at h0; rw [h0, hu] at h; exact lt_irrefl _ h
  have n1 : ‖w‖ = ‖w‖ := rfl
  have n2 : ‖-conj w‖ = ‖w‖ := by simp
  have n3 : ‖conj w‖ = ‖w‖ := by simp
  have n4 : ‖-w‖ = ‖w‖ := by simp
  have e1 := inv_sub_eq_expansion hw (hne w n1)
  have e2 := inv_sub_eq_expansion (neg_ne_zero.mpr hcw) (hne _ n2)
  have e3 := inv_sub_eq_expansion hcw (hne _ n3)
  have e4 := inv_sub_eq_expansion (neg_ne_zero.mpr hw) (hne _ n4)
  rw [sub_neg_eq_add] at e2 e4
  have key : quadrantVelocity z w - z * (w⁻¹ ^ 2 - (conj w)⁻¹ ^ 2) -
      z ^ 3 * (w⁻¹ ^ 4 - (conj w)⁻¹ ^ 4) =
      -(1 / 2) * (z ^ 5 * w⁻¹ ^ 5 * (z - w)⁻¹ - z ^ 5 * (-conj w)⁻¹ ^ 5 * (z + conj w)⁻¹ -
        z ^ 5 * (conj w)⁻¹ ^ 5 * (z - conj w)⁻¹ + z ^ 5 * (-w)⁻¹ ^ 5 * (z + w)⁻¹) := by
    unfold quadrantVelocity
    simp only [inv_neg] at e2 e4 ⊢
    linear_combination (-(1 / 2) : ℂ) * e1 - (-(1 / 2) : ℂ) * e2 - (-(1 / 2) : ℂ) * e3 +
      (-(1 / 2) : ℂ) * e4
  rw [key, norm_mul, show ‖(-(1 / 2) : ℂ)‖ = 1 / 2 by norm_num]
  have b1 := norm_remainder_le n1 h
  have b2 := norm_remainder_le (z := z) n2 h
  have b3 := norm_remainder_le (z := z) n3 h
  have b4 := norm_remainder_le (z := z) n4 h
  rw [sub_neg_eq_add] at b2 b4
  calc 1 / 2 * ‖z ^ 5 * w⁻¹ ^ 5 * (z - w)⁻¹ - z ^ 5 * (-conj w)⁻¹ ^ 5 * (z + conj w)⁻¹ -
        z ^ 5 * (conj w)⁻¹ ^ 5 * (z - conj w)⁻¹ + z ^ 5 * (-w)⁻¹ ^ 5 * (z + w)⁻¹‖
      ≤ 1 / 2 * (‖z ^ 5 * w⁻¹ ^ 5 * (z - w)⁻¹‖ + ‖z ^ 5 * (-conj w)⁻¹ ^ 5 * (z + conj w)⁻¹‖ +
        ‖z ^ 5 * (conj w)⁻¹ ^ 5 * (z - conj w)⁻¹‖ + ‖z ^ 5 * (-w)⁻¹ ^ 5 * (z + w)⁻¹‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ 1 / 2 * (4 * (‖z‖ ^ 5 / (‖w‖ ^ 5 * (‖w‖ - ‖z‖)))) := by gcongr; linarith
    _ = 2 * ‖z‖ ^ 5 / (‖w‖ ^ 5 * (‖w‖ - ‖z‖)) := by ring

/-- `|w⁻⁴ - w̄⁻⁴| ≤ 2 / |w|⁴`. -/
theorem norm_inv_pow_four_sub_le (w : ℂ) :
    ‖w⁻¹ ^ 4 - (conj w)⁻¹ ^ 4‖ ≤ 2 / ‖w‖ ^ 4 := by
  calc ‖w⁻¹ ^ 4 - (conj w)⁻¹ ^ 4‖ ≤ ‖w⁻¹ ^ 4‖ + ‖(conj w)⁻¹ ^ 4‖ := norm_sub_le _ _
    _ = 2 / ‖w‖ ^ 4 := by simp [norm_inv]; ring

/-! ### Derivatives along lines -/

/-- The derivative of `ξ ↦ c (a + ξ d)⁻ⁿ`: `-n c d (a + ξ d)⁻⁽ⁿ⁺¹⁾`. -/
theorem hasDerivAt_mul_inv_pow_line (c a d : ℂ) (n : ℕ) {ζ : ℂ} (h : a + ζ * d ≠ 0) :
    HasDerivAt (fun ξ : ℂ ↦ c * ((a + ξ * d) ^ n)⁻¹)
      (-(n : ℂ) * c * d * ((a + ζ * d) ^ (n + 1))⁻¹) ζ := by
  have hg : HasDerivAt (fun ξ : ℂ ↦ a + ξ * d) d ζ := by
    simpa using ((hasDerivAt_id ζ).mul_const d).const_add a
  have hz := hasDerivAt_zpow (-(n : ℤ)) (a + ζ * d) (Or.inl h)
  have hc := (hz.comp ζ hg).const_mul c
  have e1 : (fun ξ : ℂ ↦ c * ((a + ξ * d) ^ n)⁻¹) =
      fun ξ ↦ c * ((fun u : ℂ ↦ u ^ (-(n : ℤ))) ∘ fun ξ ↦ a + ξ * d) ξ := by
    funext ξ
    simp [zpow_neg, zpow_natCast]
  rw [e1]
  convert hc using 1
  have e2 : (a + ζ * d) ^ (-(n : ℤ) - 1) = ((a + ζ * d) ^ (n + 1))⁻¹ := by
    rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [e2]
  push_cast
  ring

/-- **Derivative along a real line.** For `z₀ + t d ≠ 0`,
`d/ds Re(c (z₀ + s d)⁻ⁿ) = Re(-n c d (z₀ + s d)⁻⁽ⁿ⁺¹⁾)` at `s = t`. -/
theorem hasDerivAt_re_mul_inv_pow_line (c z₀ d : ℂ) (n : ℕ) {t : ℝ} (h : z₀ + t * d ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (c * ((z₀ + s * d) ^ n)⁻¹).re)
      ((-(n : ℂ) * c * d * ((z₀ + t * d) ^ (n + 1))⁻¹).re) t :=
  (hasDerivAt_mul_inv_pow_line c z₀ d n h).real_of_complex

/-- The four images `w, -w̄, w̄, -w` of a source point. -/
def quadrantImage (w : ℂ) : Fin 4 → ℂ :=
  ![w, -conj w, conj w, -w]

/-- The signs `+, -, -, +` of the four images. -/
def quadrantSign : Fin 4 → ℂ :=
  ![1, -1, -1, 1]

/-- `V(z, w) = -(1/2) Σₖ σₖ (z - uₖ)⁻¹` over the images `uₖ` with the signs `σₖ`. -/
theorem quadrantVelocity_eq_sum (z w : ℂ) :
    quadrantVelocity z w = -(1 / 2) * ∑ k, quadrantSign k * (z - quadrantImage w k)⁻¹ := by
  simp only [quadrantVelocity, Fin.sum_univ_four, quadrantSign, quadrantImage]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_neg_eq_add]
  ring

/-- The images have the norm of the source. -/
theorem norm_quadrantImage (w : ℂ) (k : Fin 4) : ‖quadrantImage w k‖ = ‖w‖ := by
  fin_cases k <;> simp [quadrantImage]

/-- The signs have norm one. -/
theorem norm_quadrantSign (k : Fin 4) : ‖quadrantSign k‖ = 1 := by
  fin_cases k <;> simp [quadrantSign]

/-- A finite signed sum of inverse powers along a line has the termwise derivative. -/
private theorem hasDerivAt_sum_inv_pow (c : ℂ) (σ a : Fin 4 → ℂ) (e : Fin 4 → ℂ) (n : ℕ)
    {ζ : ℂ} (h : ∀ k, a k + ζ * e k ≠ 0) :
    HasDerivAt (fun ξ : ℂ ↦ c * ∑ k, σ k * ((a k + ξ * e k) ^ n)⁻¹)
      (-(n : ℂ) * c * ∑ k, σ k * e k * ((a k + ζ * e k) ^ (n + 1))⁻¹) ζ := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    hasDerivAt_mul_inv_pow_line (c * σ k) (a k) (e k) n (h k))
  convert hs using 1
  · funext ξ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- `|Re(c Σₖ σₖ eₖ² (aₖ)⁻³)| ≤ |c| Σₖ |eₖ|² / |aₖ|³` for unit signs. -/
private theorem abs_re_sum_le (c : ℂ) (σ a e : Fin 4 → ℂ) (hσ : ∀ k, ‖σ k‖ = 1) (m n : ℕ) :
    |(c * ∑ k, σ k * e k ^ m * ((a k) ^ n)⁻¹).re| ≤ ‖c‖ * ∑ k, ‖e k‖ ^ m / ‖a k‖ ^ n := by
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ ↦ ?_))
  rw [norm_mul, norm_mul, hσ, norm_pow, norm_inv, norm_pow, one_mul, div_eq_mul_inv]

/-- The first derivative of `Re(c V(z + s d, w))` in `s`, the target moving along `d`:
`Re((c/2) d Σₖ σₖ (z + s d - uₖ)⁻²)`. -/
def quadrantVelocityTargetDeriv (c z w d : ℂ) (s : ℝ) : ℂ :=
  c * (1 / 2) * d * ∑ k, quadrantSign k * ((z + s * d - quadrantImage w k) ^ 2)⁻¹

/-- The second derivative of `Re(c V(z + s d, w))` in `s`:
`Re(-c d² Σₖ σₖ (z + s d - uₖ)⁻³)`. -/
def quadrantVelocityTargetSecond (c z w d : ℂ) (s : ℝ) : ℂ :=
  -(c * d ^ 2 * ∑ k, quadrantSign k * ((z + s * d - quadrantImage w k) ^ 3)⁻¹)

/-- **The target moving along a line.** If `z + t d` is none of the images of `w`, then
`s ↦ Re(c V(z + s d, w))` has the derivative `Re(quadrantVelocityTargetDeriv c z w d t)` at `t`,
and that derivative has the derivative `Re(quadrantVelocityTargetSecond c z w d t)`. -/
theorem hasDerivAt_quadrantVelocity_target (c z w d : ℂ) {t : ℝ}
    (h : ∀ k, z + t * d - quadrantImage w k ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (c * quadrantVelocity (z + s * d) w).re)
        (quadrantVelocityTargetDeriv c z w d t).re t ∧
      HasDerivAt (fun s : ℝ ↦ (quadrantVelocityTargetDeriv c z w d s).re)
        (quadrantVelocityTargetSecond c z w d t).re t := by
  have h' : ∀ k, (z - quadrantImage w k) + (t : ℂ) * d ≠ 0 := fun k ↦ by
    convert h k using 1; ring
  constructor
  · have hd := hasDerivAt_sum_inv_pow (c * (-(1 / 2))) quadrantSign
      (fun k ↦ z - quadrantImage w k) (fun _ ↦ d) 1 h'
    have e : (fun s : ℝ ↦ (c * quadrantVelocity (z + s * d) w).re) =
        fun s : ℝ ↦ ((fun ξ : ℂ ↦ c * (-(1 / 2)) *
          ∑ k, quadrantSign k * (((z - quadrantImage w k) + ξ * d) ^ 1)⁻¹) s).re := by
      funext s
      change (c * quadrantVelocity (z + s * d) w).re = (c * -(1 / 2) *
        ∑ k, quadrantSign k * (((z - quadrantImage w k) + (s : ℂ) * d) ^ 1)⁻¹).re
      rw [quadrantVelocity_eq_sum, ← mul_assoc]
      congr 2
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [pow_one]
      congr 2
      ring
    rw [e]
    convert hd.real_of_complex using 2
    simp only [quadrantVelocityTargetDeriv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring_nf
  · have hd := hasDerivAt_sum_inv_pow (c * (1 / 2) * d) quadrantSign
      (fun k ↦ z - quadrantImage w k) (fun _ ↦ d) 2 h'
    have e : (fun s : ℝ ↦ (quadrantVelocityTargetDeriv c z w d s).re) =
        fun s : ℝ ↦ ((fun ξ : ℂ ↦ c * (1 / 2) * d *
          ∑ k, quadrantSign k * (((z - quadrantImage w k) + ξ * d) ^ 2)⁻¹) s).re := by
      funext s
      simp only [quadrantVelocityTargetDeriv]
      congr 2
      exact Finset.sum_congr rfl fun k _ ↦ by congr 3; ring
    rw [e]
    convert hd.real_of_complex using 2
    simp only [quadrantVelocityTargetSecond, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring_nf

/-- `|Re(quadrantVelocityTargetSecond c z w d t)| ≤ |c| |d|² Σₖ |z + t d - uₖ|⁻³`. -/
theorem abs_quadrantVelocity_target_second_le (c z w d : ℂ) (t : ℝ) :
    |(quadrantVelocityTargetSecond c z w d t).re| ≤
      ‖c‖ * ‖d‖ ^ 2 * ∑ k, 1 / ‖z + t * d - quadrantImage w k‖ ^ 3 := by
  have h := abs_re_sum_le (-c) quadrantSign (fun k ↦ z + t * d - quadrantImage w k)
    (fun _ ↦ d) norm_quadrantSign 2 3
  have e : quadrantVelocityTargetSecond c z w d t =
      -c * ∑ k, quadrantSign k * d ^ 2 * ((z + t * d - quadrantImage w k) ^ 3)⁻¹ := by
    simp only [quadrantVelocityTargetSecond, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [norm_neg, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The directions in which `z - uₖ` moves when the source moves along `d` (real parameter):
`-d, d̄, -d̄, d`. -/
def quadrantSourceDir (d : ℂ) : Fin 4 → ℂ :=
  ![-d, conj d, -conj d, d]

/-- For a real parameter `s`, `z - uₖ(w + s d) = (z - uₖ(w)) + s eₖ` with the directions
`quadrantSourceDir d`. -/
theorem sub_quadrantImage_add (z w d : ℂ) (s : ℝ) (k : Fin 4) :
    z - quadrantImage (w + s * d) k = (z - quadrantImage w k) + s * quadrantSourceDir d k := by
  fin_cases k <;> simp [quadrantImage, quadrantSourceDir] <;> ring

/-- The image directions have the norm of the source direction. -/
theorem norm_quadrantSourceDir (d : ℂ) (k : Fin 4) : ‖quadrantSourceDir d k‖ = ‖d‖ := by
  fin_cases k <;> simp [quadrantSourceDir]

/-- The first derivative of `Re(c V(z, w + s d))` in `s`, the source moving along `d`:
`Re((c/2) Σₖ σₖ eₖ (z - uₖ(w + s d))⁻²)`. -/
def quadrantVelocitySourceDeriv (c z w d : ℂ) (s : ℝ) : ℂ :=
  c * (1 / 2) * ∑ k, quadrantSign k * quadrantSourceDir d k *
    ((z - quadrantImage (w + s * d) k) ^ 2)⁻¹

/-- The second derivative of `Re(c V(z, w + s d))` in `s`:
`Re(-c Σₖ σₖ eₖ² (z - uₖ(w + s d))⁻³)`. -/
def quadrantVelocitySourceSecond (c z w d : ℂ) (s : ℝ) : ℂ :=
  -(c * ∑ k, quadrantSign k * quadrantSourceDir d k ^ 2 *
    ((z - quadrantImage (w + s * d) k) ^ 3)⁻¹)

/-- **The source moving along a line.** If `z` is none of the images of `w + t d`, then
`s ↦ Re(c V(z, w + s d))` has the derivative `Re(quadrantVelocitySourceDeriv c z w d t)` at `t`,
and that derivative has the derivative `Re(quadrantVelocitySourceSecond c z w d t)`. -/
theorem hasDerivAt_quadrantVelocity_source (c z w d : ℂ) {t : ℝ}
    (h : ∀ k, z - quadrantImage (w + t * d) k ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (c * quadrantVelocity z (w + s * d)).re)
        (quadrantVelocitySourceDeriv c z w d t).re t ∧
      HasDerivAt (fun s : ℝ ↦ (quadrantVelocitySourceDeriv c z w d s).re)
        (quadrantVelocitySourceSecond c z w d t).re t := by
  have h' : ∀ k, (z - quadrantImage w k) + (t : ℂ) * quadrantSourceDir d k ≠ 0 := fun k ↦ by
    rw [← sub_quadrantImage_add]; exact h k
  constructor
  · have hd := hasDerivAt_sum_inv_pow (c * (-(1 / 2))) quadrantSign
      (fun k ↦ z - quadrantImage w k) (quadrantSourceDir d) 1 h'
    have e : (fun s : ℝ ↦ (c * quadrantVelocity z (w + s * d)).re) =
        fun s : ℝ ↦ ((fun ξ : ℂ ↦ c * (-(1 / 2)) *
          ∑ k, quadrantSign k * (((z - quadrantImage w k) + ξ * quadrantSourceDir d k) ^ 1)⁻¹)
            s).re := by
      funext s
      change (c * quadrantVelocity z (w + s * d)).re = (c * -(1 / 2) * ∑ k, quadrantSign k *
        (((z - quadrantImage w k) + (s : ℂ) * quadrantSourceDir d k) ^ 1)⁻¹).re
      rw [quadrantVelocity_eq_sum, ← mul_assoc]
      congr 2
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [pow_one, sub_quadrantImage_add]
    rw [e]
    convert hd.real_of_complex using 2
    simp only [quadrantVelocitySourceDeriv, Finset.mul_sum, sub_quadrantImage_add]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring_nf
  · have hd := hasDerivAt_sum_inv_pow (c * (1 / 2))
      (fun k ↦ quadrantSign k * quadrantSourceDir d k)
      (fun k ↦ z - quadrantImage w k) (quadrantSourceDir d) 2 h'
    have e : (fun s : ℝ ↦ (quadrantVelocitySourceDeriv c z w d s).re) =
        fun s : ℝ ↦ ((fun ξ : ℂ ↦ c * (1 / 2) * ∑ k, quadrantSign k * quadrantSourceDir d k *
          (((z - quadrantImage w k) + ξ * quadrantSourceDir d k) ^ 2)⁻¹) s).re := by
      funext s
      simp only [quadrantVelocitySourceDeriv, sub_quadrantImage_add]
    rw [e]
    convert hd.real_of_complex using 2
    simp only [quadrantVelocitySourceSecond, Finset.mul_sum, ← Finset.sum_neg_distrib,
      sub_quadrantImage_add]
    exact Finset.sum_congr rfl fun k _ ↦ by push_cast; ring_nf

/-- `|Re(quadrantVelocitySourceSecond c z w d t)| ≤ |c| |d|² Σₖ |z - uₖ(w + t d)|⁻³`. -/
theorem abs_quadrantVelocity_source_second_le (c z w d : ℂ) (t : ℝ) :
    |(quadrantVelocitySourceSecond c z w d t).re| ≤
      ‖c‖ * ‖d‖ ^ 2 * ∑ k, 1 / ‖z - quadrantImage (w + t * d) k‖ ^ 3 := by
  have h := abs_re_sum_le (-c) quadrantSign (fun k ↦ z - quadrantImage (w + t * d) k)
    (quadrantSourceDir d) norm_quadrantSign 2 3
  have e : quadrantVelocitySourceSecond c z w d t =
      -c * ∑ k, quadrantSign k * quadrantSourceDir d k ^ 2 *
        ((z - quadrantImage (w + t * d) k) ^ 3)⁻¹ := by
    simp only [quadrantVelocitySourceSecond, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [norm_neg, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [norm_quadrantSourceDir]; ring

/-! ### The strain term along a line -/

/-- **The strain term along a line.** For `w + t d ≠ 0`, `s ↦ Re(c z (w + s d)⁻²)` has the
derivative `Re(-2 c z d (w + t d)⁻³)` at `t`, and `s ↦ Re(-2 c z d (w + s d)⁻³)` has the
derivative `Re(6 c z d² (w + t d)⁻⁴)`. -/
theorem hasDerivAt_strainTerm_line (c z w d : ℂ) {t : ℝ} (h : w + t * d ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (c * z * ((w + s * d) ^ 2)⁻¹).re)
        ((-2 * c * z * d * ((w + t * d) ^ 3)⁻¹).re) t ∧
      HasDerivAt (fun s : ℝ ↦ (-2 * c * z * d * ((w + s * d) ^ 3)⁻¹).re)
        ((6 * c * z * d ^ 2 * ((w + t * d) ^ 4)⁻¹).re) t := by
  constructor
  · convert hasDerivAt_re_mul_inv_pow_line (c * z) w d 2 h using 2
    push_cast; ring
  · convert hasDerivAt_re_mul_inv_pow_line (-2 * c * z * d) w d 3 h using 2
    push_cast; ring

/-- `|Re(6 c z d² (w + t d)⁻⁴)| ≤ 6 |c| |z| |d|² / |w + t d|⁴`. -/
theorem abs_strainTerm_second_le (c z w d : ℂ) (t : ℝ) :
    |(6 * c * z * d ^ 2 * ((w + t * d) ^ 4)⁻¹).re| ≤
      6 * ‖c‖ * ‖z‖ * ‖d‖ ^ 2 / ‖w + t * d‖ ^ 4 := by
  refine (abs_re_le_norm _).trans (le_of_eq ?_)
  simp only [norm_mul, norm_pow, norm_inv, RCLike.norm_ofNat]
  ring

/-! ### The cancelled second-order kernel -/

/-- `(z - w)⁻³ + (z + w)⁻³ + 6 z w⁻⁴`: the second derivative in `w` of the pair of images
`w, -w` of the quadrant velocity with the strain part removed, up to the factor `-d²`. -/
def cancelledKernel (z w : ℂ) : ℂ :=
  ((z - w) ^ 3)⁻¹ + ((z + w) ^ 3)⁻¹ + 6 * z * (w ^ 4)⁻¹

/-- Off the poles `z = ±w`, `w ≠ 0`, the cancelled kernel is `z³ (6z⁴ - 18z²w² + 20w⁴)/(w⁴ (z² -
w²)³)`, so it vanishes to third order in `z`. -/
theorem cancelledKernel_eq (z w : ℂ) (hw : w ≠ 0) (h1 : z - w ≠ 0) (h2 : z + w ≠ 0) :
    ((z - w) ^ 3)⁻¹ + ((z + w) ^ 3)⁻¹ + 6 * z * (w ^ 4)⁻¹ =
      z ^ 3 * (6 * z ^ 4 - 18 * z ^ 2 * w ^ 2 + 20 * w ^ 4) / (w ^ 4 * (z ^ 2 - w ^ 2) ^ 3) := by
  have h3 : z ^ 2 - w ^ 2 ≠ 0 := by
    rw [show z ^ 2 - w ^ 2 = (z - w) * (z + w) by ring]; exact mul_ne_zero h1 h2
  field_simp
  ring

/-- For `|z| < |w|`, `|cancelledKernel z w| ≤ |z|³ (6ρ² + 18ρ + 20)/(|w|² - |z|²)³` with `ρ =
|z|²/|w|²`. -/
theorem norm_cancelledKernel_le {z w : ℂ} (h : ‖z‖ < ‖w‖) :
    ‖cancelledKernel z w‖ ≤
      ‖z‖ ^ 3 * (6 * (‖z‖ ^ 2 / ‖w‖ ^ 2) ^ 2 + 18 * (‖z‖ ^ 2 / ‖w‖ ^ 2) + 20) /
        (‖w‖ ^ 2 - ‖z‖ ^ 2) ^ 3 := by
  have hw0 : 0 < ‖w‖ := (norm_nonneg z).trans_lt h
  have hw : w ≠ 0 := norm_pos_iff.mp hw0
  have h1 : z - w ≠ 0 := by
    intro h0; rw [sub_eq_zero] at h0; rw [h0] at h; exact lt_irrefl _ h
  have h2 : z + w ≠ 0 := by
    intro h0; rw [add_eq_zero_iff_eq_neg] at h0; rw [h0, norm_neg] at h; exact lt_irrefl _ h
  rw [cancelledKernel, cancelledKernel_eq z w hw h1 h2]
  have hd : ‖w‖ ^ 2 - ‖z‖ ^ 2 ≤ ‖z ^ 2 - w ^ 2‖ := by
    have := norm_sub_norm_le (w ^ 2) (z ^ 2)
    rw [norm_pow, norm_pow, norm_sub_rev] at this
    exact this
  have hd0 : 0 < ‖w‖ ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hn : ‖6 * z ^ 4 - 18 * z ^ 2 * w ^ 2 + 20 * w ^ 4‖ ≤
      6 * ‖z‖ ^ 4 + 18 * ‖z‖ ^ 2 * ‖w‖ ^ 2 + 20 * ‖w‖ ^ 4 := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans (le_of_eq ?_)
    simp only [norm_mul, norm_pow, RCLike.norm_ofNat]
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  have hz0 := norm_nonneg z
  rw [div_le_div_iff₀ (mul_pos (by positivity) (pow_pos (hd0.trans_le hd) 3)) (pow_pos hd0 3)]
  have e1 : ‖w‖ ^ 4 * (‖w‖ ^ 2 - ‖z‖ ^ 2) ^ 3 ≤ ‖w‖ ^ 4 * ‖z ^ 2 - w ^ 2‖ ^ 3 := by
    gcongr
  have key : (6 * (‖z‖ ^ 2 / ‖w‖ ^ 2) ^ 2 + 18 * (‖z‖ ^ 2 / ‖w‖ ^ 2) + 20) * ‖w‖ ^ 4 =
      6 * ‖z‖ ^ 4 + 18 * ‖z‖ ^ 2 * ‖w‖ ^ 2 + 20 * ‖w‖ ^ 4 := by
    field_simp
  calc ‖z‖ ^ 3 * ‖6 * z ^ 4 - 18 * z ^ 2 * w ^ 2 + 20 * w ^ 4‖ * (‖w‖ ^ 2 - ‖z‖ ^ 2) ^ 3
      ≤ ‖z‖ ^ 3 * (6 * ‖z‖ ^ 4 + 18 * ‖z‖ ^ 2 * ‖w‖ ^ 2 + 20 * ‖w‖ ^ 4) *
          (‖w‖ ^ 2 - ‖z‖ ^ 2) ^ 3 := by gcongr
    _ = ‖z‖ ^ 3 * (6 * (‖z‖ ^ 2 / ‖w‖ ^ 2) ^ 2 + 18 * (‖z‖ ^ 2 / ‖w‖ ^ 2) + 20) *
          (‖w‖ ^ 4 * (‖w‖ ^ 2 - ‖z‖ ^ 2) ^ 3) := by rw [← key]; ring
    _ ≤ ‖z‖ ^ 3 * (6 * (‖z‖ ^ 2 / ‖w‖ ^ 2) ^ 2 + 18 * (‖z‖ ^ 2 / ‖w‖ ^ 2) + 20) *
          (‖w‖ ^ 4 * ‖z ^ 2 - w ^ 2‖ ^ 3) := by gcongr

end GreenFunction
