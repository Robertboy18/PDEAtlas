/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessian

/-!
# Taylor expansion of the strain kernel away from the origin

The strain kernel `K₁(z) = z₁ z₂/|z|⁴ = -Im (1/(2 z²))` (`hessianKernel_zero_one_eq_neg_im`) is the
imaginary part of a holomorphic function, so its Taylor expansion about a point `c ≠ 0` comes from
the binomial series `(1 + ζ)⁻² = ∑_m (m + 1) (-ζ)^m`. For `‖ζ‖ ≤ ρ < 1` the remainder after the
terms `m ≤ n` is at most `∑_{m > n} (m + 1) ρ^m = ρ^(n+1) ((n + 2) - (n + 1) ρ)/(1 - ρ)²`, and for
`c ≠ 0` and `‖w‖ ≤ ρ ‖c‖` the same bound, multiplied by `‖c‖⁻²`, holds for
`(c + w)⁻² - ∑_{m ≤ n} (m + 1) (-1)^m w^m c^{-(m+2)}`.

On a rectangle with centre `c` and half-diagonal `d ≤ ρ |c|` the kernel is therefore a polynomial
of degree `n` in `z - c` up to `‖c‖⁻² ∑_{m > n} (m + 1) ρ^m / 2`, which turns its integrals against
polynomials into moment sums.

## Main definitions

* `inverseSquareTaylor`: the Taylor polynomial `∑_{m ≤ n} (m + 1) (-ζ)^m` of `(1 + ζ)⁻²`.
* `inverseSquareTail`: the tail `∑_{m > n} (m + 1) ρ^m` in closed form.
* `strainTaylor`: the Taylor polynomial of order `n` of `K₁` about `c ≠ 0`, in the scaled
  coordinates `ξ = (y₀ - Re c)/h₁`, `η = (y₁ - Im c)/h₂`.

## Main results

* `hasSum_inverseSquare`: the binomial series of `(1 + ζ)⁻²`.
* `norm_inv_one_add_sq_sub_le`: the tail of the binomial series is at most `inverseSquareTail` for
  `‖ζ‖ ≤ ρ < 1`.
* `norm_inv_add_sq_sub_le`: for `‖w‖ ≤ ρ ‖c‖` and `ρ < 1`,
  `‖(c + w)⁻² - ∑_{m ≤ n} (m + 1) (-1)^m w^m c^{-(m+2)}‖ ≤ ‖c‖⁻² ∑_{m > n} (m + 1) ρ^m`.
* `abs_hessianKernel_zero_one_sub_strainTaylor_le`: for `c ≠ 0` and `|y - c| ≤ ρ |c|` with
  `ρ < 1`, `|K₁(y) - T_n(y)| ≤ |c|⁻² ∑_{m > n} (m + 1) ρ^m / 2`.
-/

@[expose] public section

noncomputable section

open Finset

namespace PotentialTheory.Planar

/-- The Taylor polynomial `∑_{m ≤ n} (m + 1) (-ζ)^m` of `ζ ↦ (1 + ζ)⁻²`. -/
def inverseSquareTaylor (n : ℕ) (ζ : ℂ) : ℂ :=
  ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℂ) * (-ζ) ^ m

/-- The tail `∑_{m > n} (m + 1) ρ^m = ρ^(n+1) ((n + 2) - (n + 1) ρ)/(1 - ρ)²`. -/
def inverseSquareTail (n : ℕ) (ρ : ℝ) : ℝ :=
  ρ ^ (n + 1) * ((n + 2) - (n + 1) * ρ) / (1 - ρ) ^ 2

/-- The partial sums of `∑ (m + 1) ρ^m` in closed form. -/
theorem sum_range_succ_mul_pow (ρ : ℝ) (hρ : ρ ≠ 1) (n : ℕ) :
    ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℝ) * ρ ^ m =
      (1 - (n + 2) * ρ ^ (n + 1) + (n + 1) * ρ ^ (n + 2)) / (1 - ρ) ^ 2 := by
  have h1 : (1 - ρ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hρ))
  rw [eq_div_iff h1]
  induction n with
  | zero => simp; ring
  | succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

/-- The binomial series of `(1 + ζ)⁻²`. -/
theorem hasSum_inverseSquare {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasSum (fun m : ℕ ↦ ((m + 1 : ℕ) : ℂ) * (-ζ) ^ m) (((1 + ζ) ^ 2)⁻¹) := by
  simpa only [Nat.choose_one_right, one_div, sub_neg_eq_add] using
    hasSum_choose_mul_geometric_of_norm_lt_one 1 (r := -ζ) (by rwa [norm_neg])

/-- The tail bound of the binomial series `(1 + ζ)⁻²` for `‖ζ‖ ≤ ρ < 1`. -/
theorem norm_inv_one_add_sq_sub_le {ζ : ℂ} {ρ : ℝ} (hζ : ‖ζ‖ ≤ ρ) (hρ : ρ < 1) (n : ℕ) :
    ‖((1 + ζ) ^ 2)⁻¹ - inverseSquareTaylor n ζ‖ ≤ inverseSquareTail n ρ := by
  have hζ1 : ‖ζ‖ < 1 := hζ.trans_lt hρ
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hζ
  have hs := hasSum_inverseSquare hζ1
  have htail := (hasSum_nat_add_iff' (n + 1)).mpr hs
  have hr : HasSum (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * ρ ^ m) ((1 - ρ) ^ 2)⁻¹ := by
    simpa only [Nat.choose_one_right, one_div] using
      hasSum_choose_mul_geometric_of_norm_lt_one 1 (r := ρ) (by rwa [Real.norm_of_nonneg hρ0])
  have hrtail := (hasSum_nat_add_iff' (n + 1)).mpr hr
  have hbound : ∀ m, ‖((m + (n + 1) + 1 : ℕ) : ℂ) * (-ζ) ^ (m + (n + 1))‖ ≤
      ((m + (n + 1) + 1 : ℕ) : ℝ) * ρ ^ (m + (n + 1)) := by
    intro m
    rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
    gcongr
  have hle := htail.norm_le_of_bounded hrtail hbound
  have heq : ((1 + ζ) ^ 2)⁻¹ - ∑ i ∈ range (n + 1), ((i + 1 : ℕ) : ℂ) * (-ζ) ^ i =
      ((1 + ζ) ^ 2)⁻¹ - inverseSquareTaylor n ζ := rfl
  rw [heq] at hle
  refine hle.trans (le_of_eq ?_)
  rw [sum_range_succ_mul_pow ρ hρ.ne n, inverseSquareTail]
  have hne : (1 - ρ) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  field_simp
  ring

/-- **The Taylor expansion of `(c + w)⁻²`** about `c ≠ 0`: for `‖w‖ ≤ ρ ‖c‖` and `ρ < 1`,
`‖(c + w)⁻² - ∑_{m ≤ n} (m + 1) (-1)^m w^m c^{-(m+2)}‖ ≤ ‖c‖⁻² ∑_{m > n} (m + 1) ρ^m`. -/
theorem norm_inv_add_sq_sub_le {c w : ℂ} (hc : c ≠ 0) {ρ : ℝ} (hw : ‖w‖ ≤ ρ * ‖c‖)
    (hρ : ρ < 1) (n : ℕ) :
    ‖((c + w) ^ 2)⁻¹ - ∑ m ∈ range (n + 1),
        ((m + 1 : ℕ) : ℂ) * (-1) ^ m * w ^ m * ((c ^ (m + 2))⁻¹)‖ ≤
      (‖c‖ ^ 2)⁻¹ * inverseSquareTail n ρ := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hζ : ‖w / c‖ ≤ ρ := by
    rw [norm_div, div_le_iff₀ hcn]
    exact hw
  have h := norm_inv_one_add_sq_sub_le hζ hρ n
  have hsplit : ((c + w) ^ 2)⁻¹ - ∑ m ∈ range (n + 1),
      ((m + 1 : ℕ) : ℂ) * (-1) ^ m * w ^ m * ((c ^ (m + 2))⁻¹) =
      ((c ^ 2)⁻¹) * (((1 + w / c) ^ 2)⁻¹ - inverseSquareTaylor n (w / c)) := by
    have hcw : c + w = c * (1 + w / c) := by field_simp
    rw [hcw, mul_pow, mul_inv, mul_sub, inverseSquareTaylor, mul_sum]
    congr 1
    apply sum_congr rfl
    intro m _
    rw [neg_eq_neg_one_mul (w / c), mul_pow, div_pow, pow_add]
    field_simp
  rw [hsplit, norm_mul, norm_inv, norm_pow]
  gcongr

end PotentialTheory.Planar

namespace PotentialTheory.Planar

/-- The Taylor polynomial of order `n` of `K₁ = hessianKernel 0 1` about `c ≠ 0`, in the scaled
coordinates `ξ = (y₀ - Re c)/h₁`, `η = (y₁ - Im c)/h₂`:
`-Im ∑_{m ≤ n} (m + 1) (-1)^m (h₁ ξ + i h₂ η)^m c^{-(m+2)} / 2`. -/
def strainTaylor (c : ℂ) (h₁ h₂ : ℝ) (n : ℕ) (ξ η : ℝ) : ℝ :=
  -(∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℂ) * (-1) ^ m *
      ((h₁ * ξ : ℝ) + Complex.I * (h₂ * η : ℝ)) ^ m * ((c ^ (m + 2))⁻¹)).im / 2

/-- **The Taylor bound of the strain kernel**: for `c ≠ 0` and `|y - c| ≤ ρ |c|` with `ρ < 1`,
`|K₁(y) - T_n(y)| ≤ |c|⁻² ∑_{m > n} (m + 1) ρ^m / 2`. -/
theorem abs_hessianKernel_zero_one_sub_strainTaylor_le {c : ℂ} (hc : c ≠ 0) {h₁ h₂ ρ : ℝ}
    (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (n : ℕ) {y : ℝ^2}
    (hy : (y 0 - c.re) ^ 2 + (y 1 - c.im) ^ 2 ≤ ρ ^ 2 * ‖c‖ ^ 2) :
    |hessianKernel 0 1 y -
        strainTaylor c h₁ h₂ n ((y 0 - c.re) / h₁) ((y 1 - c.im) / h₂)| ≤
      (‖c‖ ^ 2)⁻¹ * inverseSquareTail n ρ / 2 := by
  have hre := orthonormalBasisOneI_repr_symm_re y
  have him := orthonormalBasisOneI_repr_symm_im y
  set z := Complex.orthonormalBasisOneI.repr.symm y
  set w : ℂ := ⟨y 0 - c.re, y 1 - c.im⟩ with hw
  have hzw : z = c + w := by
    apply Complex.ext <;> simp [hre, him, w]
  have hwn : ‖w‖ ≤ ρ * ‖c‖ := by
    have h2 : ‖w‖ ^ 2 ≤ (ρ * ‖c‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow]
      simp only [w]
      nlinarith
    nlinarith [norm_nonneg w, mul_nonneg hρ0 (norm_nonneg c)]
  have hsplit : ((h₁ * ((y 0 - c.re) / h₁) : ℝ) : ℂ) + Complex.I * ((h₂ * ((y 1 - c.im) / h₂) :
      ℝ) : ℂ) = w := by
    rw [mul_div_cancel₀ _ h₁0, mul_div_cancel₀ _ h₂0]
    apply Complex.ext <;> simp [w]
  rw [hessianKernel_zero_one_eq_neg_im, strainTaylor, hsplit]
  have hb := norm_inv_add_sq_sub_le hc hwn hρ n
  set S := ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℂ) * (-1) ^ m * w ^ m * ((c ^ (m + 2))⁻¹)
  have hk : (1 / (2 * z ^ 2)) = ((c + w) ^ 2)⁻¹ / 2 := by
    rw [hzw]; field_simp
  rw [hk]
  have him' : (((c + w) ^ 2)⁻¹ / 2).im = (((c + w) ^ 2)⁻¹).im / 2 := by
    simp [Complex.div_ofNat_im]
  rw [him']
  have : -((((c + w) ^ 2)⁻¹).im / 2) - -S.im / 2 = -((((c + w) ^ 2)⁻¹ - S).im) / 2 := by
    rw [Complex.sub_im]; ring
  rw [this, abs_div, abs_neg, abs_two]
  gcongr
  exact (Complex.abs_im_le_norm _).trans hb

end PotentialTheory.Planar
