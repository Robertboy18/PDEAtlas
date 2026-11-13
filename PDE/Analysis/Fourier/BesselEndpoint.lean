/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import CAS.ExactTactic

/-!
# Bessel endpoint estimate

For `s > 1` the Sobolev space `H^s(ℝ²)` embeds into `L^∞`, and the best
constant is explicit: with the Fourier normalisation
`F(x) = (2π)⁻² ∫ e^{i x·ξ} F̂(ξ) dξ` and
`‖F‖²_{H^s} = (2π)⁻² ∫ (1 + |ξ|²)^s |F̂(ξ)|² dξ`, one has
`‖F‖_∞ ≤ (2 √(π (s - 1)))⁻¹ ‖F‖_{H^s}`. The proof is the Cauchy–Schwarz
inequality in the Fourier variable against the Bessel weight `(1 + |ξ|²)^{-s}`,
whose integral over `ℝ²` is `π/(s - 1)`. This is the two-dimensional case of
the sharp `H^s ⊂ L^∞` constant of Morosi and Pizzocchero; only the upper
bound is proved here, not its optimality.

At `s = 2`, comparing the Bessel energy with the six-term Fourier derivative energy gives
the non-sharp constant `3/(2√π)` of
`PDE.Analysis.Fourier.angularFourierEndpoint_orderTwo_derivativeEnergy`.

## Main results

* `integral_Ioi_mul_one_add_sq_rpow_neg`: `∫₀^∞ r (1 + r²)^{-s} dr = 1/(2(s-1))`
  for real `s > 1`.
* `integral_prod_one_add_sq_rpow_neg`: `∫_{ℝ²} (1 + |ξ|²)^{-s} dξ = π/(s - 1)`,
  by polar coordinates.
* `norm_oscillatoryIntegral_le_sqrt_besselWeight`: the oscillatory integral
  `∫ e^{i x·ξ} F̂(ξ) dξ` is bounded by `√(π/(s-1))` times the square root of
  the weighted Fourier energy.
* `fullSpace_bessel_endpoint`: the endpoint bound
  `‖F(x)‖ ≤ (2 √(π (s-1)))⁻¹ ‖F‖_{H^s}` for every `x`, assuming the inverse
  Fourier representation of `F` and finiteness of the weighted energy.

## Implementation notes

The Fourier transform is not invoked as an operator. `fullSpace_bessel_endpoint`
takes the pair `(F, Fhat)` together with the pointwise inversion formula as a
hypothesis, so the theorem applies to any function for which that
representation has been established separately. The weighted energy enters as
an `Integrable` hypothesis on `(1 + |ξ|²)^s ‖Fhat ξ‖²`; measurability of
`Fhat` is assumed rather than derived.

The Fourier normalization is (218) of Duruisseaux, Ganeshram, George and Anandkumar and the
norm is their Bessel norm (220); `fullSpace_bessel_endpoint` is their Proposition 9, (258),
proved as in (261)-(265). They obtain the constant from their Proposition 7, the case
`d = 2`, `r = ∞` of the constant of Morosi and Pizzocchero. Evans, §5.8.5, characterizes
`H^k(ℝⁿ)` by the Fourier weight `1 + |y|^k` in Theorem 8 and defines `H^s(ℝⁿ)` for real
`s > 0` with the weight `1 + |y|^s`, in place of the Bessel weight `(1 + |ξ|^2)^(s/2)`.

## References

* C. Morosi and L. Pizzocchero, "On the constants for some Sobolev imbeddings",
  *J. Inequal. Appl.* 6 (2001), no. 6, 665-679, numbering of arXiv:math/0011141v1,
  Propositions 2.1 and 3.1, (2.4). <https://arxiv.org/abs/math/0011141v1>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, (218) and
  (220), p. 45, Appendix B.3, Proposition 7, p. 50, and Appendix B.4, Proposition 9, (258),
  and its proof, (261)-(265), p. 53. <https://arxiv.org/abs/2609.10860v2>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, p. 297, and the definition of
  `H^s(ℝⁿ)`, p. 298. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace PDE.Analysis


/--
The radial inverse Bessel-weight integral for real order `s > 1`:
`∫₀^∞ r (1 + r²)^{-s} dr = 1/(2(s-1))`. The antiderivative
`-(1 + r²)^{1-s}/(2(s-1))` tends to zero at infinity because `s > 1`; the
next theorem uses this integral in the two-dimensional polar-coordinate
calculation.
-/
theorem integral_Ioi_mul_one_add_sq_rpow_neg (s : ℝ) (hs : 1 < s) :
    (∫ r : ℝ in Set.Ioi 0, r * (1 + r ^ 2) ^ (-s)) = 1 / (2 * (s - 1)) := by
  let g : ℝ → ℝ := fun r ↦ -(1 / (2 * (s - 1))) * (1 + r ^ 2) ^ (1 - s)
  let g' : ℝ → ℝ := fun r ↦ r * (1 + r ^ 2) ^ (-s)
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt g (g' r) r := by
    intro r _hr
    dsimp only [g, g']
    cas
  have hpos : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ g' r := by
    intro r hr
    exact mul_nonneg hr.le (Real.rpow_nonneg (by positivity) _)
  have hbaseTop : Tendsto (fun r : ℝ ↦ 1 + r ^ 2) atTop atTop := by
    simpa [add_comm] using (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds 1))
  have hpowZero : Tendsto (fun r : ℝ ↦ (1 + r ^ 2) ^ (1 - s)) atTop (nhds 0) := by
    have hposPow : Tendsto (fun r : ℝ ↦ (1 + r ^ 2) ^ (s - 1)) atTop atTop :=
      (tendsto_rpow_atTop (sub_pos.mpr hs)).comp hbaseTop
    have hinv := tendsto_inv_atTop_zero.comp hposPow
    convert hinv using 1
    ext r
    change (1 + r ^ 2) ^ (1 - s) = ((1 + r ^ 2) ^ (s - 1))⁻¹
    rw [show 1 - s = -(s - 1) by ring, Real.rpow_neg (by positivity)]
  have hg : Tendsto g atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hpowZero) using 1
    all_goals simp
  simpa [g, g'] using
    (integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg)

/-- Exact inverse Bessel-weight integral in two dimensions:
`∫_{ℝ²} (1 + |ξ|²)^{-s} dξ = π/(s - 1)` for `s > 1`, by polar coordinates and
the radial integral above.
-/
theorem integral_prod_one_add_sq_rpow_neg (s : ℝ) (hs : 1 < s) :
    (∫ p : ℝ × ℝ, (1 + p.1 ^ 2 + p.2 ^ 2) ^ (-s)) = Real.pi / (s - 1) := by
  rw [← integral_comp_polarCoord_symm]
  change (∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
    p.1 * (1 + (p.1 * Real.cos p.2) ^ 2 +
      (p.1 * Real.sin p.2) ^ 2) ^ (-s)) = Real.pi / (s - 1)
  calc
    (∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 * (1 + (p.1 * Real.cos p.2) ^ 2 +
        (p.1 * Real.sin p.2) ^ 2) ^ (-s)) =
        ∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (p.1 * (1 + p.1 ^ 2) ^ (-s)) * 1 := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p _hp
      dsimp
      rw [mul_one]
      congr 2
      nlinarith [Real.cos_sq_add_sin_sq p.2]
    _ = (∫ r : ℝ in Set.Ioi 0, r * (1 + r ^ 2) ^ (-s)) *
          ∫ _theta : ℝ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      exact setIntegral_prod_mul
        (fun r : ℝ ↦ r * (1 + r ^ 2) ^ (-s)) (fun _theta : ℝ ↦ (1 : ℝ))
        (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)
    _ = Real.pi / (s - 1) := by
      rw [integral_Ioi_mul_one_add_sq_rpow_neg s hs]
      simp [Real.pi_pos.le]
      field_simp [sub_ne_zero.mpr hs.ne']
      ring

/-- Weighted Cauchy–Schwarz for the arbitrary-order inverse Fourier integral:
writing `|Fhat| = w^{-s/2} · w^{s/2} |Fhat|` with `w = 1 + |ξ|²`, the modulus
of `∫ e^{i x·ξ} Fhat(ξ) dξ` is at most `√(π/(s-1))` times the square root of
the weighted energy `∫ w^s |Fhat|²`. The phase has modulus one, so the bound
is uniform in `x`.
-/
theorem norm_oscillatoryIntegral_le_sqrt_besselWeight
    (s : ℝ) (hs : 1 < s) (Fhat : (ℝ × ℝ) → ℂ) (x : ℝ × ℝ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun p : ℝ × ℝ ↦
      (1 + p.1 ^ 2 + p.2 ^ 2) ^ s * ‖Fhat p‖ ^ 2)) :
    ‖∫ p : ℝ × ℝ,
        Complex.exp (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p‖ ≤
      √(Real.pi / (s - 1)) *
        √(∫ p : ℝ × ℝ,
          (1 + p.1 ^ 2 + p.2 ^ 2) ^ s * ‖Fhat p‖ ^ 2) := by
  let w : ℝ × ℝ → ℝ := fun p ↦ 1 + p.1 ^ 2 + p.2 ^ 2
  let a : ℝ × ℝ → ℝ := fun p ↦ (w p) ^ (-s / 2)
  let b : ℝ × ℝ → ℝ := fun p ↦ (w p) ^ (s / 2) * ‖Fhat p‖
  have hwpos (p : ℝ × ℝ) : 0 < w p := by dsimp [w]; positivity
  have ha_sq (p : ℝ × ℝ) : a p ^ 2 = w p ^ (-s) := by
    have hw := hwpos p
    dsimp only [a]
    cas
  have hb_sq (p : ℝ × ℝ) : b p ^ 2 = w p ^ s * ‖Fhat p‖ ^ 2 := by
    have hw := hwpos p
    dsimp only [b]
    cas
  have hab (p : ℝ × ℝ) : |a p * b p| = ‖Fhat p‖ := by
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hwpos p).le _)
      (mul_nonneg (Real.rpow_nonneg (hwpos p).le _) (norm_nonneg _)))]
    rw [← mul_assoc, ← Real.rpow_add (hwpos p)]
    rw [show -s / 2 + s / 2 = 0 by ring, Real.rpow_zero, one_mul]
  have haInt : Integrable (fun p : ℝ × ℝ ↦ a p ^ 2) := by
    have hexact : (∫ p : ℝ × ℝ, a p ^ 2) = Real.pi / (s - 1) := by
      simpa [ha_sq] using integral_prod_one_add_sq_rpow_neg s hs
    exact Integrable.of_integral_ne_zero
      (hexact.trans_ne (div_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hs.ne')))
  have hbInt : Integrable (fun p : ℝ × ℝ ↦ b p ^ 2) := by
    apply hEnergy.congr
    filter_upwards [] with p
    exact (hb_sq p).symm
  have haMem : MemLp a 2 :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 haInt
  have hbMem : MemLp b 2 :=
    (memLp_two_iff_integrable_sq (by
      have hwcont : Continuous w := by fun_prop
      exact (hwcont.rpow_const (fun p ↦ Or.inl (hwpos p).ne')).aestronglyMeasurable.mul
        hFhat.norm)).2 hbInt
  have hcs := MeasureTheory.integral_abs_mul_le_sqrt_integral_sq
    (μ := volume) haMem hbMem
  calc
    ‖∫ p : ℝ × ℝ,
        Complex.exp (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p‖ ≤
        ∫ p : ℝ × ℝ, ‖Complex.exp
          (Complex.I * (x.1 * p.1 + x.2 * p.2)) * Fhat p‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ p : ℝ × ℝ, |a p * b p| := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (x.1 * p.1 + x.2 * p.2)).re = 0 := by simp
      rw [hre, Real.exp_zero, one_mul, hab]
    _ ≤ √(∫ p : ℝ × ℝ, a p ^ 2) *
        √(∫ p : ℝ × ℝ, b p ^ 2) := hcs
    _ = √(Real.pi / (s - 1)) *
        √(∫ p : ℝ × ℝ,
          (1 + p.1 ^ 2 + p.2 ^ 2) ^ s * ‖Fhat p‖ ^ 2) := by
      rw [show (∫ p : ℝ × ℝ, a p ^ 2) = Real.pi / (s - 1) by
        simpa [ha_sq] using integral_prod_one_add_sq_rpow_neg s hs]
      congr 2
      apply integral_congr_ae
      filter_upwards [] with p
      simpa [w] using hb_sq p

/-- The `H^s(ℝ²) ⊂ L^∞` endpoint estimate with the constant
`(2 √(π (s-1)))⁻¹` of Morosi and Pizzocchero: `F` is given by the inverse transform
`(2π)⁻² ∫ e^{i x·ξ} Fhat(ξ) dξ` and the `H^s` norm is the square root of
`(2π)⁻² ∫ (1 + |ξ|²)^s ‖Fhat‖²`. The inversion formula and the finiteness of
the weighted energy are hypotheses.
-/
theorem fullSpace_bessel_endpoint
    (s : ℝ) (hs : 1 < s) (F Fhat : (ℝ × ℝ) → ℂ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hEnergy : Integrable (fun ξ : ℝ × ℝ ↦
      (1 + ξ.1 ^ 2 + ξ.2 ^ 2) ^ s * ‖Fhat ξ‖ ^ 2))
    (hInverse : ∀ x,
      F x = (((2 * Real.pi) ^ 2)⁻¹ : ℂ) *
        ∫ ξ : ℝ × ℝ,
          Complex.exp (Complex.I * (x.1 * ξ.1 + x.2 * ξ.2)) * Fhat ξ) :
    ∀ x,
      ‖F x‖ ≤ (1 / (2 * √(Real.pi * (s - 1)))) *
        √(((2 * Real.pi) ^ 2)⁻¹ *
          ∫ ξ : ℝ × ℝ,
            (1 + ξ.1 ^ 2 + ξ.2 ^ 2) ^ s * ‖Fhat ξ‖ ^ 2) := by
  intro x
  let c : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  let E : ℝ := ∫ ξ : ℝ × ℝ,
    (1 + ξ.1 ^ 2 + ξ.2 ^ 2) ^ s * ‖Fhat ξ‖ ^ 2
  let I : ℂ := ∫ ξ : ℝ × ℝ,
    Complex.exp (Complex.I * (x.1 * ξ.1 + x.2 * ξ.2)) * Fhat ξ
  have hc : 0 < c := by dsimp [c]; positivity
  have hraw : ‖I‖ ≤ √(Real.pi / (s - 1)) * √E :=
    norm_oscillatoryIntegral_le_sqrt_besselWeight s hs Fhat x hFhat hEnergy
  have hsqrtc : √c = (2 * Real.pi)⁻¹ := by
    dsimp only [c]
    cas
  have hcoeff :
      c * √(Real.pi / (s - 1)) =
        (1 / (2 * √(Real.pi * (s - 1)))) * √c := by
    have hs1 : 0 < s - 1 := sub_pos.mpr hs
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul Real.pi_pos.le, hsqrtc]
    have hsp : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hss : √(s - 1) ≠ 0 := (Real.sqrt_pos.2 hs1).ne'
    have hpi : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    dsimp [c]
    field_simp [Real.pi_ne_zero, hsp, hss]
    nlinarith
  have hmain : ‖(c : ℂ) * I‖ ≤
      (1 / (2 * √(Real.pi * (s - 1)))) * √(c * E) := by
    calc
      ‖(c : ℂ) * I‖ = c * ‖I‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      _ ≤ c * (√(Real.pi / (s - 1)) * √E) :=
        mul_le_mul_of_nonneg_left hraw hc.le
      _ = (1 / (2 * √(Real.pi * (s - 1)))) * √(c * E) := by
        rw [Real.sqrt_mul hc.le, ← mul_assoc, hcoeff]
        ring
  rw [hInverse]
  simpa [c, E, I] using hmain


end PDE.Analysis
