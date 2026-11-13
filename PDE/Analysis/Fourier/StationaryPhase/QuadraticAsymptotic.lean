/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.QuadraticFourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import CAS.ExactTactic

/-!
# Leading asymptotics for diagonal quadratic phases

Fourier inversion turns the oscillatory integral into an integrable Fourier
amplitude times a multiplier converging to one. The Fresnel normalization records
the signs as well as the magnitudes of the quadratic coefficients.

`tendsto_integral_diagonal_quadratic` is Lemma 2 of Evans, §4.5.3(b), for a diagonal matrix,
with error `o(1)` in place of `O(ε)`, proved by the Fourier pairing of step 3 of his proof.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 2, (41), p. 221, and step 3 of its
  proof, pp. 222-223. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology FourierTransform SchwartzMap

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- A diagonal real quadratic phase. The coefficients are half the Hessian eigenvalues. -/
def diagonalQuadratic (b : Fin n → ℝ) (x : ℝ^n) : ℝ :=
  ∑ i, b i * x i ^ 2

/-- The Fresnel coefficient of a nondegenerate diagonal quadratic phase. -/
def diagonalFresnel (b : Fin n → ℝ) : ℂ :=
  ∏ i, (Real.sqrt (Real.pi / |b i|) : ℂ) *
    Complex.exp (Real.pi / 4 * (Real.sign (b i) : ℂ) * I)

/-- Positive rescaling preserves the sign in a Fresnel coefficient. -/
theorem diagonalFresnel_div_sq (b : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    diagonalFresnel (fun i ↦ b i / ε ^ 2) = (ε : ℂ) ^ n * diagonalFresnel b := by
  have hs (r : ℝ) : Real.sign (r / ε ^ 2) = Real.sign r := by
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [Real.sign_of_neg hr, Real.sign_of_neg (div_neg_of_neg_of_pos hr (sq_pos_of_pos hε))]
    · simp
    · rw [Real.sign_of_pos hr, Real.sign_of_pos (div_pos hr (sq_pos_of_pos hε))]
  have hroot (r : ℝ) :
      Real.sqrt (Real.pi / |r / ε ^ 2|) = ε * Real.sqrt (Real.pi / |r|) := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hε), div_div_eq_mul_div]
    rw [show Real.pi * ε ^ 2 / |r| = ε ^ 2 * (Real.pi / |r|) by cas,
      Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
  simp only [diagonalFresnel, hs, hroot, Complex.ofReal_mul, mul_assoc,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The dual quadratic multipliers converge under the integral. The multipliers
have modulus one, so for a nonintegrable amplitude both sides are zero. -/
theorem tendsto_integral_dual_quadratic {b : Fin n → ℝ} {f : ℝ^n → ℂ} :
    Tendsto (fun ε : ℝ ↦ ∫ x : ℝ^n,
      Complex.exp (-Real.pi ^ 2 * (ε : ℂ) ^ 2 *
        ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)) * f x)
      (𝓝 0) (𝓝 (∫ x, f x)) := by
  by_cases hf : Integrable f
  swap
  · rw [integral_undef hf]
    refine tendsto_const_nhds.congr fun ε ↦ (integral_undef fun hint ↦ hf ?_).symm
    have hre (x : ℝ^n) : (-((Real.pi : ℂ) ^ 2) * (ε : ℂ) ^ 2 *
        ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)).re = 0 := by
      simp [Complex.mul_re, Complex.re_sum, Complex.div_re,
        ← Complex.ofReal_pow]
    refine (hint.bdd_mul (c := 1)
      (show Continuous (fun x : ℝ^n ↦ Complex.exp
        (-(-Real.pi ^ 2 * (ε : ℂ) ^ 2 *
          ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)))) by
        fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [Complex.norm_exp, Complex.neg_re, hre, neg_zero, Real.exp_zero])).congr
      (Eventually.of_forall fun x ↦ ?_)
    simp only [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
  · exact Eventually.of_forall fun ε ↦
      (show Continuous (fun x : ℝ^n ↦ Complex.exp
        (-Real.pi ^ 2 * (ε : ℂ) ^ 2 *
          ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I))) by
        fun_prop).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · refine Eventually.of_forall fun ε ↦ Filter.Eventually.of_forall fun x ↦ ?_
    have hre : (-((Real.pi : ℂ) ^ 2) * (ε : ℂ) ^ 2 *
        ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I)).re = 0 := by
      simp [Complex.mul_re, Complex.re_sum, Complex.div_re,
        ← Complex.ofReal_pow]
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
  · exact hf.norm
  · filter_upwards with x
    have ht : Tendsto (fun ε : ℝ ↦ -((Real.pi : ℂ) ^ 2) * (ε : ℂ) ^ 2 *
        ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I))
        (𝓝 0) (𝓝 0) := by
      simpa using
        ((Complex.continuous_ofReal.tendsto 0).pow 2).const_mul
          (-((Real.pi : ℂ) ^ 2)) |>.mul_const
            (∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I))
    simpa using ht.cexp.mul_const (f x)

/-- The normalized quadratic integral converges to the Fresnel coefficient times
the value of a Schwartz amplitude at the critical point. -/
theorem tendsto_integral_diagonal_quadratic_schwartz {b : Fin n → ℝ}
    (hb : ∀ i, b i ≠ 0) (a : 𝓢(ℝ^n, ℂ)) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
      ∫ x : ℝ^n, Complex.exp ((diagonalQuadratic b x / ε ^ 2 : ℝ) * I) * a x)
      (𝓝[>] 0) (𝓝 (diagonalFresnel b * a 0)) := by
  let g : 𝓢(ℝ^n, ℂ) := 𝓕⁻ a
  have hFg : 𝓕 (g : ℝ^n → ℂ) = (a : ℝ^n → ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (fun h : 𝓢(ℝ^n, ℂ) ↦ (h : ℝ^n → ℂ))
      (FourierTransform.fourier_fourierInv_eq a)
  have hg0 : (∫ x : ℝ^n, g x) = a 0 := by
    have h := congrFun hFg 0
    simpa [Real.fourier_eq] using h
  have hlimit := (tendsto_integral_dual_quadratic (b := b) (f := g)).const_mul
    (diagonalFresnel b)
  rw [hg0] at hlimit
  apply (hlimit.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hscaled := integral_cexp_quadratic_mul_fourier
    (fun i ↦ div_ne_zero (hb i) (pow_ne_zero 2 hε.ne'))
    g.integrable (by rw [hFg]; exact a.integrable)
  have hphase (x : ℝ^n) :
      -∑ i, (-((b i / ε ^ 2 : ℝ) : ℂ) * I) * (x i : ℂ) ^ 2 =
        (diagonalQuadratic b x / ε ^ 2 : ℝ) * I := by
    simp only [diagonalQuadratic, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_div, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdual (x : ℝ^n) :
      -((Real.pi : ℂ) ^ 2) *
          ∑ i, (x i : ℂ) ^ 2 / (-((b i / ε ^ 2 : ℝ) : ℂ) * I) =
        -((Real.pi : ℂ) ^ 2) * (ε : ℂ) ^ 2 *
          ∑ i, (x i : ℂ) ^ 2 / (-(b i : ℂ) * I) := by
    rw [mul_assoc]
    apply congrArg (fun z : ℂ ↦ -((Real.pi : ℂ) ^ 2) * z)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.ofReal_div, Complex.ofReal_pow]
    field_simp
  simp only [hphase, hdual, hFg] at hscaled
  change _ = ((ε : ℂ) ^ n)⁻¹ * _
  rw [hscaled]
  change _ = ((ε : ℂ) ^ n)⁻¹ *
    (diagonalFresnel (fun i ↦ b i / ε ^ 2) * _)
  rw [diagonalFresnel_div_sq b hε]
  simp only [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hε'), one_mul]

/-- Every smooth compactly supported amplitude has the quadratic leading term. -/
theorem tendsto_integral_diagonal_quadratic {b : Fin n → ℝ}
    (hb : ∀ i, b i ≠ 0) {a : ℝ^n → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
      ∫ x : ℝ^n, Complex.exp ((diagonalQuadratic b x / ε ^ 2 : ℝ) * I) * a x)
      (𝓝[>] 0) (𝓝 (diagonalFresnel b * a 0)) :=
  tendsto_integral_diagonal_quadratic_schwartz hb (hc.toSchwartzMap ha)

/-- The difference from the leading quadratic term, divided by its natural
scale, tends to zero for any smooth compactly supported amplitude. -/
theorem tendsto_diagonal_quadratic_remainder {b : Fin n → ℝ}
    (hb : ∀ i, b i ≠ 0) {a : ℝ^n → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ *
      ((∫ x : ℝ^n, Complex.exp ((diagonalQuadratic b x / ε ^ 2 : ℝ) * I) * a x) -
        (ε : ℂ) ^ n * (diagonalFresnel b * a 0)))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_integral_diagonal_quadratic hb ha hc).sub_const
    (diagonalFresnel b * a 0)
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀
    (pow_ne_zero n (Complex.ofReal_ne_zero.mpr hε.ne')), one_mul]

end PDE.Analysis.StationaryPhase
