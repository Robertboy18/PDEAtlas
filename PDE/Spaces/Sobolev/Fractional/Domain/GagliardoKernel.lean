/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Translation
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The radial kernel in the Gagliardo-Fourier identity

After applying Plancherel to the translated difference, the remaining integral
over the increment is

`J ξ = ∫ ‖e^{2πi⟪h,ξ⟫} - 1‖² / ‖h‖^(n + 2s) dh`.

For `1 ≤ n` and `0 < s < 1`, we prove that the integrand is integrable, that `J ξ > 0` away from the
origin, and that

`J ξ = J e * ‖ξ‖^(2s)`

for every unit vector `e`. We do not compute `J e` in closed form. The argument is
the radial-kernel identity (3.12) of Di Nezza, Palatucci and Valdinoci, *Hitchhiker's guide to
the fractional Sobolev spaces*, which they prove inside the proof of Proposition 3.3, by (3.13) and
(3.14), and use for Proposition 3.4.

Integrability of the kernel uses the two elementary bounds `‖e^{2πit} - 1‖ ≤ 2` and
`‖e^{2πit} - 1‖ ≤ 2π|t|`: the second gives `|h|^{2 - n - 2s}` near the origin, integrable
because `s < 1`, and the first gives `|h|^{-n-2s}` at infinity, integrable because `s > 0`.
The scaling law follows from the change of variables `h ↦ h / ‖ξ‖`, and rotational invariance
from invariance of Lebesgue measure under linear isometries.

## Main results

* `gagKernel`, `gagJ`: the kernel and its increment integral.
* `integrable_gagKernel`: integrability for `1 ≤ n` and `0 < s < 1`.
* `gagJ_pos`: `J ξ > 0` for `ξ ≠ 0`.
* `gagJ_eq_mul_rpow`: `J ξ = J e · ‖ξ‖^{2s}` for any unit vector `e`.
* `lintegral_ofReal_gagKernel`: the extended-real form used with Tonelli in `GagliardoFourier`.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, (3.12)-(3.14) in the proof
  of Proposition 3.3: finiteness and positivity of the kernel integral, rotational invariance, and
  scaling; the identity is used in the proof of Proposition 3.4.
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped FourierTransform InnerProductSpace RealInnerProductSpace

namespace SobolevSpace.Fractional.GagliardoKernel

variable {n : ℕ} {s : ℝ}

/-! ## Scalar bounds for the Fourier character -/

private theorem norm_fourierChar_sub_one (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [Real.fourierChar_apply]
  have h :
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * Real.pi * t / 2 = Real.pi * t by ring,
    Real.norm_eq_abs, abs_mul]
  norm_num

private theorem norm_fourierChar_sub_one_le_two (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ ≤ 2 := by
  rw [norm_fourierChar_sub_one]
  nlinarith [Real.abs_sin_le_one (Real.pi * t)]

private theorem norm_fourierChar_sub_one_le (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ ≤ 2 * Real.pi * |t| := by
  rw [norm_fourierChar_sub_one]
  have hsin := Real.abs_sin_le_abs (x := Real.pi * t)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  nlinarith

private theorem norm_fourierChar_sub_one_pos
    {t : ℝ} (h0 : 0 < t) (h1 : t < 1 / 2) :
    0 < ‖(𝐞 t : ℂ) - 1‖ := by
  rw [norm_fourierChar_sub_one]
  have hsin : 0 < Real.sin (Real.pi * t) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    nlinarith [Real.pi_pos]
  rw [abs_of_pos hsin]
  linarith

/-! ## The kernel and its integral -/

/-- The kernel
`h ↦ ‖e^{2πi⟪h,ξ⟫} - 1‖² / ‖h‖^(n + 2s)`. -/
noncomputable def gagKernel (n : ℕ) (s : ℝ) (ξ h : ℝ^n) : ℝ :=
  ‖fourierCharFn h ξ - 1‖ ^ 2 /
    ‖h‖ ^ ((n : ℝ) + 2 * s)

/-- The increment integral of the Gagliardo-Fourier kernel. -/
noncomputable def gagJ (n : ℕ) (s : ℝ) (ξ : ℝ^n) : ℝ :=
  ∫ h, gagKernel n s ξ h

/-- The kernel is a quotient of a squared norm by a nonnegative power, hence nonnegative. -/
theorem gagKernel_nonneg (ξ h : ℝ^n) :
    0 ≤ gagKernel n s ξ h := by
  unfold gagKernel
  positivity

/-- At `h = 0` the kernel is `0`: the character equals `1` there, so the numerator vanishes. -/
@[simp] theorem gagKernel_zero_right (ξ : ℝ^n) :
    gagKernel n s ξ 0 = 0 := by
  simp [gagKernel]

/-- At frequency `ξ = 0` the character is identically `1`, so the kernel vanishes. -/
@[simp] theorem gagKernel_zero_left (h : ℝ^n) :
    gagKernel n s 0 h = 0 := by
  simp [gagKernel, fourierCharFn]

/-- `J 0 = 0`, since the kernel vanishes identically at frequency zero. -/
@[simp] theorem gagJ_zero :
    gagJ n s (0 : ℝ^n) = 0 := by
  simp [gagJ]

private theorem measurable_gagKernel (ξ : ℝ^n) :
    Measurable (gagKernel n s ξ) := by
  unfold gagKernel fourierCharFn
  fun_prop

/-- `J ξ ≥ 0`, as the integral of a nonnegative kernel. -/
theorem gagJ_nonneg (ξ : ℝ^n) :
    0 ≤ gagJ n s ξ :=
  integral_nonneg fun _ ↦ gagKernel_nonneg _ _

private theorem gagKernel_le_rpow_near (ξ h : ℝ^n) :
    gagKernel n s ξ h ≤
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
        ‖h‖ ^ (-((n : ℝ) + 2 * s - 2)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [gagKernel_zero_right]
    positivity
  · have hh0 : (0 : ℝ) < ‖h‖ := norm_pos_iff.mpr hh
    have hdenom : (0 : ℝ) < ‖h‖ ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hh0 _
    have hinner :
        |⟪h, ξ⟫_ℝ| ≤ ‖h‖ * ‖ξ‖ :=
      abs_real_inner_le_norm h ξ
    have hchar :
        ‖fourierCharFn h ξ - 1‖ ≤
          2 * Real.pi * (‖h‖ * ‖ξ‖) := by
      rw [fourierCharFn_apply]
      refine (norm_fourierChar_sub_one_le _).trans ?_
      nlinarith [Real.pi_pos]
    have hnum :
        ‖fourierCharFn h ξ - 1‖ ^ 2 ≤
          4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖h‖ ^ 2 := by
      nlinarith [norm_nonneg (fourierCharFn h ξ - 1),
        Real.pi_pos, norm_nonneg ξ, hh0.le]
    have hrpow :
        ‖h‖ ^ (-((n : ℝ) + 2 * s - 2)) =
          ‖h‖ ^ 2 / ‖h‖ ^ ((n : ℝ) + 2 * s) := by
      rw [← Real.rpow_natCast ‖h‖ 2, ← Real.rpow_sub hh0]
      norm_num
    rw [gagKernel, hrpow, ← mul_div_assoc]
    gcongr

private theorem gagKernel_le_rpow_far (ξ h : ℝ^n) :
    gagKernel n s ξ h ≤
      4 * ‖h‖ ^ (-((n : ℝ) + 2 * s)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · rw [gagKernel_zero_right]
    positivity
  · have hh0 : (0 : ℝ) < ‖h‖ := norm_pos_iff.mpr hh
    have hdenom : (0 : ℝ) < ‖h‖ ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hh0 _
    have hnum : ‖fourierCharFn h ξ - 1‖ ^ 2 ≤ 4 := by
      rw [fourierCharFn_apply]
      nlinarith [norm_fourierChar_sub_one_le_two ⟪h, ξ⟫_ℝ,
        norm_nonneg ((𝐞 ⟪h, ξ⟫ : ℂ) - 1)]
    rw [gagKernel, Real.rpow_neg hh0.le, ← div_eq_mul_inv]
    gcongr

/-- The radial kernel is integrable when `1 ≤ n` and `0 < s < 1`. -/
theorem integrable_gagKernel
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℝ^n) :
    Integrable (gagKernel n s ξ) (volume : Measure (ℝ^n)) := by
  have hfinrank : Module.finrank ℝ (ℝ^n) = n :=
    finrank_euclideanSpace_fin
  have hmeas :
      AEStronglyMeasurable (gagKernel n s ξ)
        (volume : Measure (ℝ^n)) :=
    (measurable_gagKernel ξ).aestronglyMeasurable
  rw [← integrableOn_univ,
    ← Set.union_compl_self (ball (0 : ℝ^n) 1)]
  refine IntegrableOn.union ?_ ?_
  · refine integrableOn_ball_of_norm_le_rpow
      (μ := volume) (by rw [hfinrank]; exact_mod_cast hn)
      (α := (n : ℝ) + 2 * s - 2)
      (C := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)
      (by rw [hfinrank]; linarith) ?_ hmeas
    filter_upwards with h
    rw [Real.norm_of_nonneg (gagKernel_nonneg ξ h)]
    exact gagKernel_le_rpow_near ξ h
  · have hexponent_nonneg :
        (0 : ℝ) ≤ (n : ℝ) + 2 * s := by
      positivity
    have hfinrank_lt :
        ((Module.finrank ℝ (ℝ^n) : ℕ) : ℝ) <
          (n : ℝ) + 2 * s := by
      rw [hfinrank]
      linarith
    have hmajorant :
        Integrable
          (fun x : ℝ^n ↦
            4 * 2 ^ ((n : ℝ) + 2 * s) *
              (1 + ‖x‖) ^ (-((n : ℝ) + 2 * s)))
          (volume : Measure (ℝ^n)) :=
      (integrable_one_add_norm hfinrank_lt).const_mul _
    refine Integrable.mono' (hmajorant.restrict) hmeas.restrict ?_
    rw [ae_restrict_iff' measurableSet_ball.compl]
    filter_upwards with x hx
    rw [Real.norm_of_nonneg (gagKernel_nonneg ξ x)]
    have hx1 : (1 : ℝ) ≤ ‖x‖ := by
      simpa [mem_ball, dist_eq_norm] using hx
    have hx0 : (0 : ℝ) < ‖x‖ :=
      lt_of_lt_of_le one_pos hx1
    have hdenom : (0 : ℝ) < ‖x‖ ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos hx0 _
    have hshifted :
        (0 : ℝ) < (1 + ‖x‖) ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hpow_le :
        (1 + ‖x‖) ^ ((n : ℝ) + 2 * s) ≤
          (2 * ‖x‖) ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_le_rpow (by linarith) (by linarith)
        hexponent_nonneg
    have hmul_rpow :
        (2 * ‖x‖) ^ ((n : ℝ) + 2 * s) =
          2 ^ ((n : ℝ) + 2 * s) *
            ‖x‖ ^ ((n : ℝ) + 2 * s) :=
      Real.mul_rpow (by norm_num) (norm_nonneg x)
    have htwo_pos :
        (0 : ℝ) < 2 ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos (by norm_num) _
    refine (gagKernel_le_rpow_far ξ x).trans ?_
    rw [Real.rpow_neg hx0.le, Real.rpow_neg (by linarith),
      ← div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv,
      ← mul_div_assoc, div_le_div_iff₀ hdenom hshifted]
    nlinarith

/-! ## Positivity, scaling, and rotational invariance -/

/-- The kernel integral is positive away from the origin. -/
theorem gagJ_pos
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    {ξ : ℝ^n} (hξ : ξ ≠ 0) :
    0 < gagJ n s ξ := by
  have hξ0 : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
  let U : Set (ℝ^n) :=
    (fun h : ℝ^n ↦ ⟪h, ξ⟫_ℝ) ⁻¹' Ioo 0 (1 / 2)
  have hUopen : IsOpen U := by
    refine IsOpen.preimage ?_ isOpen_Ioo
    exact Continuous.inner continuous_id continuous_const
  have hUne : U.Nonempty := by
    refine ⟨(1 / (4 * ‖ξ‖ ^ 2)) • ξ, ?_⟩
    have hinner :
        ⟪(1 / (4 * ‖ξ‖ ^ 2)) • ξ, ξ⟫_ℝ = 1 / 4 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    simp only [U, Set.mem_preimage, hinner, Set.mem_Ioo]
    norm_num
  have hsupport : U ⊆ Function.support (gagKernel n s ξ) := by
    intro h hh
    obtain ⟨h0, h1⟩ :
        0 < ⟪h, ξ⟫_ℝ ∧ ⟪h, ξ⟫_ℝ < 1 / 2 :=
      hh
    have hhne : h ≠ 0 := by
      rintro rfl
      simp at h0
    have hdenom :
        (0 : ℝ) < ‖h‖ ^ ((n : ℝ) + 2 * s) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hhne) _
    have hnum :
        0 < ‖fourierCharFn h ξ - 1‖ ^ 2 := by
      rw [fourierCharFn_apply]
      have hchar :=
        norm_fourierChar_sub_one_pos h0 h1
      positivity
    exact ne_of_gt (div_pos hnum hdenom)
  rw [gagJ, integral_pos_iff_support_of_nonneg
    (fun h ↦ gagKernel_nonneg ξ h)
    (integrable_gagKernel hn hs0 hs1 ξ)]
  exact lt_of_lt_of_le
    (hUopen.measure_pos volume hUne) (measure_mono hsupport)

private theorem gagKernel_comp_smul
    {r : ℝ} (hr : 0 < r) (ξ h : ℝ^n) :
    gagKernel n s ξ (r • h) =
      r ^ (-((n : ℝ) + 2 * s)) *
        gagKernel n s (r • ξ) h := by
  have hinner : ⟪r • h, ξ⟫_ℝ = ⟪h, r • ξ⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_smul_right]
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have hrpow :
        ‖r • h‖ ^ ((n : ℝ) + 2 * s) =
          r ^ ((n : ℝ) + 2 * s) *
            ‖h‖ ^ ((n : ℝ) + 2 * s) := by
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      exact Real.mul_rpow hr.le (norm_nonneg h)
    simp only [gagKernel, fourierCharFn_apply]
    rw [hinner, hrpow, Real.rpow_neg hr.le]
    ring

private theorem gagJ_smul
    {r : ℝ} (hr : 0 < r) (ξ : ℝ^n) :
    gagJ n s (r • ξ) = r ^ (2 * s) * gagJ n s ξ := by
  have hfinrank : Module.finrank ℝ (ℝ^n) = n :=
    finrank_euclideanSpace_fin
  have hchange :
      ∫ h : ℝ^n, gagKernel n s ξ (r • h) =
        |(r ^ Module.finrank ℝ (ℝ^n))⁻¹| • gagJ n s ξ :=
    Measure.integral_comp_smul volume (gagKernel n s ξ) r
  have hlhs :
      ∫ h : ℝ^n, gagKernel n s ξ (r • h) =
        r ^ (-((n : ℝ) + 2 * s)) *
          gagJ n s (r • ξ) := by
    rw [gagJ, ← integral_const_mul]
    exact integral_congr_ae
      (Filter.Eventually.of_forall
        fun h ↦ gagKernel_comp_smul hr ξ h)
  have habs :
      |(r ^ Module.finrank ℝ (ℝ^n))⁻¹| =
        r ^ (-(n : ℝ)) := by
    rw [hfinrank, abs_of_nonneg (by positivity),
      Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [hlhs, habs, smul_eq_mul] at hchange
  have hmul :=
    congrArg (fun z : ℝ ↦ r ^ ((n : ℝ) + 2 * s) * z)
      hchange
  rw [← mul_assoc, ← Real.rpow_add hr, add_neg_cancel,
    Real.rpow_zero, one_mul, ← mul_assoc,
    ← Real.rpow_add hr] at hmul
  rw [hmul]
  norm_num

private theorem gagJ_linearIsometryEquiv
    (f : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) (ξ : ℝ^n) :
    gagJ n s (f ξ) = gagJ n s ξ := by
  have hpreserving :
      MeasurePreserving f
        (volume : Measure (ℝ^n))
        (volume : Measure (ℝ^n)) :=
    f.measurePreserving
  have hcomp :=
    hpreserving.integral_comp
      f.toHomeomorph.measurableEmbedding
      (gagKernel n s (f ξ))
  rw [gagJ, ← hcomp, gagJ]
  refine integral_congr_ae
    (Filter.Eventually.of_forall fun h ↦ ?_)
  simp only [gagKernel, fourierCharFn, f.inner_map_map, f.norm_map]

/-- For a unit vector `e`, the radial integral has the form
`J ξ = J e * ‖ξ‖^(2s)`. -/
theorem gagJ_eq_mul_rpow
    (hs0 : 0 < s) {e : ℝ^n} (he : ‖e‖ = 1) (ξ : ℝ^n) :
    gagJ n s ξ = gagJ n s e * ‖ξ‖ ^ (2 * s) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [gagJ_zero, norm_zero,
      Real.zero_rpow (by positivity), mul_zero]
  · have hξ0 : (0 : ℝ) < ‖ξ‖ :=
      norm_pos_iff.mpr hξ
    have hnorm :
        ‖ξ‖ = ‖(‖ξ‖ : ℝ) • e‖ := by
      rw [norm_smul, he, Real.norm_of_nonneg hξ0.le, mul_one]
    have hreflection :=
      Submodule.reflection_sub (F := ℝ^n) hnorm
    have hinvariant :=
      gagJ_linearIsometryEquiv
        (s := s)
        (Submodule.reflection
          (𝕜 := ℝ) (ℝ ∙ (ξ - (‖ξ‖ : ℝ) • e))ᗮ)
        ξ
    rw [hreflection] at hinvariant
    rw [← hinvariant, gagJ_smul hξ0, mul_comm]

/-- Extended-real form of the kernel integral, for use with Tonelli's theorem. -/
theorem lintegral_ofReal_gagKernel
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℝ^n) :
    ∫⁻ h, ENNReal.ofReal (gagKernel n s ξ h)
        ∂(volume : Measure (ℝ^n)) =
      ENNReal.ofReal (gagJ n s ξ) :=
  (ofReal_integral_eq_lintegral_ofReal
    (integrable_gagKernel hn hs0 hs1 ξ)
    (Filter.Eventually.of_forall
      fun h ↦ gagKernel_nonneg ξ h)).symm

end SobolevSpace.Fractional.GagliardoKernel
