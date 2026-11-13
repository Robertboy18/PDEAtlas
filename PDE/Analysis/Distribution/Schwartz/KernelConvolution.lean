/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Convolution
public import PDE.Common.Euclidean
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Convolution of Schwartz kernels with polynomially weighted data

Let `K` be a Schwartz function on `ℝ^n` and let `f` be a function such that
`y ↦ (1 + ‖y‖)⁻ᴺ f y` is integrable for some `N`. For a continuous bilinear pairing `L`, the
convolution `K ⋆[L] f` is smooth. Its derivative is the convolution of the derivative of `K`
with `f` under the pairing `precompL L`, and the `m`-th derivative is bounded at every point
`x` by `‖L‖` times `∫ ‖Dᵐ K (x - y)‖ ‖f y‖ dy`. Every derivative of a Schwartz function lies in
every `Lᵠ(ℝ^n)`.

Every function in `Lᵖ(ℝ^n)`, `1 ≤ p ≤ ∞`, satisfies the weighted condition with `N = n + 1`,
by Hölder's inequality against `(1 + ‖y‖)^(-(n+1))`, which lies in every `Lᵠ`, `q ≥ 1`.

The derivatives are differentiated under the integral sign with the dominating function
`C (2 + ‖x₀‖)ᴺ (1 + ‖y‖)⁻ᴺ ‖f y‖` on the unit ball around `x₀`, from Peetre's inequality
`1 + ‖y‖ ≤ (1 + ‖x‖)(1 + ‖x - y‖)`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology SchwartzMap ContDiff Convolution

universe uE uF uG

section PolynomialWeight

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
  {f : ℝ^n → E}

namespace PDE

/-- The polynomial weight `(1 + ‖y‖)⁻ᴺ`. -/
def polynomialWeight (N : ℕ) (y : ℝ^n) : ℝ :=
  ((1 + ‖y‖) ^ N)⁻¹

theorem polynomialWeight_pos (N : ℕ) (y : ℝ^n) : 0 < polynomialWeight N y := by
  unfold polynomialWeight
  positivity

theorem continuous_polynomialWeight (N : ℕ) : Continuous (polynomialWeight (n := n) N) := by
  have h : Continuous (fun y : ℝ^n ↦ (1 + ‖y‖) ^ N) := by fun_prop
  exact h.inv₀ fun y ↦ (pow_pos (by positivity) N).ne'

/-- Peetre's inequality for the polynomial weight. -/
theorem polynomialWeight_sub_le (N : ℕ) (x y : ℝ^n) :
    polynomialWeight N (x - y) ≤ (1 + ‖x‖) ^ N * polynomialWeight N y := by
  unfold polynomialWeight
  have hy : 1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖x - y‖) := by
    have h : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      simpa using norm_sub_le x (x - y)
    nlinarith [norm_nonneg x, norm_nonneg (x - y)]
  have hpow : (1 + ‖y‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖x - y‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hy N
  rw [← div_eq_mul_inv, inv_le_comm₀ (by positivity) (by positivity), inv_div,
    div_le_iff₀ (by positivity)]
  simpa only [mul_comm] using hpow

/-- Weighted integrability gives measurability of the data. -/
theorem aestronglyMeasurable_of_integrable_polynomialWeight_smul
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) : AEStronglyMeasurable f := by
  have hc : Continuous (fun y : ℝ^n ↦ (1 + ‖y‖) ^ N) := by fun_prop
  have h := hc.aestronglyMeasurable.smul hf.aestronglyMeasurable
  refine h.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.smul_apply', polynomialWeight, smul_smul]
  rw [mul_inv_cancel₀ (by positivity), one_smul]

/-- The polynomial weight of order `n + 1` lies in every `Lᵠ(ℝ^n)`, `1 ≤ q ≤ ∞`. -/
theorem memLp_polynomialWeight {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLp (polynomialWeight (n := n) (n + 1)) q volume := by
  have hmeas := (continuous_polynomialWeight (n := n) (n + 1)).aestronglyMeasurable
    (μ := (volume : Measure (ℝ^n)))
  by_cases htop : q = ⊤
  · subst htop
    refine memLp_top_of_bound hmeas 1 (Filter.Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (polynomialWeight_pos _ y)]
    unfold polynomialWeight
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by simp))
  · have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    have hqr : 1 ≤ q.toReal := by
      simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).mpr hq
    refine (integrable_norm_rpow_iff hmeas hq0 htop).mp ?_
    have hint := integrable_one_add_norm (E := ℝ^n) (μ := volume)
      (r := ((n + 1 : ℕ) : ℝ) * q.toReal) (by
        rw [finrank_euclideanSpace_fin]
        have : (n : ℝ) < (n + 1 : ℕ) := by push_cast; linarith
        nlinarith)
    refine hint.congr (Filter.Eventually.of_forall fun y ↦ ?_)
    have hpos : 0 < 1 + ‖y‖ := by positivity
    simp only [polynomialWeight, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), Real.inv_rpow (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le, Real.rpow_neg hpos.le]

/-- The polynomial weight of order `N` lies in `Lᵠ(ℝ^n)`, `1 ≤ q < ∞`, when `n < N q`. -/
theorem memLp_polynomialWeight_of_lt {N : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (htop : q ≠ ⊤)
    (hN : (n : ℝ) < N * q.toReal) :
    MemLp (polynomialWeight (n := n) N) q volume := by
  have hmeas := (continuous_polynomialWeight (n := n) N).aestronglyMeasurable
    (μ := (volume : Measure (ℝ^n)))
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  refine (integrable_norm_rpow_iff hmeas hq0 htop).mp ?_
  have hint := integrable_one_add_norm (E := ℝ^n) (μ := volume) (r := (N : ℝ) * q.toReal)
    (by rwa [finrank_euclideanSpace_fin])
  refine hint.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  simp only [polynomialWeight, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), Real.inv_rpow (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hpos.le, Real.rpow_neg hpos.le]

/-- Every `Lᵖ(ℝ^n)` function with `1 ≤ p ≤ ∞` is integrable against the polynomial weight of
order `n + 1`. -/
theorem integrable_polynomialWeight_smul_of_memLp {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) :
    Integrable (fun y ↦ polynomialWeight (n + 1) y • f y) := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hpinv : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  have hq : 1 ≤ q := ENNReal.one_le_inv.mpr tsub_le_self
  have : ENNReal.HolderTriple q p 1 :=
    ⟨by simp only [q, inv_inv, inv_one]; exact tsub_add_cancel_of_le hpinv⟩
  exact memLp_one_iff_integrable.mp ((memLp_polynomialWeight hq).smul hf)

end PDE

end PolynomialWeight

open PDE (polynomialWeight)

namespace SchwartzMap

variable {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Schwartz function decays faster than every polynomial weight. -/
theorem exists_norm_le_polynomialWeight {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : 𝓢(ℝ^n, F)) (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ z, ‖K z‖ ≤ C * polynomialWeight N z := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) K,
    by positivity, fun z ↦ ?_⟩
  have h := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (le_refl N) (le_refl 0) K z
  rw [norm_iteratedFDeriv_zero] at h
  unfold polynomialWeight
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact h

variable {N : ℕ} {f : ℝ^n → E}

section Bounds

variable {F : Type uF} {G : Type uG} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]


/-- The integrand is dominated by the weighted data. -/
theorem norm_kernel_apply_le (L : F →L[ℝ] E →L[ℝ] G) {K : ℝ^n → F} {C : ℝ}
    (hK : ∀ z, ‖K z‖ ≤ C * polynomialWeight N z) (hC : 0 ≤ C) (x y : ℝ^n) :
    ‖L (K (x - y)) (f y)‖ ≤
      ‖L‖ * C * (1 + ‖x‖) ^ N * ‖polynomialWeight N y • f y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (PDE.polynomialWeight_pos N y)]
  calc
    _ ≤ ‖L‖ * ‖K (x - y)‖ * ‖f y‖ := L.le_opNorm₂ _ _
    _ ≤ ‖L‖ * (C * ((1 + ‖x‖) ^ N * polynomialWeight N y)) * ‖f y‖ := by
      gcongr
      exact (hK _).trans (mul_le_mul_of_nonneg_left (PDE.polynomialWeight_sub_le N x y) hC)
    _ = _ := by ring

/-- The convolution integrand is integrable at every point. -/
theorem integrable_kernel (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (x : ℝ^n) :
    Integrable (fun y ↦ L (K (x - y)) (f y)) := by
  obtain ⟨C, hC, hK⟩ := exists_norm_le_polynomialWeight K N
  refine Integrable.mono' (hf.norm.const_mul (‖L‖ * C * (1 + ‖x‖) ^ N)) ?_
    (Filter.Eventually.of_forall fun y ↦ norm_kernel_apply_le L hK hC x y)
  exact L.aestronglyMeasurable_comp₂
    ((K.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (PDE.aestronglyMeasurable_of_integrable_polynomialWeight_smul hf)

/-- Differentiation under the integral sign: the derivative falls on the kernel. -/
theorem hasFDerivAt_convolution (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (x₀ : ℝ^n) :
    HasFDerivAt (⇑K ⋆[L] f)
      ((⇑(fderivCLM ℝ (ℝ^n) F K) ⋆[L.precompL (ℝ^n)] f) x₀) x₀ := by
  obtain ⟨C, hC, hK⟩ := exists_norm_le_polynomialWeight (fderivCLM ℝ (ℝ^n) F K) N
  let L' : (ℝ^n →L[ℝ] F) →L[ℝ] E →L[ℝ] ℝ^n →L[ℝ] G := L.precompL (ℝ^n)
  rw [show (⇑K ⋆[L] f) = fun x ↦ ∫ y, L (K (x - y)) (f y) from
    funext fun x ↦ convolution_eq_swap (L := L) (μ := volume), convolution_eq_swap]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ one_pos)
    (F := fun x y ↦ L (K (x - y)) (f y))
    (F' := fun x y ↦ L' (fderivCLM ℝ (ℝ^n) F K (x - y)) (f y))
    (bound := fun y ↦ ‖L‖ * C * (2 + ‖x₀‖) ^ N * ‖polynomialWeight N y • f y‖)
    (Filter.Eventually.of_forall fun x ↦ (integrable_kernel L K hf x).aestronglyMeasurable)
    (integrable_kernel L K hf x₀)
    (integrable_kernel L' (fderivCLM ℝ (ℝ^n) F K) hf x₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x hx ↦ ?_)
    (hf.norm.const_mul _) (Filter.Eventually.of_forall fun y x _ ↦ ?_)
  · refine (norm_kernel_apply_le L' hK hC x y).trans ?_
    have hx' : 1 + ‖x‖ ≤ 2 + ‖x₀‖ := by
      have h := norm_le_norm_add_norm_sub' x x₀
      rw [mem_ball, dist_eq_norm] at hx
      linarith
    have hL' := ContinuousLinearMap.norm_precompL_le (ℝ^n) L
    exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hL' hC)
      (pow_le_pow_left₀ (by positivity) hx' N) (by positivity)
      (mul_nonneg (norm_nonneg L) hC)) (norm_nonneg _)
  · have hK' : HasFDerivAt (fun x ↦ K (x - y)) ((fderiv ℝ K (x - y)).comp
        (ContinuousLinearMap.id ℝ (ℝ^n))) x :=
      (K.hasFDerivAt (x - y)).comp x ((hasFDerivAt_id x).sub_const y)
    have h := ((L.flip (f y)).hasFDerivAt.comp x hK')
    refine h.congr_fderiv ?_
    ext v
    simp [L']

/-- The derivative of the convolution is the convolution of the derivative. -/
theorem fderiv_convolution (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) :
    fderiv ℝ (⇑K ⋆[L] f) = ⇑(fderivCLM ℝ (ℝ^n) F K) ⋆[L.precompL (ℝ^n)] f :=
  funext fun x ↦ (hasFDerivAt_convolution L K hf x).fderiv

theorem differentiable_convolution (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) :
    Differentiable ℝ (⇑K ⋆[L] f) :=
  fun x ↦ (hasFDerivAt_convolution L K hf x).differentiableAt

/-- The convolution is linear in the data. -/
theorem convolution_sub (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F)) {g : ℝ^n → E}
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y))
    (hg : Integrable (fun y ↦ polynomialWeight N y • g y)) :
    ⇑K ⋆[L] (f - g) = ⇑K ⋆[L] f - ⇑K ⋆[L] g := by
  funext x
  simp only [Pi.sub_apply, convolution_eq_swap, map_sub]
  exact integral_sub (integrable_kernel L K hf x) (integrable_kernel L K hg x)

end Bounds

private theorem contDiff_nat_convolution
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (m : ℕ) :
    ∀ {F : Type uF} {G : Type uG} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
      (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F)), ContDiff ℝ m (⇑K ⋆[L] f) := by
  induction m with
  | zero =>
    intro F G _ _ _ _ L K
    exact contDiff_zero.mpr (differentiable_convolution L K hf).continuous
  | succ m ih =>
    intro F G _ _ _ _ L K
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_convolution L K hf, by simp, ?_⟩
    rw [fderiv_convolution L K hf]
    exact ih _ _

/-- The convolution of a Schwartz kernel with polynomially weighted data is smooth. -/
theorem contDiff_convolution {F : Type uF} {G : Type uG} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) :
    ContDiff ℝ (⊤ : ℕ∞) (⇑K ⋆[L] f) :=
  contDiff_infty.mpr fun m ↦ contDiff_nat_convolution hf m L K

private theorem enorm_eq_of_norm_eq {A B : Type*} [SeminormedAddCommGroup A]
    [SeminormedAddCommGroup B] {a : A} {b : B} (h : ‖a‖ = ‖b‖) : ‖a‖ₑ = ‖b‖ₑ := by
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  exact NNReal.eq (by simpa only [coe_nnnorm] using h)

/-- Every derivative of the convolution is bounded at each point `x` by `‖L‖` times
`∫ ‖Dᵐ K (x - y)‖ ‖f y‖ dy`. -/
theorem enorm_iteratedFDeriv_convolution_le {F : Type uF} {G : Type uG}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] E →L[ℝ] G) (K : 𝓢(ℝ^n, F))
    (hf : Integrable (fun y ↦ polynomialWeight N y • f y)) (m : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (⇑K ⋆[L] f) x‖ₑ ≤
      ‖L‖ₑ * ∫⁻ y, ‖iteratedFDeriv ℝ m K (x - y)‖ₑ * ‖f y‖ₑ := by
  induction m generalizing F G L K x with
  | zero =>
    rw [enorm_eq_of_norm_eq norm_iteratedFDeriv_zero, convolution_eq_swap]
    simp_rw [enorm_eq_of_norm_eq (norm_iteratedFDeriv_zero (f := ⇑K) (x := x - _))]
    calc
      _ ≤ ∫⁻ y, ‖L (K (x - y)) (f y)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, ‖L‖ₑ * (‖K (x - y)‖ₑ * ‖f y‖ₑ) :=
        lintegral_mono fun y ↦ by rw [← mul_assoc]; exact L.le_opENorm₂ _ _
      _ = _ := lintegral_const_mul' _ _ enorm_ne_top
  | succ m ih =>
    rw [← enorm_eq_of_norm_eq (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ⇑K ⋆[L] f)
      (x := x)), fderiv_convolution L K hf]
    refine (ih (L.precompL (ℝ^n)) (fderivCLM ℝ (ℝ^n) F K) x).trans ?_
    have hK (z : ℝ^n) : ‖iteratedFDeriv ℝ m (fderivCLM ℝ (ℝ^n) F K) z‖ₑ =
        ‖iteratedFDeriv ℝ (m + 1) K z‖ₑ := by
      rw [show ((fderivCLM ℝ (ℝ^n) F K : 𝓢(ℝ^n, ℝ^n →L[ℝ] F)) : ℝ^n → ℝ^n →L[ℝ] F) =
        fderiv ℝ K from funext fun z ↦ fderivCLM_apply ℝ K z]
      exact enorm_eq_of_norm_eq norm_iteratedFDeriv_fderiv
    simp_rw [hK]
    gcongr
    simpa only [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] using
      ContinuousLinearMap.norm_precompL_le (ℝ^n) L

/-- Every derivative of a Schwartz function lies in every `Lᵠ(ℝ^n)`. -/
theorem memLp_iteratedFDeriv {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : 𝓢(ℝ^n, F)) (m : ℕ) (q : ℝ≥0∞) : MemLp (iteratedFDeriv ℝ m K) q volume := by
  induction m generalizing F K with
  | zero =>
    refine (K.memLp q volume).of_le
      ((K.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_iteratedFDeriv_zero]
  | succ m ih =>
    refine (ih (fderivCLM ℝ (ℝ^n) F K)).of_le
      ((K.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [show ((fderivCLM ℝ (ℝ^n) F K : 𝓢(ℝ^n, ℝ^n →L[ℝ] F)) : ℝ^n → ℝ^n →L[ℝ] F) =
      fderiv ℝ K from funext fun z ↦ fderivCLM_apply ℝ K z, norm_iteratedFDeriv_fderiv]

end SchwartzMap
