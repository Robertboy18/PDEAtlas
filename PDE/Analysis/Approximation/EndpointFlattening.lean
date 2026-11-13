/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CAS.ExactTactic
import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# Flattening a Lipschitz profile at a singularly weighted endpoint

The cutoff is one before `L - 2 * δ` and zero after `L - δ`. Its derivative is bounded
by a fixed constant divided by `δ`. If `f L = 0`, Lipschitz regularity cancels the
inverse-square value weight at `L`. No vanishing endpoint derivative is required.

This is the endpoint step of smooth initialization. Multiplication by the cutoff
does not smooth interior knots.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace PDE.Analysis.Calculus

/-- A smooth cutoff supported to the left of `L - δ`. -/
def endpointCutoff (L δ x : ℝ) : ℝ :=
  Real.smoothTransition ((L - x) / δ - 1)

/-- The change made by the one-sided endpoint cutoff. -/
def endpointError (f : ℝ → ℝ) (L δ x : ℝ) : ℝ :=
  (endpointCutoff L δ x - 1) * f x

/-- The endpoint cutoff is smooth, including the two ends of its transition strip. -/
theorem contDiff_endpointCutoff (L δ : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (endpointCutoff L δ) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.sub contDiff_id).div_const δ).sub contDiff_const)

theorem endpointCutoff_nonneg (L δ x : ℝ) : 0 ≤ endpointCutoff L δ x :=
  Real.smoothTransition.nonneg _

theorem endpointCutoff_le_one (L δ x : ℝ) : endpointCutoff L δ x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The retained part of the profile is unchanged exactly. -/
theorem endpointCutoff_eq_one {L δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ L - 2 * δ) :
    endpointCutoff L δ x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 2 ≤ (L - x) / δ := (le_div_iff₀ hδ).2 (by cas)
  cas

/-- There is an open collar of width `δ` at the endpoint on which the cutoff is zero. -/
theorem endpointCutoff_eq_zero {L δ x : ℝ} (hδ : 0 < δ) (hx : L - δ ≤ x) :
    endpointCutoff L δ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : (L - x) / δ ≤ 1 := (div_le_iff₀ hδ).2 (by cas)
  cas

theorem hasDerivAt_endpointCutoff (L δ x : ℝ) :
    HasDerivAt (endpointCutoff L δ)
      (deriv Real.smoothTransition ((L - x) / δ - 1) * (-1 / δ)) x := by
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _
    ).hasDerivAt.comp x (((hasDerivAt_const x L).sub (hasDerivAt_id x)).div_const δ
      |>.sub_const 1)
  simpa only [endpointCutoff, Function.comp_def, Pi.sub_apply, id_eq, zero_sub] using! h

/-- The derivative has the expected inverse-width bound. -/
theorem abs_deriv_endpointCutoff_le {C : ℝ≥0}
    (hC : LipschitzWith C Real.smoothTransition) {L δ x : ℝ} (hδ : 0 < δ) :
    |deriv (endpointCutoff L δ) x| ≤ C / δ := by
  rw [(hasDerivAt_endpointCutoff L δ x).deriv, abs_mul, abs_div, abs_neg,
    abs_one, abs_of_pos hδ, mul_one_div]
  exact div_le_div_of_nonneg_right (norm_deriv_le_of_lipschitz hC) hδ.le

/-- The error vanishes before the transition strip. -/
theorem endpointError_eq_zero {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hx : x ≤ L - 2 * δ) : endpointError f L δ x = 0 := by
  simp [endpointError, endpointCutoff_eq_one hδ hx]

/-- Strictly before the transition, the error and all its derivatives vanish locally. -/
theorem endpointError_eventuallyEq_zero {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hx : x < L - 2 * δ) :
    endpointError f L δ =ᶠ[𝓝 x] (fun _ ↦ 0) := by
  filter_upwards [eventually_lt_nhds hx] with y hy
  exact endpointError_eq_zero hδ hy.le

theorem deriv_endpointError_eq_zero {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hx : x < L - 2 * δ) :
    deriv (endpointError f L δ) x = 0 := by
  rw [(endpointError_eventuallyEq_zero hδ hx).deriv_eq]
  exact deriv_const x 0

/-- Only value zero and a Lipschitz constant are needed for linear endpoint decay. -/
theorem abs_le_lipschitz_mul_endpoint_dist {f : ℝ → ℝ} {K : ℝ≥0} {L x : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0) (hx : x ≤ L) :
    |f x| ≤ K * (L - x) := by
  have h := hf.dist_le_mul x L
  simpa only [Real.dist_eq, hfL, sub_zero, abs_of_nonpos (sub_nonpos.mpr hx),
    neg_sub] using h

/-- The value error still vanishes linearly at the endpoint. -/
theorem abs_endpointError_le {f : ℝ → ℝ} {K : ℝ≥0} {L δ x : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0) (hx : x ≤ L) :
    |endpointError f L δ x| ≤ K * (L - x) := by
  have hc : |endpointCutoff L δ x - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (endpointCutoff_le_one L δ x))]
    have := endpointCutoff_nonneg L δ x
    cas
  calc
    |endpointError f L δ x| = |endpointCutoff L δ x - 1| * |f x| := abs_mul _ _
    _ ≤ 1 * (K * (L - x)) :=
      mul_le_mul hc (abs_le_lipschitz_mul_endpoint_dist hf hfL hx)
        (abs_nonneg _) (by positivity)
    _ = K * (L - x) := one_mul _

/-- A formula for the classical derivative at each differentiability point of the input. -/
theorem hasDerivAt_endpointError {f : ℝ → ℝ} {L δ x : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (endpointError f L δ)
      (deriv (endpointCutoff L δ) x * f x +
        (endpointCutoff L δ x - 1) * deriv f x) x :=
  (((contDiff_endpointCutoff L δ (n := 1)).differentiable one_ne_zero x
    ).hasDerivAt.sub_const 1).mul hf.hasDerivAt

/-- The cutoff derivative loses one inverse power of the strip width, but the zero endpoint
value supplies the compensating power. In particular the bound is independent of `δ`. -/
theorem abs_deriv_endpointError_le {f : ℝ → ℝ} {K C : ℝ≥0} {L δ x : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0)
    (hC : LipschitzWith C Real.smoothTransition) (hδ : 0 < δ)
    (hx : x ∈ Icc (L - 2 * δ) L) (hfx : DifferentiableAt ℝ f x) :
    |deriv (endpointError f L δ) x| ≤ (2 * C + 1) * K := by
  have hc : |endpointCutoff L δ x - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (endpointCutoff_le_one L δ x))]
    have := endpointCutoff_nonneg L δ x
    cas
  have hfirst : |deriv (endpointCutoff L δ) x * f x| ≤ 2 * C * K := by
    calc
      |deriv (endpointCutoff L δ) x * f x| =
          |deriv (endpointCutoff L δ) x| * |f x| := abs_mul _ _
      _ ≤ (C / δ) * (K * (L - x)) :=
        mul_le_mul (abs_deriv_endpointCutoff_le hC hδ)
          (abs_le_lipschitz_mul_endpoint_dist hf hfL hx.2) (abs_nonneg _)
          (by positivity)
      _ ≤ (C / δ) * (K * (2 * δ)) := by
        gcongr
        have := hx.1
        cas
      _ = 2 * C * K := by
        field_simp
  have hsecond : |(endpointCutoff L δ x - 1) * deriv f x| ≤ K := by
    rw [abs_mul]
    simpa only [one_mul, Real.norm_eq_abs] using
      mul_le_mul hc (norm_deriv_le_of_lipschitz hf) (abs_nonneg _) zero_le_one
  rw [(hasDerivAt_endpointError hfx).deriv]
  calc
    _ ≤ |deriv (endpointCutoff L δ) x * f x| +
        |(endpointCutoff L δ x - 1) * deriv f x| := abs_add_le _ _
    _ ≤ 2 * C * K + K := add_le_add hfirst hsecond
    _ = (2 * C + 1) * K := by cas

/-- The energy density is uniformly bounded in the endpoint strip, even though the
value weight has an inverse-square singularity. These are input weight comparisons,
not an assumption on the approximation error. -/
theorem endpointError_energy_density_le {f w v : ℝ → ℝ}
    {K C : ℝ≥0} {L δ A B x : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0)
    (hC : LipschitzWith C Real.smoothTransition) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : x ∈ Ico (L - 2 * δ) L)
    (hfx : DifferentiableAt ℝ f x)
    (hw : w x ≤ A / (L - x) ^ 2) (hv : v x ≤ B) :
    endpointError f L δ x ^ 2 * w x + deriv (endpointError f L δ) x ^ 2 * v x ≤
      A * K ^ 2 + B * ((2 * C + 1) * K) ^ 2 := by
  have hd : 0 < L - x := sub_pos.mpr hx.2
  have hq := abs_endpointError_le (δ := δ) hf hfL hx.2.le
  have hsq : endpointError f L δ x ^ 2 ≤ (K * (L - x)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
  have hratio : endpointError f L δ x ^ 2 / (L - x) ^ 2 ≤ K ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    simpa only [mul_pow] using hsq
  have hvq := abs_deriv_endpointError_le hf hfL hC hδ ⟨hx.1, hx.2.le⟩ hfx
  have hsq' : deriv (endpointError f L δ) x ^ 2 ≤ ((2 * C + 1) * K) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hvq 2
  apply add_le_add
  · calc
      endpointError f L δ x ^ 2 * w x ≤
          endpointError f L δ x ^ 2 * (A / (L - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = A * (endpointError f L δ x ^ 2 / (L - x) ^ 2) := by cas
      _ ≤ A * K ^ 2 := mul_le_mul_of_nonneg_left hratio hA
  · calc
      deriv (endpointError f L δ) x ^ 2 * v x ≤
          deriv (endpointError f L δ) x ^ 2 * B :=
        mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ ≤ ((2 * C + 1) * K) ^ 2 * B := mul_le_mul_of_nonneg_right hsq' hB
      _ = B * ((2 * C + 1) * K) ^ 2 := mul_comm _ _

/-- The nonnegative singular weighted squared `H¹` error on the positive half interval.
For nonnegative weights, `ofReal` does not discard any part of the energy density. -/
def singularWeightedH1Error (w v q : ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 L, ENNReal.ofReal (q x ^ 2 * w x + deriv q x ^ 2 * v x)

/-- A weighted error estimate: the integral is at most the strip length times
a constant independent of that length. No measurability or integrability of the weighted
error is assumed. -/
theorem singularWeightedH1Error_endpointError_le {f w v : ℝ → ℝ}
    {K C : ℝ≥0} {L δ A B : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0)
    (hC : LipschitzWith C Real.smoothTransition) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ f x)
    (hw : ∀ x ∈ Ico (L - 2 * δ) L, w x ≤ A / (L - x) ^ 2)
    (hv : ∀ x ∈ Ico (L - 2 * δ) L, v x ≤ B) :
    singularWeightedH1Error w v (endpointError f L δ) L ≤
      ENNReal.ofReal (2 * δ * (A * K ^ 2 + B * ((2 * C + 1) * K) ^ 2)) := by
  let M : ℝ := A * K ^ 2 + B * ((2 * C + 1) * K) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : singularWeightedH1Error w v (endpointError f L δ) L ≤
      ∫⁻ x in Ioo 0 L, (Ico (L - 2 * δ) L).indicator (fun _ ↦ ENNReal.ofReal M) x := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    by_cases ht : L - 2 * δ ≤ x
    · have hxt : x ∈ Ico (L - 2 * δ) L := ⟨ht, hx.2⟩
      rw [indicator_of_mem hxt]
      exact ENNReal.ofReal_le_ofReal
        (endpointError_energy_density_le hf hfL hC hδ hA hB hxt (hfd x hx)
          (hw x hxt) (hv x hxt))
    · have hxt : x < L - 2 * δ := lt_of_not_ge ht
      simp only [endpointError_eq_zero hδ hxt.le, deriv_endpointError_eq_zero hδ hxt,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero,
        ENNReal.ofReal_zero]
      exact zero_le
  calc
    singularWeightedH1Error w v (endpointError f L δ) L ≤
        ∫⁻ x in Ioo 0 L, (Ico (L - 2 * δ) L).indicator (fun _ ↦ ENNReal.ofReal M) x :=
      hbound
    _ ≤ ∫⁻ x, (Ico (L - 2 * δ) L).indicator (fun _ ↦ ENNReal.ofReal M) x :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal M * ENNReal.ofReal (L - (L - 2 * δ)) := by
      rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
    _ = ENNReal.ofReal (2 * δ * M) := by
      rw [← ENNReal.ofReal_mul hM]
      congr 1
      cas

/-- Endpoint flattening can have arbitrarily small weighted error and stay inside any
prescribed endpoint collar. The single constant `C` is obtained from the fixed smooth
transition; neither a localized error bound nor an approximation oracle is assumed. -/
theorem exists_endpointError_lt {f w v : ℝ → ℝ} {K : ℝ≥0} {L r A B ε : ℝ}
    (hf : LipschitzWith K f) (hfL : f L = 0)
    (hr : 0 < r) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ f x)
    (hw : ∀ x ∈ Ioo (L - r) L, w x ≤ A / (L - x) ^ 2)
    (hv : ∀ x ∈ Ioo (L - r) L, v x ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < r ∧
      singularWeightedH1Error w v (endpointError f L δ) L < ENNReal.ofReal ε := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_smoothTransition
  let M : ℝ := A * K ^ 2 + B * ((2 * C + 1) * K) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ : ℝ := min (r / 4) (ε / (4 * (M + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : 2 * δ < r := by
    have := min_le_left (r / 4) (ε / (4 * (M + 1)))
    change δ ≤ r / 4 at this
    cas
  have hδM : 2 * δ * M < ε := by
    have hd := min_le_right (r / 4) (ε / (4 * (M + 1)))
    change δ ≤ ε / (4 * (M + 1)) at hd
    have hd' := (le_div_iff₀ (show 0 < 4 * (M + 1) by positivity)).mp hd
    cas
  refine ⟨δ, hδ, hδr, ?_⟩
  have hsub : Ico (L - 2 * δ) L ⊆ Ioo (L - r) L := by
    intro x hx
    exact ⟨by have := hx.1; cas, hx.2⟩
  exact (singularWeightedH1Error_endpointError_le hf hfL hC hδ hA hB hfd
    (fun x hx ↦ hw x (hsub hx)) (fun x hx ↦ hv x (hsub hx))).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hε).2 hδM)

/-- Simultaneous flattening at the two endpoints, with an even smooth multiplier. -/
def flattenedProfile (f : ℝ → ℝ) (L δ x : ℝ) : ℝ :=
  endpointCutoff L δ x * endpointCutoff L δ (-x) * f x

/-- An odd input remains odd after endpoint flattening. -/
theorem flattenedProfile_neg {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x)
    (L δ x : ℝ) : flattenedProfile f L δ (-x) = -flattenedProfile f L δ x := by
  simp only [flattenedProfile, neg_neg, hf]
  cas

/-- Flattening fixes the entire inner interval, not just a finite jet at the origin. -/
theorem flattenedProfile_eq_self {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hx : |x| ≤ L - 2 * δ) : flattenedProfile f L δ x = f x := by
  rw [flattenedProfile,
    endpointCutoff_eq_one hδ ((le_abs_self x).trans hx),
    endpointCutoff_eq_one hδ ((neg_le_abs x).trans hx), one_mul, one_mul]

/-- Every local polynomial identity near the origin survives this cutoff exactly. -/
theorem flattenedProfile_eventuallyEq_self {f : ℝ → ℝ} {L δ : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ < L) :
    flattenedProfile f L δ =ᶠ[𝓝 0] f := by
  filter_upwards [Ioo_mem_nhds (show -(L - 2 * δ) < 0 by cas)
    (show 0 < L - 2 * δ by cas)] with x hx
  exact flattenedProfile_eq_self hδ (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)

/-- In particular the origin derivative, hence the prescribed slope, is unchanged. -/
theorem deriv_flattenedProfile_zero {f : ℝ → ℝ} {L δ : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ < L) :
    deriv (flattenedProfile f L δ) 0 = deriv f 0 :=
  (flattenedProfile_eventuallyEq_self hδ hL).deriv_eq

/-- The perturbation is identically zero on a neighborhood of the origin. -/
theorem flattenedProfile_sub_eventuallyEq_zero {f : ℝ → ℝ} {L δ : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ < L) :
    (fun x ↦ flattenedProfile f L δ x - f x) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  filter_upwards [flattenedProfile_eventuallyEq_self (f := f) hδ hL] with x hx
  exact sub_eq_zero.mpr hx

/-- The perturbation has zero origin derivative without any extra slope assumption. -/
theorem deriv_flattenedProfile_sub_zero {f : ℝ → ℝ} {L δ : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ < L) :
    deriv (fun x ↦ flattenedProfile f L δ x - f x) 0 = 0 := by
  rw [(flattenedProfile_sub_eventuallyEq_zero hδ hL).deriv_eq]
  exact deriv_const 0 0

/-- Both endpoint collars vanish, irrespective of the input's endpoint slopes. -/
theorem flattenedProfile_eq_zero {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hx : L - δ ≤ |x|) : flattenedProfile f L δ x = 0 := by
  rcases le_or_gt 0 x with hpos | hneg
  · have hx' : L - δ ≤ x := by simpa only [abs_of_nonneg hpos] using hx
    simp only [flattenedProfile, endpointCutoff_eq_zero hδ hx', zero_mul]
  · have hx' : L - δ ≤ -x := by simpa only [abs_of_neg hneg] using hx
    simp only [flattenedProfile, endpointCutoff_eq_zero hδ hx', mul_zero, zero_mul]

theorem tsupport_flattenedProfile_subset {f : ℝ → ℝ} {L δ : ℝ} (hδ : 0 < δ) :
    tsupport (flattenedProfile f L δ) ⊆ Icc (-(L - δ)) (L - δ) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hmem
  have habs : L - δ ≤ |x| := le_of_not_gt (fun h ↦ hmem
    (abs_le.mp h.le))
  exact hx (flattenedProfile_eq_zero hδ habs)

theorem hasCompactSupport_flattenedProfile {f : ℝ → ℝ} {L δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (flattenedProfile f L δ) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (tsupport_flattenedProfile_subset hδ)

/-- Interior regularity becomes global regularity once the endpoints have been flattened.
The order can be infinity, but this theorem does not upgrade a finitely smooth input. -/
theorem contDiff_flattenedProfile {f : ℝ → ℝ} {L δ : ℝ} {n : ℕ∞}
    (hδ : 0 < δ) (hf : ContDiffOn ℝ n f (Ioo (-L) L)) :
    ContDiff ℝ n (flattenedProfile f L δ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo (-L) L
  · exact ((contDiff_endpointCutoff L δ).contDiffAt.mul
      ((contDiff_endpointCutoff L δ).comp contDiff_neg).contDiffAt).mul
        (hf.contDiffAt (Ioo_mem_nhds hx.1 hx.2))
  · have hx' : L ≤ |x| := le_of_not_gt (fun h ↦ hx (abs_lt.mp h))
    have heq : flattenedProfile f L δ =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      have hlt : L - δ < |x| := by cas
      filter_upwards [((continuous_abs.tendsto x).eventually
        (eventually_gt_nhds hlt))] with y hy
      exact flattenedProfile_eq_zero hδ hy.le
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- On the positive interval the reflected cutoff is identically one. -/
theorem flattenedProfile_sub_eq_endpointError {f : ℝ → ℝ} {L δ x : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ ≤ L) (hx : 0 ≤ x) :
    flattenedProfile f L δ x - f x = endpointError f L δ x := by
  rw [flattenedProfile, endpointCutoff_eq_one hδ (show -x ≤ L - 2 * δ by cas),
    mul_one, endpointError]
  cas

/-- The symmetric error has the same derivative as the one-sided error
throughout the open positive half-line. -/
theorem flattenedProfile_sub_eventuallyEq_endpointError
    {f : ℝ → ℝ} {L δ x : ℝ} (hδ : 0 < δ) (hL : 2 * δ ≤ L) (hx : 0 < x) :
    (fun y ↦ flattenedProfile f L δ y - f y) =ᶠ[𝓝 x] endpointError f L δ := by
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact flattenedProfile_sub_eq_endpointError hδ hL hy.le

/-- The weighted estimate applies to the change of the symmetric profile. -/
theorem singularWeightedH1Error_flattenedProfile_sub {f w v : ℝ → ℝ} {L δ : ℝ}
    (hδ : 0 < δ) (hL : 2 * δ ≤ L) :
    singularWeightedH1Error w v (fun x ↦ flattenedProfile f L δ x - f x) L =
      singularWeightedH1Error w v (endpointError f L δ) L := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [flattenedProfile_sub_eq_endpointError hδ hL hx.1.le,
    (flattenedProfile_sub_eventuallyEq_endpointError hδ hL hx.1).deriv_eq]

/-- Qualitative endpoint approximation with one common witness: the input's interior
regularity becomes global, oddness is retained, the origin neighborhood is fixed exactly,
and the singular weighted squared error is arbitrarily small.

For the assembled Hermite profile use `n = 2`. Interior smoothing is still needed to
obtain an infinitely smooth initializer from that profile. -/
theorem exists_flattenedProfile_error_lt {f w v : ℝ → ℝ} {K : ℝ≥0}
    {L r A B ε : ℝ} {n : ℕ∞}
    (hf : LipschitzWith K f) (hfL : f L = 0) (hodd : ∀ x, f (-x) = -f x)
    (hregular : ContDiffOn ℝ n f (Ioo (-L) L))
    (hfd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ f x)
    (hr : 0 < r) (hrL : r < L) (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ x ∈ Ioo (L - r) L, w x ≤ A / (L - x) ^ 2)
    (hv : ∀ x ∈ Ioo (L - r) L, v x ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < r ∧
      ContDiff ℝ n (flattenedProfile f L δ) ∧
      HasCompactSupport (flattenedProfile f L δ) ∧
      (∀ x, flattenedProfile f L δ (-x) = -flattenedProfile f L δ x) ∧
      (∀ x, |x| ≤ L - r → flattenedProfile f L δ x = f x) ∧
      deriv (flattenedProfile f L δ) 0 = deriv f 0 ∧
      singularWeightedH1Error w v (fun x ↦ flattenedProfile f L δ x - f x) L <
        ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hδr, herror⟩ :=
    exists_endpointError_lt hf hfL hr hε hA hB hfd hw hv
  have hδL : 2 * δ < L := hδr.trans hrL
  refine ⟨δ, hδ, hδr, contDiff_flattenedProfile hδ hregular,
    hasCompactSupport_flattenedProfile hδ, flattenedProfile_neg hodd L δ,
    ?_, deriv_flattenedProfile_zero hδ hδL, ?_⟩
  · intro x hx
    exact flattenedProfile_eq_self hδ (by cas)
  · rwa [singularWeightedH1Error_flattenedProfile_sub hδ hδL.le]

end PDE.Analysis.Calculus
