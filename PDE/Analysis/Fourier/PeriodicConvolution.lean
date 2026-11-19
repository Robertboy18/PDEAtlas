/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier coefficients on an interval: convolution over a period and comparison in `L²`

For `a < b`, Mathlib's `fourierCoeffOn hab f n` is the `n`-th Fourier coefficient of `f` on
`[a, b]`, the integral of `exp (-2 π i n x / (b - a)) f (x)` over `[a, b]` divided by `b - a`.
Two facts about these coefficients are proved here, for every interval `[a, b]` with `a < b`.

* `PDE.Analysis.fourierCoeffOn_convolution`: the coefficients of the convolution over a period
  `x ↦ ∫ₐᵇ g (x - z) k (z) dz` are `b - a` times the products of the coefficients of `g` and `k`,
  for every continuous `g` of period `b - a` and every interval integrable `k`.
* `PDE.Analysis.integral_norm_sq_le_of_norm_fourierCoeffOn_le`: if the coefficients of `u` are
  bounded by `C` times those of `v`, then `∫ₐᵇ ‖u‖² ≤ C² ∫ₐᵇ ‖v‖²`, for all complex functions `u`,
  `v` that are square integrable on `(a, b]`. So a Fourier multiplier with a bounded symbol is
  bounded on `L²` of a period. `PDE.Analysis.integral_sq_le_of_norm_fourierCoeffOn_le` is the case
  of real continuous functions.

`IntervalIntegrable.ofReal` embeds a real interval integrable function into `ℝ` or `ℂ`.

## How it works

The character `e (x) = exp (-2 π i n x / (b - a))` is multiplicative, `e (x) = e (x - z) e (z)`,
and `e g` has period `b - a`, so its integral over `[a - z, b - z]` is its integral over `[a, b]`.
The integrand `e (x) g (x - z) k (z)` is integrable on the square, because `g` is bounded on a
compact set and `k` is integrable, so Fubini's theorem exchanges the two integrals. The comparison
in `L²` is Parseval's identity `hasSum_sq_fourierCoeffOn` for both functions.

These are standard facts of Fourier series; no source was consulted for them.
-/

@[expose] public noncomputable section

open MeasureTheory Set

/-- The embedding into `ℝ` or `ℂ` of a real interval integrable function is interval
integrable. -/
theorem IntervalIntegrable.ofReal {𝕜 : Type*} [RCLike 𝕜] {g : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x ↦ (g x : 𝕜)) μ a b :=
  ⟨hg.1.ofReal, hg.2.ofReal⟩

namespace PDE.Analysis

/-- **The Fourier coefficients of a convolution over a period.** For a continuous function `g` of
period `b - a` and an interval integrable function `k`, the `n`-th Fourier coefficient on `[a, b]`
of `x ↦ ∫ₐᵇ g (x - z) k (z) dz` is `b - a` times the product of the `n`-th coefficients of `g` and
`k`. -/
theorem fourierCoeffOn_convolution {a b : ℝ} (hab : a < b) {g k : ℝ → ℂ} (hg : Continuous g)
    (hper : g.Periodic (b - a)) (hk : IntervalIntegrable k volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun x ↦ ∫ z in a..b, g (x - z) * k z) n =
      (b - a) * fourierCoeffOn hab g n * fourierCoeffOn hab k n := by
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℂ, ∀ x, e x = fourier (-n) (x : AddCircle (b - a)) :=
    ⟨_, fun _ ↦ rfl⟩
  have hec : Continuous e := by
    rw [funext he]
    exact (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hmul : ∀ x z : ℝ, e x = e (x - z) * e z := by
    intro x z
    simp only [he, fourier_coe_apply]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    cas
  have hper' : (fun x ↦ e x * g x).Periodic (b - a) := by
    intro x
    simp only [he]
    rw [AddCircle.coe_add_period, hper x]
  have hint : IntegrableOn (Function.uncurry fun x z ↦ e x * (g (x - z) * k z))
      (uIoc a b ×ˢ uIoc a b) := by
    rw [uIoc_of_le hab.le]
    have hφ : Continuous fun p : ℝ × ℝ ↦ e p.1 * g (p.1 - p.2) := by fun_prop
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := a) (b := b)).prod
      (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn hφ.continuousOn
    have hk' : Integrable (fun p : ℝ × ℝ ↦ k p.2)
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
      Integrable.comp_snd ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hk) _
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine (hk'.bdd_mul (c := C) hφ.aestronglyMeasurable ?_).congr (ae_of_all _ fun p ↦ ?_)
    · rw [Measure.prod_restrict]
      exact ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc)
        fun p hp ↦ hC p (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hp)
    · exact mul_assoc _ _ _
  have hinner : ∀ z : ℝ, ∫ x in a..b, e x * (g (x - z) * k z) =
      (∫ x in a..b, e x * g x) * (e z * k z) := by
    intro z
    have h2 : ∀ x : ℝ, e x * (g (x - z) * k z) = e (x - z) * g (x - z) * (e z * k z) :=
      fun x ↦ by rw [hmul x z]; cas
    have h3 : ∫ x in a..b, e (x - z) * g (x - z) = ∫ x in a - z..b - z, e x * g x :=
      intervalIntegral.integral_comp_sub_right (fun y ↦ e y * g y) z
    have h4 := hper'.intervalIntegral_add_eq (a - z) a
    rw [show a - z + (b - a) = b - z by cas, show a + (b - a) = b by cas] at h4
    simp only [h2]
    rw [intervalIntegral.integral_mul_const, h3, h4]
  have hkey : ∫ x in a..b, e x * ∫ z in a..b, g (x - z) * k z =
      (∫ x in a..b, e x * g x) * ∫ z in a..b, e z * k z := by
    calc ∫ x in a..b, e x * ∫ z in a..b, g (x - z) * k z
        = ∫ x in a..b, ∫ z in a..b, e x * (g (x - z) * k z) := by
          simp only [intervalIntegral.integral_const_mul]
      _ = ∫ z in a..b, ∫ x in a..b, e x * (g (x - z) * k z) :=
          intervalIntegral_intervalIntegral_swap hint
      _ = ∫ z in a..b, (∫ x in a..b, e x * g x) * (e z * k z) := by
          simp only [hinner]
      _ = (∫ x in a..b, e x * g x) * ∫ z in a..b, e z * k z := by
          rw [intervalIntegral.integral_const_mul]
  have hne : (b : ℂ) - a ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne'
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [← he, smul_eq_mul]
  rw [hkey]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub]
  cas using [hne]

/-- **Comparison of `L²` norms through Fourier coefficients.** If the Fourier coefficients on
`[a, b]` of `u` are bounded by `C` times those of `v`, and `u`, `v` are square integrable on
`(a, b]`, then `∫ₐᵇ ‖u‖² ≤ C² ∫ₐᵇ ‖v‖²`, by Parseval's identity `hasSum_sq_fourierCoeffOn`. -/
theorem integral_norm_sq_le_of_norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioc a b))) (hv : MemLp v 2 (volume.restrict (Ioc a b)))
    {C : ℝ} (h : ∀ n, ‖fourierCoeffOn hab u n‖ ≤ C * ‖fourierCoeffOn hab v n‖) :
    ∫ x in a..b, ‖u x‖ ^ 2 ≤ C ^ 2 * ∫ x in a..b, ‖v x‖ ^ 2 := by
  have hle : ∀ n, ‖fourierCoeffOn hab u n‖ ^ 2 ≤ C ^ 2 * ‖fourierCoeffOn hab v n‖ ^ 2 :=
    fun n ↦ by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (h n) 2
  have hsum := hasSum_le hle (hasSum_sq_fourierCoeffOn hab hu)
    ((hasSum_sq_fourierCoeffOn hab hv).mul_left (C ^ 2))
  simp only [smul_eq_mul] at hsum
  rw [mul_left_comm (C ^ 2)] at hsum
  exact le_of_mul_le_mul_left hsum (inv_pos.mpr (sub_pos.mpr hab))

/-- If the Fourier coefficients on `[a, b]` of a real continuous function `u` are bounded by `C`
times those of a real continuous function `v`, then `∫ₐᵇ u² ≤ C² ∫ₐᵇ v²`: the case of real
continuous functions of `integral_norm_sq_le_of_norm_fourierCoeffOn_le`. -/
theorem integral_sq_le_of_norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {C : ℝ}
    (h : ∀ n, ‖fourierCoeffOn hab (fun x ↦ (u x : ℂ)) n‖ ≤
      C * ‖fourierCoeffOn hab (fun x ↦ (v x : ℂ)) n‖) :
    ∫ x in a..b, u x ^ 2 ≤ C ^ 2 * ∫ x in a..b, v x ^ 2 := by
  have hmem : ∀ {w : ℝ → ℝ}, Continuous w →
      MemLp (fun x ↦ (w x : ℂ)) 2 (volume.restrict (Ioc a b)) := by
    intro w hw
    have hc : Continuous fun x ↦ (w x : ℂ) := Complex.continuous_ofReal.comp hw
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      (Continuous.integrableOn_Ioc (by fun_prop))
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    integral_norm_sq_le_of_norm_fourierCoeffOn_le hab (hmem hu) (hmem hv) h

end PDE.Analysis
