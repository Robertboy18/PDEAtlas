/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.FiniteRankResponse.Discontinuous
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Scalar linear equations with a stopped forcing and a jump

Chen and Hou, Part II, Section 3.5, solve the equation of a correction coefficient
`a' = c a - F_ext`, `F_ext = F 1_{t ≤ T} - F_end δ_T`, exactly for all times by Duhamel's formula
(3.33):
`a(t) = e^{c t} a(0) - ∫₀^{min(t, T)} e^{c (t - s)} F(s) ds + 1_{T ≤ t} F_end e^{c (t - T)}`
(`stoppedDuhamel c a₀ T J f`, with `J = F_end`). The forcing is the numerical residual of the
mode, which is computed only up to the stopping time `T`; the jump `J` of the coefficient at `T`
is the end trace that the stopping removes from the mode.

## Main definitions

* `stoppedDuhamel`: the solution (3.33) of `a' = c a - f` on `[0, T)`, with the forcing switched
  off after the stopping time `T` and the jump `J` at `T`.

## Main results

* `stoppedDuhamel_of_le`: the exact exponential tail, `a(t) = e^{c (t - T)} a(T)` for `t ≥ T`,
  where `a(T)` contains the jump.
* `tendsto_stoppedDuhamel_stop`: the left limit at the stopping time is `a(T) - J`.
* `hasDerivAt_stoppedDuhamel_of_lt`: `a' = c a - f` on `(0, T)` where `f` is continuous; after
  `T`, `a' = c a` (`hasDerivAt_stoppedDuhamel_of_gt`).
* `hasDerivWithJump_stoppedDuhamel`: the integrated form
  `a(τ) = a(0) + ∫₀^τ (c a - 1_{· < T} f) + 1_{T ≤ τ} J` (`HasDerivWithJump`), for a forcing
  that is integrable on `[0, T]` and continuous off a countable set (piecewise polynomial
  forcings qualify); `hasDerivWithJump_deriv_stoppedDuhamel` is the form with Lean's `deriv`.
* `aemeasurable_stoppedDuhamel`: measurability on `(0, ∞)`, for the tail estimates.
* `lintegral_enorm_stoppedDuhamel_le`: for `c < 0`,
  `∫₀^∞ |a| ≤ (|a(0)| + ∫₀^T |f| + |J|) / |c|`, the bound after (3.36).
* `hasDerivWithJump_triangular`: the diagonalization (3.32) of the triangular system
  `a₁' = λ₁ a₁ + μ a₂ - F₁`, `a₂' = λ₂ a₂ - F₂` through `ã₁ = a₁ + μ a₂ / (λ₁ - λ₂)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 3.3,
  (3.20)-(3.21), and Section 3.5, (3.32)-(3.36) and the bound after (3.36).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval ENNReal

namespace PDE.Analysis.Evolution

/-- **Part II (3.33).** The solution
`e^{c t} a₀ - ∫₀^{min(t, T)} e^{c (t - s)} f(s) ds + 1_{T ≤ t} J e^{c (t - T)}` of `a' = c a - f`
on `[0, T)`, with the forcing switched off after the stopping time `T` and the jump `J` at `T`. -/
def stoppedDuhamel (c a₀ T J : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (c * t) * a₀ - (∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * f s) +
    if T ≤ t then J * Real.exp (c * (t - T)) else 0

variable {c a₀ T J t : ℝ} {f : ℝ → ℝ}

/-- The solution through the integrating factor `e^{-c s}`. -/
theorem stoppedDuhamel_eq (c a₀ T J : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    stoppedDuhamel c a₀ T J f t =
      Real.exp (c * t) * (a₀ - ∫ s in (0 : ℝ)..min t T, Real.exp (-c * s) * f s) +
        if T ≤ t then J * Real.exp (c * (t - T)) else 0 := by
  have h : ∀ s, Real.exp (c * (t - s)) * f s =
      Real.exp (c * t) * (Real.exp (-c * s) * f s) := fun s ↦ by
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  simp only [stoppedDuhamel, h, intervalIntegral.integral_const_mul]
  ring

/-- **The exact exponential tail.** From the stopping time on, the solution is
`e^{c (t - T)} a(T)`; the value `a(T)` contains the jump. -/
theorem stoppedDuhamel_of_le (ht : T ≤ t) :
    stoppedDuhamel c a₀ T J f t = Real.exp (c * (t - T)) * stoppedDuhamel c a₀ T J f T := by
  rw [stoppedDuhamel_eq, stoppedDuhamel_eq, min_eq_right ht, min_self, ite_eq_left ht,
    ite_eq_left le_rfl, sub_self, mul_zero, Real.exp_zero, mul_one]
  have : Real.exp (c * t) = Real.exp (c * (t - T)) * Real.exp (c * T) := by
    rw [← Real.exp_add]
    ring_nf
  rw [this]
  ring

/-- The value at the stopping time: the solution of the forced equation up to `T` plus the jump. -/
theorem stoppedDuhamel_stop :
    stoppedDuhamel c a₀ T J f T =
      Real.exp (c * T) * a₀ - (∫ s in (0 : ℝ)..T, Real.exp (c * (T - s)) * f s) + J := by
  simp [stoppedDuhamel]

/-- Before the stopping time the solution is the forced Duhamel formula. -/
theorem stoppedDuhamel_of_lt (ht : t < T) :
    stoppedDuhamel c a₀ T J f t =
      Real.exp (c * t) * (a₀ - ∫ s in (0 : ℝ)..t, Real.exp (-c * s) * f s) := by
  rw [stoppedDuhamel_eq, min_eq_left ht.le, ite_eq_right (not_le.2 ht), add_zero]

/-- The solution shifted by `J` before the stopping time, which is continuous. -/
theorem stoppedDuhamel_add_ite (t : ℝ) :
    stoppedDuhamel c a₀ T J f t + (if t < T then J else 0) =
      Real.exp (c * t) * (a₀ - ∫ s in (0 : ℝ)..min t T, Real.exp (-c * s) * f s) +
        J * Real.exp (c * (max t T - T)) := by
  rw [stoppedDuhamel_eq]
  rcases lt_or_ge t T with h | h
  · rw [ite_eq_right (not_le.2 h), ite_eq_left h, max_eq_right h.le, sub_self, mul_zero,
      Real.exp_zero, mul_one, add_zero]
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h), max_eq_left h, add_zero]

/-- The weighted forcing `s ↦ exp (-c s) f(s)` is integrable on `[0, T]` when `f` is. -/
theorem intervalIntegrable_exp_mul (hf : IntervalIntegrable f volume 0 T) (c : ℝ) :
    IntervalIntegrable (fun s ↦ Real.exp (-c * s) * f s) volume 0 T :=
  hf.continuousOn_mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)

/-- The shifted solution is continuous on `[0, ∞)`. -/
theorem continuousOn_stoppedDuhamel_add_ite (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) :
    ContinuousOn (fun t ↦ stoppedDuhamel c a₀ T J f t + if t < T then J else 0) (Ici 0) := by
  simp only [stoppedDuhamel_add_ite]
  have hP : ContinuousOn (fun u ↦ ∫ s in (0 : ℝ)..u, Real.exp (-c * s) * f s) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_exp_mul hf c)
      (show (0 : ℝ) ∈ [[0, T]] from Set.left_mem_uIcc)
    rwa [Set.uIcc_of_le hT] at this
  have hmin : ContinuousOn (fun t : ℝ ↦ ∫ s in (0 : ℝ)..min t T, Real.exp (-c * s) * f s)
      (Ici 0) :=
    hP.comp (continuous_id.min continuous_const).continuousOn fun t ht ↦
      ⟨le_min ht hT, min_le_right _ _⟩
  refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    (continuousOn_const.sub hmin)).add ?_
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_id.max continuous_const).sub continuous_const)))).continuousOn

/-- **The left limit at the stopping time** is `a(T) - J`. -/
theorem tendsto_stoppedDuhamel_stop (hT : 0 < T) (hf : IntervalIntegrable f volume 0 T) :
    Tendsto (stoppedDuhamel c a₀ T J f) (𝓝[<] T) (𝓝 (stoppedDuhamel c a₀ T J f T - J)) := by
  have hcont := continuousOn_stoppedDuhamel_add_ite (c := c) (a₀ := a₀) (J := J) hT.le hf
  have h₁ : ContinuousWithinAt
      (fun t ↦ stoppedDuhamel c a₀ T J f t + if t < T then J else 0) (Ioo 0 T) T :=
    (hcont T hT.le).mono fun t ht ↦ ht.1.le
  rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hT, ite_eq_right (lt_irrefl T),
    add_zero] at h₁
  refine (h₁.sub_const J).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t < T)
  rw [ite_eq_left ht, add_sub_cancel_right]

/-- The solution is continuous on `[0, T)`. -/
theorem continuousOn_stoppedDuhamel_Ico (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) :
    ContinuousOn (stoppedDuhamel c a₀ T J f) (Ico 0 T) := by
  have hcont := continuousOn_stoppedDuhamel_add_ite (c := c) (a₀ := a₀) (J := J) hT hf
  have h : ContinuousOn (fun t ↦ (stoppedDuhamel c a₀ T J f t + if t < T then J else 0) - J)
      (Ico 0 T) :=
    (hcont.mono Ico_subset_Ici_self).sub continuousOn_const
  refine h.congr fun t ht ↦ ?_
  simp [ite_eq_left ht.2]

/-- The solution is continuous on `[T, ∞)`. -/
theorem continuousOn_stoppedDuhamel_Ici :
    ContinuousOn (stoppedDuhamel c a₀ T J f) (Ici T) := by
  have h : Continuous fun t ↦ Real.exp (c * (t - T)) * stoppedDuhamel c a₀ T J f T :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
      continuous_const
  exact h.continuousOn.congr fun t ht ↦ stoppedDuhamel_of_le ht

/-- **The equation before the stopping time.** At a time `t ∈ (0, T)` where `f` is continuous,
`a' = c a - f`. -/
theorem hasDerivAt_stoppedDuhamel_of_lt (hf : IntervalIntegrable f volume 0 T) (h0 : 0 < t)
    (ht : t < T) (hfc : ContinuousAt f t) :
    HasDerivAt (stoppedDuhamel c a₀ T J f) (c * stoppedDuhamel c a₀ T J f t - f t) t := by
  have hg := intervalIntegrable_exp_mul hf c
  have hgt : IntervalIntegrable (fun s ↦ Real.exp (-c * s) * f s) volume 0 t :=
    hg.mono_set (by rw [Set.uIcc_of_le h0.le, Set.uIcc_of_le (h0.trans ht).le]
                    exact Icc_subset_Icc le_rfl ht.le)
  have hmeas : StronglyMeasurableAtFilter (fun s ↦ Real.exp (-c * s) * f s) (𝓝 t) :=
    ⟨Ioo 0 T, Ioo_mem_nhds h0 ht, (hg.1.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable⟩
  have hP := intervalIntegral.integral_hasDerivAt_right hgt hmeas
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).mul hfc)
  have hE : HasDerivAt (fun s ↦ Real.exp (c * s)) (Real.exp (c * t) * c) t := by
    simpa using ((hasDerivAt_id t).const_mul c).exp
  have hH := hE.mul (hP.const_sub a₀)
  refine (hH.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Iio_mem_nhds ht] with s hs
    exact stoppedDuhamel_of_lt hs
  · rw [stoppedDuhamel_of_lt ht]
    have : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
      rw [← Real.exp_add]
      simp
    linear_combination (-(f t)) * this

/-- **The equation after the stopping time.** For `t > T`, `a' = c a`. -/
theorem hasDerivAt_stoppedDuhamel_of_gt (ht : T < t) :
    HasDerivAt (stoppedDuhamel c a₀ T J f) (c * stoppedDuhamel c a₀ T J f t) t := by
  have h : HasDerivAt (fun s ↦ Real.exp (c * (s - T)) * stoppedDuhamel c a₀ T J f T)
      (Real.exp (c * (t - T)) * c * stoppedDuhamel c a₀ T J f T) t := by
    have := (((hasDerivAt_id t).sub_const T).const_mul c).exp.mul_const
      (stoppedDuhamel c a₀ T J f T)
    simpa using this
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact stoppedDuhamel_of_le hs.le
  · rw [stoppedDuhamel_of_le ht.le]
    ring

/-- The solution is a.e. measurable on `(0, ∞)`. -/
theorem aemeasurable_stoppedDuhamel (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) :
    AEMeasurable (stoppedDuhamel c a₀ T J f) (volume.restrict (Ioi 0)) := by
  have hcont := continuousOn_stoppedDuhamel_add_ite (c := c) (a₀ := a₀) (J := J) hT hf
  have h₁ : AEMeasurable (fun t ↦ stoppedDuhamel c a₀ T J f t + if t < T then J else 0)
      (volume.restrict (Ioi 0)) :=
    (hcont.mono Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi
  have h₂ : Measurable fun t : ℝ ↦ if t < T then J else 0 :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  exact (h₁.sub h₂.aemeasurable).congr (Filter.Eventually.of_forall fun t ↦ by simp)

/-- The derivative `c a - 1_{· < T} f` of the integrated form. -/
def stoppedDuhamelDeriv (c a₀ T J : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  c * stoppedDuhamel c a₀ T J f t - if t < T then f t else 0

/-- The stopped solution is integrable on every interval `[0, τ]`. -/
theorem integrableOn_stoppedDuhamel (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T)
    (τ : ℝ) : IntegrableOn (stoppedDuhamel c a₀ T J f) (Icc 0 τ) := by
  have hcont := continuousOn_stoppedDuhamel_add_ite (c := c) (a₀ := a₀) (J := J) hT hf
  have h₁ : IntegrableOn (fun t ↦ stoppedDuhamel c a₀ T J f t + if t < T then J else 0)
      (Icc 0 τ) := (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  have h₂ : IntegrableOn (fun t : ℝ ↦ if t < T then J else 0) (Icc 0 τ) := by
    have : (fun t : ℝ ↦ if t < T then J else 0) = (Iio T).indicator fun _ ↦ J := by
      funext t
      by_cases h : t < T <;> simp [h]
    rw [this]
    exact (integrableOn_const (by simp)).indicator measurableSet_Iio
  refine (h₁.sub h₂).congr_fun (fun t _ ↦ ?_) measurableSet_Icc
  simp

/-- The stopped forcing `1_{· < T} f` is integrable on every interval `[0, τ]` when `f` is
integrable on `[0, T]`. -/
theorem integrableOn_ite_forcing (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) (τ : ℝ) :
    IntegrableOn (fun t ↦ if t < T then f t else 0) (Icc 0 τ) := by
  have : (fun t ↦ if t < T then f t else 0) = (Iio T).indicator f := by
    funext t
    by_cases h : t < T <;> simp [h]
  rw [this, integrableOn_indicator_iff measurableSet_Iio.nullMeasurableSet]
  refine ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hf).mono_set fun t ht ↦ ?_
  exact ⟨ht.2.1, ht.1.le⟩

/-- **The integrated form with the jump.** If `f` is integrable on `[0, T]`, `T > 0`, and
continuous on `(0, T)` off a countable set, then
`a(τ) = a(0) + ∫₀^τ (c a - 1_{· < T} f) + 1_{T ≤ τ} J` for `τ ≥ 0`. -/
theorem hasDerivWithJump_stoppedDuhamel (hT : 0 < T) (hf : IntervalIntegrable f volume 0 T)
    {C : Set ℝ} (hC : C.Countable) (hfc : ∀ t ∈ Ioo 0 T \ C, ContinuousAt f t) :
    HasDerivWithJump (stoppedDuhamel c a₀ T J f) (stoppedDuhamelDeriv c a₀ T J f) T J where
  integrableOn τ :=
    ((integrableOn_stoppedDuhamel hT.le hf τ).const_mul c).sub (integrableOn_ite_forcing hT.le hf τ)
  eq_add τ hτ := by
    set H : ℝ → ℝ := fun t ↦ stoppedDuhamel c a₀ T J f t + if t < T then J else 0 with hH
    have hcont := continuousOn_stoppedDuhamel_add_ite (c := c) (a₀ := a₀) (J := J) hT.le hf
    have hint : IntervalIntegrable (stoppedDuhamelDeriv c a₀ T J f) volume 0 τ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2
        (((integrableOn_stoppedDuhamel hT.le hf τ).const_mul c).sub
          (integrableOn_ite_forcing hT.le hf τ))
    have hderiv : ∀ x ∈ Ioo 0 τ \ (C ∪ {T}), HasDerivAt H (stoppedDuhamelDeriv c a₀ T J f x) x := by
      rintro x ⟨hx, hxC⟩
      simp only [mem_union, mem_singleton_iff, not_or] at hxC
      rcases lt_or_gt_of_ne hxC.2 with hlt | hgt
      · have h := (hasDerivAt_stoppedDuhamel_of_lt (c := c) (a₀ := a₀) (J := J) hf hx.1 hlt
          (hfc x ⟨⟨hx.1, hlt⟩, hxC.1⟩)).add_const J
        refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [Iio_mem_nhds hlt] with s hs
          simp [hH, ite_eq_left (show s < T from hs)]
        · simp [stoppedDuhamelDeriv, ite_eq_left hlt]
      · have h := hasDerivAt_stoppedDuhamel_of_gt (c := c) (a₀ := a₀) (J := J) (f := f) hgt
        refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [Ioi_mem_nhds hgt] with s hs
          simp [hH, ite_eq_right (show ¬ s < T from not_lt.2 (le_of_lt hs))]
        · simp [stoppedDuhamelDeriv, ite_eq_right (not_lt.2 hgt.le)]
    have hftc := integral_eq_of_hasDerivAt_off_countable_of_le H (stoppedDuhamelDeriv c a₀ T J f)
      hτ (hC.union (countable_singleton T)) (hcont.mono Icc_subset_Ici_self) hderiv hint
    rw [hftc]
    simp only [hH, ite_eq_left hT]
    by_cases h : T ≤ τ
    · rw [ite_eq_right (not_lt.2 h), ite_eq_left h]
      ring
    · rw [ite_eq_left (not_le.1 h), ite_eq_right h]
      ring

/-- **The integrated form with Lean's derivative.** -/
theorem hasDerivWithJump_deriv_stoppedDuhamel (hT : 0 < T)
    (hf : IntervalIntegrable f volume 0 T) {C : Set ℝ} (hC : C.Countable)
    (hfc : ∀ t ∈ Ioo 0 T \ C, ContinuousAt f t) :
    HasDerivWithJump (stoppedDuhamel c a₀ T J f)
      (fun t ↦ deriv (stoppedDuhamel c a₀ T J f) t) T J := by
  refine (hasDerivWithJump_stoppedDuhamel hT hf hC hfc).congr_of_countable
    (hC.union (countable_singleton T)) fun t ht htC ↦ ?_
  simp only [mem_union, mem_singleton_iff, not_or] at htC
  rcases lt_or_gt_of_ne htC.2 with hlt | hgt
  · rw [(hasDerivAt_stoppedDuhamel_of_lt hf ht hlt (hfc t ⟨⟨ht, hlt⟩, htC.1⟩)).deriv,
      stoppedDuhamelDeriv, ite_eq_left hlt]
  · rw [(hasDerivAt_stoppedDuhamel_of_gt hgt).deriv, stoppedDuhamelDeriv,
      ite_eq_right (not_lt.2 hgt.le), sub_zero]

/-! ### The integral of the absolute value -/

/-- The integral of `exp (c (t - s)) (-|f s|)` over `[0, u]` is minus the integral of `exp (c (t -
s)) |f s|`. -/
theorem integral_exp_mul_neg_abs (c t : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    ∫ s in (0 : ℝ)..u, Real.exp (c * (t - s)) * -|f s| =
      -∫ s in (0 : ℝ)..u, Real.exp (c * (t - s)) * |f s| := by
  simp only [mul_neg, intervalIntegral.integral_neg]

/-- The comparison solution with `|a₀|`, `|J|` and the forcing `-|f|` is nonnegative. -/
theorem stoppedDuhamel_abs_nonneg (hT : 0 ≤ T) (ht : 0 ≤ t) :
    0 ≤ stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) t := by
  rw [stoppedDuhamel, integral_exp_mul_neg_abs, sub_neg_eq_add]
  have hI : 0 ≤ ∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * |f s| :=
    intervalIntegral.integral_nonneg (le_min ht hT) fun s _ ↦
      mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hJ : 0 ≤ if T ≤ t then |J| * Real.exp (c * (t - T)) else 0 := by
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    · exact le_rfl
  have := mul_nonneg (Real.exp_pos (c * t)).le (abs_nonneg a₀)
  linarith

/-- `|a(t)|` is bounded by the comparison solution. -/
theorem abs_stoppedDuhamel_le (hT : 0 ≤ T) (ht : 0 ≤ t) :
    |stoppedDuhamel c a₀ T J f t| ≤ stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) t := by
  rw [stoppedDuhamel, stoppedDuhamel, integral_exp_mul_neg_abs, sub_neg_eq_add]
  have hI : |∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * f s| ≤
      ∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * |f s| := by
    refine (intervalIntegral.abs_integral_le_integral_abs (le_min ht hT)).trans_eq ?_
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    simp [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hJ : |if T ≤ t then J * Real.exp (c * (t - T)) else 0| ≤
      if T ≤ t then |J| * Real.exp (c * (t - T)) else 0 := by
    split_ifs
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    · simp
  have ha : |Real.exp (c * t) * a₀| = Real.exp (c * t) * |a₀| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |Real.exp (c * t) * a₀ - (∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * f s) +
        if T ≤ t then J * Real.exp (c * (t - T)) else 0|
      ≤ |Real.exp (c * t) * a₀ - (∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * f s)| +
          |if T ≤ t then J * Real.exp (c * (t - T)) else 0| := abs_add_le _ _
    _ ≤ |Real.exp (c * t) * a₀| + |∫ s in (0 : ℝ)..min t T, Real.exp (c * (t - s)) * f s| +
          |if T ≤ t then J * Real.exp (c * (t - T)) else 0| := by
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by rw [ha]; gcongr

/-- The forcing part of the comparison solution is at most `∫₀^T |f|`. -/
theorem integral_ite_abs_le (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    ∫ r in (0 : ℝ)..τ, (if r < T then |f r| else 0) ≤ ∫ s in (0 : ℝ)..T, |f s| := by
  have hle : ∀ r, (if r < T then |f r| else 0) ≤ |f r| := fun r ↦ by
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  have hi : ∀ σ, 0 ≤ σ →
      IntervalIntegrable (fun r ↦ if r < T then |f r| else 0) volume 0 σ := fun σ hσ ↦
    (intervalIntegrable_iff_integrableOn_Icc_of_le hσ).2
      (integrableOn_ite_forcing (f := fun r ↦ |f r|) hT hf.abs σ)
  rcases le_or_gt τ T with h | h
  · refine (intervalIntegral.integral_mono_on hτ (hi τ hτ)
      (hf.abs.mono_set (by rw [Set.uIcc_of_le hτ, Set.uIcc_of_le hT]
                           exact Icc_subset_Icc le_rfl h)) fun r _ ↦ hle r).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hτ h
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _) hf.abs
  · have hzero : ∫ r in T..τ, (if r < T then |f r| else 0) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)), intervalIntegral.integral_zero]
      intro r hr
      rw [Set.uIcc_of_le h.le] at hr
      simp [ite_eq_right (not_lt.2 hr.1)]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi T hT)
      (((hi τ hτ).mono_set (by rw [Set.uIcc_of_le hτ, Set.uIcc_of_le h.le]
                               exact Icc_subset_Icc hT le_rfl))), hzero, add_zero]
    exact intervalIntegral.integral_mono_on hT (hi T hT) hf.abs fun r _ ↦ hle r

/-- The comparison solution has `∫₀^τ b ≤ (|a₀| + ∫₀^T |f| + |J|) / |c|` for `c < 0`. -/
theorem integral_stoppedDuhamel_abs_le (hc : c < 0) (hT : 0 < T)
    (hf : IntervalIntegrable f volume 0 T) {C : Set ℝ} (hC : C.Countable)
    (hfc : ∀ t ∈ Ioo 0 T \ C, ContinuousAt f t) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ t in (0 : ℝ)..τ, stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) t ≤
      (|a₀| + (∫ s in (0 : ℝ)..T, |f s|) + |J|) / -c := by
  have hg : IntervalIntegrable (fun s ↦ -|f s|) volume 0 T := hf.abs.neg
  have hgc : ∀ t ∈ Ioo 0 T \ C, ContinuousAt (fun s ↦ -|f s|) t := fun t ht ↦
    (hfc t ht).abs.neg
  have hJ := (hasDerivWithJump_stoppedDuhamel (c := c) (a₀ := |a₀|) (J := |J|) hT hg hC
    hgc).eq_add τ hτ
  have hb0 : stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) 0 = |a₀| := by
    simp [stoppedDuhamel, ite_eq_right (not_le.2 hT), min_eq_left hT.le]
  have hbi : IntervalIntegrable (stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|)) volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2 (integrableOn_stoppedDuhamel hT.le hg τ)
  have hfi : IntervalIntegrable (fun r ↦ if r < T then |f r| else 0) volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2
      (integrableOn_ite_forcing (f := fun r ↦ |f r|) hT.le hf.abs τ)
  have hsplit : ∫ r in (0 : ℝ)..τ, stoppedDuhamelDeriv c |a₀| T |J| (fun s ↦ -|f s|) r =
      c * (∫ r in (0 : ℝ)..τ, stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) r) +
        ∫ r in (0 : ℝ)..τ, (if r < T then |f r| else 0) := by
    have h₁ : (fun r ↦ stoppedDuhamelDeriv c |a₀| T |J| (fun s ↦ -|f s|) r) =
        fun r ↦ c * stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) r +
          (if r < T then |f r| else 0) := by
      funext r
      simp only [stoppedDuhamelDeriv]
      split_ifs <;> ring
    rw [h₁, intervalIntegral.integral_add (hbi.const_mul c) hfi,
      intervalIntegral.integral_const_mul]
  rw [hb0, hsplit] at hJ
  have hbτ := stoppedDuhamel_abs_nonneg (c := c) (a₀ := a₀) (J := J) (f := f) hT.le hτ
  have hIf := integral_ite_abs_le hT.le hf hτ
  have hJle : (if T ≤ τ then |J| else 0) ≤ |J| := by
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  rw [le_div_iff₀ (neg_pos.2 hc)]
  nlinarith

/-- **The `L¹` bound of the coefficient**, Part II after (3.36): for `c < 0`,
`∫₀^∞ |a| ≤ (|a(0)| + ∫₀^T |f| + |J|) / |c|`. -/
theorem lintegral_enorm_stoppedDuhamel_le (hc : c < 0) (hT : 0 < T)
    (hf : IntervalIntegrable f volume 0 T) {C : Set ℝ} (hC : C.Countable)
    (hfc : ∀ t ∈ Ioo 0 T \ C, ContinuousAt f t) :
    ∫⁻ t in Ioi 0, ‖stoppedDuhamel c a₀ T J f t‖ₑ ≤
      ENNReal.ofReal ((|a₀| + (∫ s in (0 : ℝ)..T, |f s|) + |J|) / -c) := by
  set b := stoppedDuhamel c |a₀| T |J| (fun s ↦ -|f s|) with hb
  set K := (|a₀| + (∫ s in (0 : ℝ)..T, |f s|) + |J|) / -c
  have hg : IntervalIntegrable (fun s ↦ -|f s|) volume 0 T := hf.abs.neg
  have hnn : ∀ t, 0 ≤ t → 0 ≤ b t := fun t ht ↦ stoppedDuhamel_abs_nonneg hT.le ht
  have hint : IntegrableOn b (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded K 0
      (fun n : ℕ ↦ (integrableOn_stoppedDuhamel hT.le hg (n : ℝ)).mono_set Ioc_subset_Icc_self)
      tendsto_natCast_atTop_atTop (Filter.Eventually.of_forall fun n ↦ ?_)
    rw [intervalIntegral.integral_congr (g := b) fun t ht ↦ ?_]
    · exact integral_stoppedDuhamel_abs_le hc hT hf hC hfc (Nat.cast_nonneg n)
    · rw [Set.uIcc_of_le (Nat.cast_nonneg n)] at ht
      exact Real.norm_of_nonneg (hnn t ht.1)
  have hlim : ∫ t in Ioi 0, b t ≤ K :=
    le_of_tendsto' (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop)
      fun n ↦ integral_stoppedDuhamel_abs_le hc hT hf hC hfc (Nat.cast_nonneg n)
  calc ∫⁻ t in Ioi 0, ‖stoppedDuhamel c a₀ T J f t‖ₑ
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (b t) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht ↦ by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (abs_stoppedDuhamel_le hT.le (le_of_lt ht))
    _ = ENNReal.ofReal (∫ t in Ioi 0, b t) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
            fun t ht ↦ hnn t (le_of_lt ht)))).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hlim

/-! ### The triangular system -/

/-- **Part II (3.32), the diagonalization.** For `l₁ ≠ l₂` put `κ = μ / (l₁ - l₂)`. If `ã₁` and
`a₂` are primitives with jumps of `l₁ ã₁ - F̃₁` and `l₂ a₂ - F₂` (for instance `stoppedDuhamel`
with the diagonal rates), then `a₁ = ã₁ - κ a₂` is a primitive with jump `J̃₁ - κ J₂` of
`l₁ a₁ + μ a₂ - (F̃₁ - κ F₂)`: the pair `(a₁, a₂)` solves the triangular system
`a₁' = l₁ a₁ + μ a₂ - F₁`, `a₂' = l₂ a₂ - F₂` with `F₁ = F̃₁ - κ F₂`, initial value
`a₁(0) = ã₁(0) - κ a₂(0)` and jump `J₁ = J̃₁ - κ J₂`. In Part II, `l₁ - l₂ = -c̄_l / 2` and
`μ = 1`. -/
theorem hasDerivWithJump_triangular {l₁ l₂ μ T J₁ J₂ : ℝ} (hl : l₁ ≠ l₂) {b₁ a₂ F₁ F₂ : ℝ → ℝ}
    (h₁ : HasDerivWithJump b₁ (fun t ↦ l₁ * b₁ t - F₁ t) T J₁)
    (h₂ : HasDerivWithJump a₂ (fun t ↦ l₂ * a₂ t - F₂ t) T J₂) :
    HasDerivWithJump (fun t ↦ b₁ t - μ / (l₁ - l₂) * a₂ t)
      (fun t ↦ l₁ * (b₁ t - μ / (l₁ - l₂) * a₂ t) + μ * a₂ t -
        (F₁ t - μ / (l₁ - l₂) * F₂ t)) T (J₁ - μ / (l₁ - l₂) * J₂) := by
  have hsub : l₁ - l₂ ≠ 0 := sub_ne_zero.2 hl
  have h := hasDerivWithJump_sum_smul (Finset.univ : Finset (Fin 2)) ![1, -(μ / (l₁ - l₂))]
    (G := ![b₁, a₂]) (G' := ![fun t ↦ l₁ * b₁ t - F₁ t, fun t ↦ l₂ * a₂ t - F₂ t])
    (J := ![J₁, J₂]) (fun k _ ↦ by fin_cases k <;> assumption)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
    neg_mul, one_mul] at h
  have e₁ : (fun τ ↦ b₁ τ + -(μ / (l₁ - l₂) * a₂ τ)) = fun t ↦ b₁ t - μ / (l₁ - l₂) * a₂ t :=
    funext fun τ ↦ by ring
  have e₂ : (fun τ ↦ l₁ * b₁ τ - F₁ τ + -(μ / (l₁ - l₂) * (l₂ * a₂ τ - F₂ τ))) =
      fun t ↦ l₁ * (b₁ t - μ / (l₁ - l₂) * a₂ t) + μ * a₂ t - (F₁ t - μ / (l₁ - l₂) * F₂ t) :=
    funext fun τ ↦ by field_simp; ring
  rw [e₁, e₂, show J₁ + -(μ / (l₁ - l₂) * J₂) = J₁ - μ / (l₁ - l₂) * J₂ by ring] at h
  exact h

end PDE.Analysis.Evolution
