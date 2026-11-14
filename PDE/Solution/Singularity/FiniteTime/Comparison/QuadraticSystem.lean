/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Solution.Singularity.FiniteTime.Comparison.QuadraticGrowth
import CAS.ExactTactic

/-!
# Finite-time obstruction from a quadratic system of second order

Let `I` and `J` be continuous on `[t₀, T]` and differentiable on `(t₀, T)`, with `I' ≥ J` and
`J' ≥ c I²` there, where `c > 0`. If `I (t₀) > 0` and `J (t₀) ≥ 0`, then

`T < t₀ + √(8 √3 / (c I (t₀)))`,

so such a pair cannot live longer (`right_endpoint_lt_of_deriv_ge`). The theorem holds for all
real functions `I` and `J` with these properties. For `I' = J` the hypotheses say that
`I'' ≥ c I²`. The constant `√(8 √3)` is not optimal.

This is the scalar step in the proof of Theorem 2.1 of Choi, Hou, Kiselev, Luo, Šverák and Yao.
There `I` is the moment (4.7), `J` is the lower bound of `dI/dt` found before (4.8), and the two
inequalities are `dI/dt ≥ J` and `dJ/dt ≥ (2 / L²) I²`, which give (4.9). The paper infers the
blowup from (4.9) by a comparison with the equation `h'' = 2 c₀ h (h')^{1/2}`. The proof here is
a different one, by a reduction to the Riccati inequality of
`PDE.Solution.Singularity.FiniteTime.QuadraticGrowth`, and it gives the bound above for the time.

## How it works

The function `w (t) = I (t₀) + ∫_{t₀}^t J` has `w' = J` and `w ≤ I`. The bound is proved for
every `w` with these two properties (`right_endpoint_lt_of_hasDerivAt`), in three steps.

* `J` and `w` are nondecreasing, so `J' ≥ c w² ≥ c w (t₀)²`, `J (t) ≥ c w (t₀)² (t - t₀)` and
  `w (t) - w (t₀) ≥ c w (t₀)² (t - t₀)² / 2`.
* The energy `J² - (2 c / 3) w³` is nondecreasing (`monotoneOn_sq_sub_mul_cube`), so
  `J² ≥ (2 c / 3) (w - w (t₀))³`.
* Hence `y = √(w - w (t₀))` satisfies `y' ≥ √(c / 6) y²` where it is positive. Let
  `δ = √(2 √3 / (c w (t₀)))`, so that `2 δ = √(8 √3 / (c w (t₀)))`. If `T ≤ t₀ + δ` there is
  nothing to prove. Otherwise the Riccati lemma `QuadraticGrowth.right_endpoint_lt_riccati_horizon`
  on `[t₀ + δ, T]` gives `T < t₀ + δ + (√(c / 6) y (t₀ + δ))⁻¹`, and by the first step the last
  term is at most `2 √3 / (c w (t₀) δ) = δ`.

## Main results

* `monotoneOn_sq_sub_mul_cube`: the energy `J² - (2 c / 3) w³` is nondecreasing when
  `w' = J ≥ 0` and `J' ≥ c w²`.
* `right_endpoint_lt_of_hasDerivAt`: the bound `T < t₀ + √(8 √3 / (c w (t₀)))` when `w' = J`,
  `w ≤ I` and `J' ≥ c I²`.
* `right_endpoint_lt_of_deriv_ge`: the bound `T < t₀ + √(8 √3 / (c I (t₀)))` when `I' ≥ J` and
  `J' ≥ c I²`.

## References

* K. Choi, T. Y. Hou, A. Kiselev, G. Luo, V. Šverák, and Y. Yao, "On the finite-time blowup of a
  one-dimensional model for the three-dimensional axisymmetric Euler equations", *Comm. Pure
  Appl. Math.* 70 (2017), no. 11, 2218-2243; numbering of arXiv:1407.4776v2, proof of
  Theorem 2.1, (4.7)-(4.9). <https://doi.org/10.1002/cpa.21697> <https://arxiv.org/abs/1407.4776v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Real
open PDE.Solution.Singularity.FiniteTime.QuadraticGrowth (right_endpoint_lt_riccati_horizon)

namespace PDE.Solution.Singularity.FiniteTime.QuadraticSystem

/-- Let `w` and `J` be continuous on `[t₀, T]`, and on `(t₀, T)` let `w' = J ≥ 0` and
`J' ≥ c w²`, with `J` differentiable. Then the energy `J² - (2 c / 3) w³` is nondecreasing on
`[t₀, T]`. -/
theorem monotoneOn_sq_sub_mul_cube {w J : ℝ → ℝ} {c t₀ T : ℝ}
    (hw_cont : ContinuousOn w (Icc t₀ T)) (hJ_cont : ContinuousOn J (Icc t₀ T))
    (hw_deriv : ∀ t ∈ Ioo t₀ T, HasDerivAt w (J t) t)
    (hJ_diff : DifferentiableOn ℝ J (Ioo t₀ T)) (hJ_nonneg : ∀ t ∈ Ioo t₀ T, 0 ≤ J t)
    (hJ_deriv : ∀ t ∈ Ioo t₀ T, c * w t ^ 2 ≤ deriv J t) :
    MonotoneOn (fun t ↦ J t ^ 2 - 2 * c / 3 * w t ^ 3) (Icc t₀ T) := by
  have hE : ∀ t ∈ Ioo t₀ T, HasDerivAt (fun t ↦ J t ^ 2 - 2 * c / 3 * w t ^ 3)
      (2 * J t * (deriv J t - c * w t ^ 2)) t := fun t ht ↦ by
    have hJ := ((hJ_diff t ht).differentiableAt (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt
    cas using [hJ, hw_deriv t ht]
  refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) (by fun_prop) ?_ ?_
  · rw [interior_Icc]
    exact fun t ht ↦ (hE t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hE t ht).deriv]
    exact mul_nonneg (mul_nonneg zero_le_two (hJ_nonneg t ht)) (sub_nonneg.2 (hJ_deriv t ht))

/-- **Finite lifespan when a primitive of `J` lies below `I`.** Let `c > 0`, let `w` and `J` be
continuous on `[t₀, T]`, and on `(t₀, T)` let `w' = J`, `w ≤ I` and `J' ≥ c I²`, with `J`
differentiable. If `w (t₀) > 0` and `J (t₀) ≥ 0`, then `T < t₀ + √(8 √3 / (c w (t₀)))`.
For `I = w` the hypotheses say that `w'' ≥ c w²`. -/
theorem right_endpoint_lt_of_hasDerivAt {w I J : ℝ → ℝ} {c t₀ T : ℝ} (hc : 0 < c)
    (hw₀ : 0 < w t₀) (hJ₀ : 0 ≤ J t₀)
    (hw_cont : ContinuousOn w (Icc t₀ T)) (hJ_cont : ContinuousOn J (Icc t₀ T))
    (hw_deriv : ∀ t ∈ Ioo t₀ T, HasDerivAt w (J t) t)
    (hJ_diff : DifferentiableOn ℝ J (Ioo t₀ T)) (hwI : ∀ t ∈ Ioo t₀ T, w t ≤ I t)
    (hJ_deriv : ∀ t ∈ Ioo t₀ T, c * I t ^ 2 ≤ deriv J t) :
    T < t₀ + √(8 * √3 / (c * w t₀)) := by
  generalize hR : √(8 * √3 / (c * w t₀)) = R
  have hR0 : 0 < R := by
    rw [← hR]
    exact Real.sqrt_pos.2 (by positivity)
  have hR2 : c * w t₀ * R ^ 2 = 8 * √3 := by
    rw [← hR]
    cas using [hc, hw₀]
  rcases le_or_gt T (t₀ + R / 2) with hT | hT
  · cas
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.2 (by cas)
  -- `J ≥ 0` and `w ≥ w (t₀)`, hence `J' ≥ c w²`.
  have hJ_mono : MonotoneOn J (Icc t₀ T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) hJ_cont ?_ ?_
    · rwa [interior_Icc]
    · rw [interior_Icc]
      exact fun t ht ↦ (mul_nonneg hc.le (sq_nonneg _)).trans (hJ_deriv t ht)
  have hJ_nonneg : ∀ t ∈ Icc t₀ T, 0 ≤ J t := fun t ht ↦ hJ₀.trans (hJ_mono ht₀ ht ht.1)
  have hw_mono : MonotoneOn w (Icc t₀ T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) hw_cont ?_ ?_
    · rw [interior_Icc]
      exact fun t ht ↦ (hw_deriv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hw_deriv t ht).deriv]
      exact hJ_nonneg t (Ioo_subset_Icc_self ht)
  have hw_ge : ∀ t ∈ Icc t₀ T, w t₀ ≤ w t := fun t ht ↦ hw_mono ht₀ ht ht.1
  have hJ_deriv' : ∀ t ∈ Ioo t₀ T, c * w t ^ 2 ≤ deriv J t := fun t ht ↦
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (hw₀.le.trans (hw_ge t (Ioo_subset_Icc_self ht))) (hwI t ht) 2) hc.le).trans (hJ_deriv t ht)
  -- Growth: `J (t) ≥ c w (t₀)² (t - t₀)` and `w (t) ≥ w (t₀) + c w (t₀)² (t - t₀)² / 2`.
  have hJ_lin : ∀ t ∈ Icc t₀ T, c * w t₀ ^ 2 * (t - t₀) ≤ J t := by
    have hC : ∀ s ∈ interior (Icc t₀ T), c * w t₀ ^ 2 ≤ deriv J s := by
      rw [interior_Icc]
      exact fun s hs ↦ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw₀.le
        (hw_ge s (Ioo_subset_Icc_self hs)) 2) hc.le).trans (hJ_deriv' s hs)
    intro t ht
    have h := (convex_Icc t₀ T).mul_sub_le_image_sub_of_le_deriv hJ_cont
      (by rwa [interior_Icc]) hC t₀ ht₀ t ht ht.1
    cas
  have hw_quad : ∀ t ∈ Icc t₀ T, w t₀ + c * w t₀ ^ 2 * (t - t₀) ^ 2 / 2 ≤ w t := by
    have hq : ∀ t ∈ Ioo t₀ T, HasDerivAt (fun s ↦ w s - c * w t₀ ^ 2 * (s - t₀) ^ 2 / 2)
        (J t - c * w t₀ ^ 2 * (t - t₀)) t := fun t ht ↦ (hw_deriv t ht).fun_sub (by cas)
    have hmono : MonotoneOn (fun s ↦ w s - c * w t₀ ^ 2 * (s - t₀) ^ 2 / 2) (Icc t₀ T) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T) (by fun_prop) ?_ ?_
      · rw [interior_Icc]
        exact fun t ht ↦ (hq t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hq t ht).deriv]
        exact sub_nonneg.2 (hJ_lin t (Ioo_subset_Icc_self ht))
    intro t ht
    have h : w t₀ - c * w t₀ ^ 2 * (t₀ - t₀) ^ 2 / 2 ≤ w t - c * w t₀ ^ 2 * (t - t₀) ^ 2 / 2 :=
      hmono ht₀ ht ht.1
    cas
  -- Energy: `J² ≥ (2 c / 3) (w - w (t₀))³`.
  have hE : ∀ t ∈ Icc t₀ T, 2 * c / 3 * (w t - w t₀) ^ 3 ≤ J t ^ 2 := fun t ht ↦ by
    have h : J t₀ ^ 2 - 2 * c / 3 * w t₀ ^ 3 ≤ J t ^ 2 - 2 * c / 3 * w t ^ 3 :=
      monotoneOn_sq_sub_mul_cube hw_cont hJ_cont hw_deriv hJ_diff
        (fun s hs ↦ hJ_nonneg s (Ioo_subset_Icc_self hs)) hJ_deriv' ht₀ ht ht.1
    have h' : 0 ≤ c * (w t₀ * w t * (w t - w t₀)) :=
      mul_nonneg hc.le (mul_nonneg (mul_nonneg hw₀.le (hw₀.le.trans (hw_ge t ht)))
        (sub_nonneg.2 (hw_ge t ht)))
    cas using [h, h', sq_nonneg (J t₀)]
  -- On `[t₀ + R / 2, T]` the function `y = √(w - w (t₀))` is positive and `y' ≥ √(c / 6) y²`.
  have hz_pos : ∀ t ∈ Icc (t₀ + R / 2) T, 0 < w t - w t₀ := fun t ht ↦ by
    have ht' : t₀ < t := by cas using [ht.1]
    have h := hw_quad t ⟨ht'.le, ht.2⟩
    have h2 : 0 < c * w t₀ ^ 2 * (t - t₀) ^ 2 / 2 :=
      div_pos (mul_pos (mul_pos hc (pow_pos hw₀ 2)) (pow_pos (sub_pos.2 ht') 2)) two_pos
    cas
  have hy : ∀ t ∈ Ioo (t₀ + R / 2) T,
      HasDerivAt (fun s ↦ √(w s - w t₀)) (J t / (2 * √(w t - w t₀))) t := fun t ht ↦
    ((hw_deriv t ⟨by cas using [ht.1], ht.2⟩).sub_const (w t₀)).sqrt
      (hz_pos t (Ioo_subset_Icc_self ht)).ne'
  have hy_deriv : ∀ t ∈ Ioo (t₀ + R / 2) T,
      √(c / 6) * √(w t - w t₀) ^ 2 ≤ deriv (fun s ↦ √(w s - w t₀)) t := fun t ht ↦ by
    have ht' : t ∈ Icc t₀ T := ⟨by cas using [ht.1], ht.2.le⟩
    have hz := hz_pos t (Ioo_subset_Icc_self ht)
    rw [(hy t ht).deriv, Real.sq_sqrt hz.le, le_div_iff₀ (by positivity)]
    refine le_of_pow_le_pow_left₀ two_ne_zero (hJ_nonneg t ht') ?_
    calc (√(c / 6) * (w t - w t₀) * (2 * √(w t - w t₀))) ^ 2
      _ = 2 * c / 3 * (w t - w t₀) ^ 3 := by cas using [hc, hz]
      _ ≤ J t ^ 2 := hE t ht'
  have hT' : T < t₀ + R / 2 + (√(c / 6) * √(w (t₀ + R / 2) - w t₀))⁻¹ :=
    right_endpoint_lt_riccati_horizon (y := fun s ↦ √(w s - w t₀)) (a := √(c / 6))
      (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 (hz_pos _ (left_mem_Icc.2 hT.le)))
      ((hw_cont.mono (Icc_subset_Icc_left (by cas))).fun_sub continuousOn_const).sqrt
      (fun t ht ↦ (hy t ht).differentiableAt.differentiableWithinAt) hy_deriv
  -- The Riccati horizon of `y` comes at most `R / 2` after `t₀ + R / 2`.
  have hinv : (√(c / 6) * √(w (t₀ + R / 2) - w t₀))⁻¹ ≤ R / 2 := by
    have hz := hz_pos (t₀ + R / 2) (left_mem_Icc.2 hT.le)
    have hz' : c * w t₀ ^ 2 * (R / 2) ^ 2 / 2 ≤ w (t₀ + R / 2) - w t₀ := by
      cas using [hw_quad (t₀ + R / 2) ⟨by cas, hT.le⟩]
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    refine (one_le_sq_iff₀ (by positivity)).1 ?_
    calc (1 : ℝ)
      _ = (R / 2) ^ 2 * (c / 6 * (c * w t₀ ^ 2 * (R / 2) ^ 2 / 2)) := by cas using [hR2]
      _ ≤ (R / 2) ^ 2 * (c / 6 * (w (t₀ + R / 2) - w t₀)) := by gcongr
      _ = (R / 2 * (√(c / 6) * √(w (t₀ + R / 2) - w t₀))) ^ 2 := by cas using [hc, hz]
  cas

/-- **Comparison lemma for `I' ≥ J`, `J' ≥ c I²`.** Let `c > 0`, and let `I` and `J` be
continuous on `[t₀, T]` and differentiable on `(t₀, T)`, with `I' ≥ J` and `J' ≥ c I²` there. If
`I (t₀) > 0` and `J (t₀) ≥ 0`, then `T < t₀ + √(8 √3 / (c I (t₀)))`. This is the system
`dI/dt ≥ J`, `dJ/dt ≥ (2 / L²) I²` in the proof of Theorem 2.1 of Choi, Hou, Kiselev, Luo,
Šverák and Yao, between (4.7) and (4.9). -/
theorem right_endpoint_lt_of_deriv_ge {I J : ℝ → ℝ} {c t₀ T : ℝ} (hc : 0 < c)
    (hI₀ : 0 < I t₀) (hJ₀ : 0 ≤ J t₀)
    (hI_cont : ContinuousOn I (Icc t₀ T)) (hJ_cont : ContinuousOn J (Icc t₀ T))
    (hI_diff : DifferentiableOn ℝ I (Ioo t₀ T)) (hJ_diff : DifferentiableOn ℝ J (Ioo t₀ T))
    (hI_deriv : ∀ t ∈ Ioo t₀ T, J t ≤ deriv I t)
    (hJ_deriv : ∀ t ∈ Ioo t₀ T, c * I t ^ 2 ≤ deriv J t) :
    T < t₀ + √(8 * √3 / (c * I t₀)) := by
  rcases le_or_gt T t₀ with hT | hT
  · exact hT.trans_lt (lt_add_of_pos_right t₀ (Real.sqrt_pos.2 (by positivity)))
  -- The primitive `w (t) = I (t₀) + ∫_{t₀}^t J` of `J` lies below `I`.
  have hw₀ : 0 < I t₀ + ∫ s in t₀..t₀, J s := by
    rwa [intervalIntegral.integral_same, add_zero]
  have hw_cont : ContinuousOn (fun t ↦ I t₀ + ∫ s in t₀..t, J s) (Icc t₀ T) := by
    have hint : IntegrableOn J (uIcc t₀ T) := by
      rw [uIcc_of_le hT.le]
      exact hJ_cont.integrableOn_Icc
    have h := intervalIntegral.continuousOn_primitive_interval hint
    rw [uIcc_of_le hT.le] at h
    exact h.const_add (I t₀)
  have hw_deriv : ∀ t ∈ Ioo t₀ T, HasDerivAt (fun t ↦ I t₀ + ∫ s in t₀..t, J s) (J t) t :=
    fun t ht ↦ (intervalIntegral.integral_hasDerivAt_right
      ((hJ_cont.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hJ_cont.mono Ioo_subset_Icc_self) t ht)
      (hJ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2))).const_add (I t₀)
  have hwI : ∀ t ∈ Ioo t₀ T, I t₀ + ∫ s in t₀..t, J s ≤ I t := fun t ht ↦ by
    have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht.1.le
      (hI_cont.mono (Icc_subset_Icc_right ht.2.le))
      (fun s hs ↦ ((hI_diff s ⟨hs.1, hs.2.trans ht.2⟩).differentiableAt
        (Ioo_mem_nhds hs.1 (hs.2.trans ht.2))).hasDerivAt.hasDerivWithinAt)
      (hJ_cont.mono (Icc_subset_Icc_right ht.2.le)).integrableOn_Icc
      fun s hs ↦ hI_deriv s ⟨hs.1, hs.2.trans ht.2⟩
    cas
  have h : T < t₀ + √(8 * √3 / (c * (I t₀ + ∫ s in t₀..t₀, J s))) :=
    right_endpoint_lt_of_hasDerivAt (w := fun t ↦ I t₀ + ∫ s in t₀..t, J s) hc hw₀ hJ₀ hw_cont
      hJ_cont hw_deriv hJ_diff hwI hJ_deriv
  rwa [intervalIntegral.integral_same, add_zero] at h

end PDE.Solution.Singularity.FiniteTime.QuadraticSystem
