/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.FiniteRankResponse
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Response integrals of discontinuous kernels

The response integral `∫₀ᵗ G(t - s) (a s) ds` of `PDE.Analysis.Evolution.responseIntegral`
for kernels that are only integrable in time, such as approximate solutions computed up to a
stopping time and then switched off.

A kernel with one jump is described by `HasDerivWithJump G G' T J`, the weak form of
`∂_τ G = G' + J δ_T`. It is closed under finite linear combinations
(`hasDerivWithJump_sum_smul`, `HasDerivWithJump.add`, `HasDerivWithJump.smul_const`) and under
replacement of `G'` by a function agreeing with it at positive times outside a countable set
(`HasDerivWithJump.congr_of_countable`). The response formula comes from Fubini's theorem on the
triangle `0 ≤ s ≤ u ≤ t` (`responseIntegral_primitive`), so the kernel need not be
differentiable anywhere.

## Main definitions

* `HasDerivWithJump`: `G(τ) = G(0) + ∫₀^τ G' + 1_{T ≤ τ} J` on `[0, ∞)`, with `G'` integrable on
  bounded intervals.

## Main results

* `continuousOn_responseIntegral_Icc`: an integrable kernel and continuous coefficients give a
  continuous response on `[0, T]`; `continuousOn_responseIntegral_Ici` is the case `[0, ∞)`.
* `norm_responseIntegral_le`: a kernel bounded by `M` and coefficients bounded by `D` give a
  response bounded by `M D t`.
* `enorm_responseIntegral_le`: a bound `‖a‖ ≤ C` on `[0, t]` bounds the response by `C` times the
  time integral of the kernel.
* `responseIntegral_eq_add_of_hasDerivWithJump`: the response is the sum of the primitives of
  `G(0) a`, of the response of `G'`, and of the jump term.
* `hasDerivWithinAt_responseIntegral_of_hasDerivWithJump`: at every `t ≥ 0`, the jump time
  included, the response has the right derivative
  `G(0) a(t) + ∫₀ᵗ G'(t - s) a(s) ds + 1_{T ≤ t} J a(t - T)`, with the right-continuous indicator.
* `hasDerivAt_responseIntegral_of_hasDerivWithJump`: away from `t = T` this is the two-sided
  derivative.
* `hasDerivAt_integral_smul_of_hasDerivWithJump`: the same derivative for the scalar Duhamel
  integral `∫₀ᵗ a(s) κ(t - s) ds`; `hasDerivWithinAt_integral_smul_of_hasDerivWithJump` is the
  right derivative.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 4.2.4, (4.19)-(4.21),
  Section 4.2.5, and Section 5.7, (5.84)-(5.89). <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 3.5,
  (3.35)-(3.36). <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal

namespace PDE.Analysis.Evolution

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The response integral in the age variable `u = t - s`. -/
theorem responseIntegral_eq_integral_sub (G : ℝ → F →L[ℝ] E) (a : ℝ → F) (t : ℝ) :
    responseIntegral G a t = ∫ u in 0..t, G u (a (t - u)) := by
  have h := intervalIntegral.integral_comp_sub_left (fun u ↦ G u (a (t - u))) (a := 0) (b := t) t
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  exact h

/-- An integrable kernel and continuous coefficients on `[0, T]` give a continuous response on
`[0, T]`. The kernel may jump in time. -/
theorem continuousOn_responseIntegral_Icc {G : ℝ → F →L[ℝ] E} {a : ℝ → F} {T : ℝ}
    (hG : IntegrableOn G (Icc 0 T)) (ha : ContinuousOn a (Icc 0 T)) :
    ContinuousOn (responseIntegral G a) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Icc_eq_empty_of_lt hT]
  set b : ℝ → F := fun τ ↦ a (max 0 (min τ T)) with hb_def
  have hb : Continuous b :=
    ha.comp_continuous (by fun_prop) fun τ ↦ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hbC : ∀ τ, ‖b τ‖ ≤ C := fun τ ↦
    hC _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  set H : ℝ → E := fun t ↦ ∫ u in 0..T, (Iic t).indicator (fun u ↦ G u (b (t - u))) u
  have hHeq : ∀ t ∈ Icc 0 T, responseIntegral G a t = H t := by
    intro t ht
    rw [responseIntegral_eq_integral_sub, intervalIntegral.integral_of_le ht.1]
    simp only [H]
    rw [intervalIntegral.integral_of_le hT, integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le ht.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
    have h1 : min (t - u) T = t - u := min_eq_left ((sub_le_self t hu.1.le).trans ht.2)
    simp only [hb_def, h1, max_eq_right (sub_nonneg.mpr hu.2)]
  have hGm : AEStronglyMeasurable G (volume.restrict (Ι 0 T)) := by
    rw [uIoc_of_le hT]
    exact hG.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  intro t₀ ht₀
  have hHcont : ContinuousWithinAt H (Icc 0 T) t₀ := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun u ↦ ‖G u‖ * C)
    · refine Filter.Eventually.of_forall fun t ↦ ?_
      exact ((ContinuousLinearMap.id ℝ (F →L[ℝ] E)).aestronglyMeasurable_comp₂ hGm
        (hb.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).indicator
          measurableSet_Iic
    · exact .of_forall fun t ↦ .of_forall fun u _ ↦ (norm_indicator_le_norm_self _ _).trans
        ((G u).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left (hbC _) (norm_nonneg _)))
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hG).norm.mul_const C
    · filter_upwards [Measure.ae_ne volume t₀] with u hu _
      rcases hu.lt_or_gt with hlt | hgt
      · have hev : (fun t ↦ (Iic t).indicator (fun u ↦ G u (b (t - u))) u) =ᶠ[𝓝 t₀]
            fun t ↦ G u (b (t - u)) := by
          filter_upwards [Ioi_mem_nhds hlt] with t ht
          exact indicator_of_mem (mem_Iic.2 ht.le) _
        exact ((G u).continuous.comp (hb.comp (continuous_id.sub continuous_const))
          |>.continuousAt.congr hev.symm).continuousWithinAt
      · have hev : (fun t ↦ (Iic t).indicator (fun u ↦ G u (b (t - u))) u) =ᶠ[𝓝 t₀]
            fun _ ↦ 0 := by
          filter_upwards [Iio_mem_nhds hgt] with t ht
          exact indicator_of_notMem (notMem_Iic.2 (mem_Iio.1 ht)) _
        exact (continuousAt_const.congr hev.symm).continuousWithinAt
  exact hHcont.congr (fun t ht ↦ hHeq t ht) (hHeq t₀ ht₀)

/-- A function continuous on every `[0, T]` is continuous on `[0, ∞)`. -/
theorem continuousOn_Ici_of_forall_Icc {X : Type*} [TopologicalSpace X] {g : ℝ → X}
    (h : ∀ T, ContinuousOn g (Icc 0 T)) : ContinuousOn g (Ici 0) := by
  intro t₀ ht₀
  have hT : Icc 0 (t₀ + 1) ∈ 𝓝[Ici 0] t₀ := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (lt_add_one t₀))
  exact (h (t₀ + 1) t₀ ⟨ht₀, by linarith [mem_Ici.1 ht₀]⟩).mono_of_mem_nhdsWithin hT

/-- An integrable kernel and continuous coefficients on `[0, ∞)` give a continuous response on
`[0, ∞)`. The kernel may jump in time. -/
theorem continuousOn_responseIntegral_Ici {G : ℝ → F →L[ℝ] E} {a : ℝ → F}
    (hG : ∀ T, IntegrableOn G (Icc 0 T)) (ha : ContinuousOn a (Ici 0)) :
    ContinuousOn (responseIntegral G a) (Ici 0) :=
  continuousOn_Ici_of_forall_Icc fun T ↦
    continuousOn_responseIntegral_Icc (hG T) (ha.mono Icc_subset_Ici_self)

/-- The integrand of a response integral with a bounded measurable kernel and continuous
coefficients is integrable. -/
theorem intervalIntegrable_response {G : ℝ → F →L[ℝ] E} {a : ℝ → F} {t M : ℝ} (ht : 0 ≤ t)
    (hG : AEStronglyMeasurable G (volume.restrict (Icc 0 t)))
    (hGM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) (ha : ContinuousOn a (Icc 0 t)) :
    IntervalIntegrable (fun s ↦ G (t - s) (a s)) volume 0 t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hsub : IntervalIntegrable (fun u ↦ G u (a (t - u))) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
    refine Integrable.of_bound ((ContinuousLinearMap.id ℝ (F →L[ℝ] E)).aestronglyMeasurable_comp₂
      hG ((ha.comp (continuous_const.sub continuous_id).continuousOn fun u hu ↦
        ⟨sub_nonneg.2 hu.2, sub_le_self t hu.1⟩).aestronglyMeasurable measurableSet_Icc))
      (M * C) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hut : t - u ∈ Icc 0 t := ⟨sub_nonneg.2 hu.2, sub_le_self t hu.1⟩
    exact ((G u).le_opNorm _).trans (mul_le_mul (hGM u hu) (hC _ hut) (norm_nonneg _)
      ((norm_nonneg _).trans (hGM u hu)))
  simpa [sub_sub_cancel] using (hsub.comp_sub_left t).symm

/-- A bounded kernel bounds the response integral of bounded coefficients by `M D t`. -/
theorem norm_responseIntegral_le {G : ℝ → F →L[ℝ] E} {a : ℝ → F} {t M D : ℝ} (ht : 0 ≤ t)
    (hGM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) (ha : ∀ s ∈ Icc 0 t, ‖a s‖ ≤ D) :
    ‖responseIntegral G a t‖ ≤ M * D * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s ↦ G (t - s) (a s)) (C := M * D) fun s hs ↦ by
      rw [uIoc_of_le ht] at hs
      have hts : t - s ∈ Icc 0 t := ⟨sub_nonneg.2 hs.2, sub_le_self t hs.1.le⟩
      exact ((G (t - s)).le_opNorm _).trans (mul_le_mul (hGM _ hts) (ha s (Ioc_subset_Icc_self hs))
        (norm_nonneg _) ((norm_nonneg _).trans (hGM _ hts)))
  simpa [responseIntegral, abs_of_nonneg ht] using h

/-- For a measurable kernel bounded on `[0, t]` and coefficients continuous on `[0, t]`, the
response of `a - b` is the difference of the responses of `a` and `b`. -/
theorem responseIntegral_sub {G : ℝ → F →L[ℝ] E} {a b : ℝ → F} {t M : ℝ} (ht : 0 ≤ t)
    (hG : AEStronglyMeasurable G (volume.restrict (Icc 0 t)))
    (hGM : ∀ s ∈ Icc 0 t, ‖G s‖ ≤ M) (ha : ContinuousOn a (Icc 0 t))
    (hb : ContinuousOn b (Icc 0 t)) :
    responseIntegral G a t - responseIntegral G b t = responseIntegral G (a - b) t := by
  rw [responseIntegral, responseIntegral, responseIntegral,
    ← intervalIntegral.integral_sub (intervalIntegrable_response ht hG hGM ha)
      (intervalIntegrable_response ht hG hGM hb)]
  simp only [Pi.sub_apply, map_sub]

/-- A bound `‖a‖ ≤ C` on `[0, t]` bounds the response by `C` times the time integral of the
kernel over `(0, ∞)`, Part I (5.89). -/
theorem enorm_responseIntegral_le (G : ℝ → F →L[ℝ] E) {a : ℝ → F} {t C : ℝ} (ht : 0 ≤ t)
    (ha : ∀ s ∈ Icc 0 t, ‖a s‖ ≤ C) :
    ‖responseIntegral G a t‖ₑ ≤ ENNReal.ofReal C * ∫⁻ τ in Ioi 0, ‖G τ‖ₑ := by
  rw [responseIntegral_eq_integral_sub, intervalIntegral.integral_of_le ht]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ u in Ioc 0 t, ‖G u (a (t - u))‖ₑ
      ≤ ∫⁻ u in Ioc 0 t, ENNReal.ofReal C * ‖G u‖ₑ := by
        refine setLIntegral_mono' measurableSet_Ioc fun u hu ↦ ?_
        have hut : t - u ∈ Icc 0 t := ⟨sub_nonneg.2 hu.2, sub_le_self t hu.1.le⟩
        refine ((G u).le_opENorm _).trans ?_
        rw [mul_comm]
        gcongr
        exact (ofReal_norm (a (t - u))).symm.le.trans (ENNReal.ofReal_le_ofReal (ha _ hut))
    _ ≤ ENNReal.ofReal C * ∫⁻ τ in Ioi 0, ‖G τ‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact fun u (hu : u ∈ Ioc 0 t) ↦ hu.1

/-- Fubini on the triangle `0 ≤ s ≤ u ≤ τ`: the response of the primitive of `G'` is the
primitive of the response of `G'`. -/
theorem responseIntegral_primitive {G' : ℝ → F →L[ℝ] E} {a : ℝ → F} {τ : ℝ} (hτ : 0 ≤ τ)
    (hG' : IntegrableOn G' (Icc 0 τ)) (ha : IntegrableOn a (Icc 0 τ)) :
    responseIntegral (fun ρ ↦ ∫ r in 0..ρ, G' r) a τ = ∫ u in 0..τ, responseIntegral G' a u := by
  set f : ℝ → F := (Icc 0 τ).indicator a with hf_def
  set g : ℝ → F →L[ℝ] E := (Icc 0 τ).indicator G' with hg_def
  have hf : Integrable f := (integrable_indicator_iff measurableSet_Icc).2 ha
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Icc).2 hG'
  set φ : ℝ × ℝ → E := {p : ℝ × ℝ | p.1 ≤ τ}.indicator
    (fun p ↦ (ContinuousLinearMap.id ℝ (F →L[ℝ] E)).flip (f p.2) (g (p.1 - p.2))) with hφ_def
  have hφ : Integrable φ (volume.prod volume) :=
    (hf.convolution_integrand _ hg).indicator
      (measurableSet_le measurable_fst measurable_const)
  have hφ_apply : ∀ u s, φ (u, s) =
      if 0 ≤ s ∧ s ≤ u ∧ u ≤ τ then G' (u - s) (a s) else 0 := by
    intro u s
    by_cases hc : 0 ≤ s ∧ s ≤ u ∧ u ≤ τ
    · have h1 : (u, s) ∈ {p : ℝ × ℝ | p.1 ≤ τ} := hc.2.2
      have h2 : s ∈ Icc 0 τ := ⟨hc.1, hc.2.1.trans hc.2.2⟩
      have h3 : u - s ∈ Icc 0 τ := ⟨sub_nonneg.2 hc.2.1, by linarith [hc.1, hc.2.2]⟩
      rw [ite_eq_left hc, hφ_def, indicator_of_mem h1]
      simp only [hf_def, hg_def, indicator_of_mem h2, indicator_of_mem h3,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply]
    · rw [ite_eq_right hc, hφ_def]
      by_cases h1 : (u, s) ∈ {p : ℝ × ℝ | p.1 ≤ τ}
      · rw [indicator_of_mem h1, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply]
        by_cases h2 : s ∈ Icc 0 τ
        · have h3 : u - s ∉ Icc 0 τ := fun h3 ↦ hc ⟨h2.1, sub_nonneg.1 h3.1, h1⟩
          simp [hg_def, indicator_of_notMem h3]
        · simp only [hf_def, indicator_of_notMem h2, map_zero]
      · exact indicator_of_notMem h1 _
  have hinner_s : ∀ u, ∫ s, φ (u, s) = (Icc 0 τ).indicator (responseIntegral G' a) u := by
    intro u
    simp_rw [hφ_apply u]
    by_cases hu : u ∈ Icc 0 τ
    · rw [indicator_of_mem hu, responseIntegral, intervalIntegral.integral_of_le hu.1,
        ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
      simp only [hu.2, and_true, indicator_apply, mem_Icc]
    · rw [indicator_of_notMem hu]
      exact integral_eq_zero_of_ae (ae_of_all _ fun s ↦ ite_eq_right fun h ↦
        hu ⟨h.1.trans h.2.1, h.2.2⟩)
  have hinner_u : ∀ s, ∫ u, φ (u, s) =
      (Icc 0 τ).indicator (fun s ↦ ∫ u in s..τ, G' (u - s) (a s)) s := by
    intro s
    simp_rw [hφ_apply _ s]
    by_cases hs : s ∈ Icc 0 τ
    · rw [indicator_of_mem hs, intervalIntegral.integral_of_le hs.2,
        ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
      simp only [hs.1, true_and, indicator_apply, mem_Icc]
    · rw [indicator_of_notMem hs]
      exact integral_eq_zero_of_ae (ae_of_all _ fun u ↦ ite_eq_right fun h ↦
        hs ⟨h.1, h.2.1.trans h.2.2⟩)
  have hswap := integral_integral_swap (f := fun u s ↦ φ (u, s)) hφ
  calc responseIntegral (fun ρ ↦ ∫ r in 0..ρ, G' r) a τ
      = ∫ s in 0..τ, ∫ u in s..τ, G' (u - s) (a s) := by
        refine intervalIntegral.integral_congr fun s hs ↦ ?_
        rw [uIcc_of_le hτ] at hs
        have hint : IntervalIntegrable G' volume 0 (τ - s) := by
          refine IntegrableOn.intervalIntegrable ?_
          rw [uIcc_of_le (sub_nonneg.2 hs.2)]
          exact hG'.mono_set (Icc_subset_Icc_right (sub_le_self τ hs.1))
        simp only
        rw [ContinuousLinearMap.intervalIntegral_apply hint,
          intervalIntegral.integral_comp_sub_right (fun r ↦ G' r (a s)), sub_self]
    _ = ∫ s, ∫ u, φ (u, s) := by
        simp_rw [hinner_u]
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hτ]
    _ = ∫ u, ∫ s, φ (u, s) := hswap.symm
    _ = ∫ u in 0..τ, responseIntegral G' a u := by
        simp_rw [hinner_s]
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hτ]

/-- The kernel `τ ↦ toSpanSingleton ℝ (κ τ)`, through which a scalar coefficient `a` acts on a
field `κ`, has the response `∫₀ᵗ a(s) κ(t - s) ds`. -/
theorem responseIntegral_toSpanSingleton (κ : ℝ → E) (a : ℝ → ℝ) (t : ℝ) :
    responseIntegral (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ)) a t =
      ∫ s in 0..t, a s • κ (t - s) := by
  simp [responseIntegral]

/-- If `κ` is integrable on `s`, so is the kernel `τ ↦ toSpanSingleton ℝ (κ τ)`. -/
theorem integrableOn_toSpanSingleton {κ : ℝ → E} {s : Set ℝ} (h : IntegrableOn κ s) :
    IntegrableOn (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ)) s :=
  (ContinuousLinearMap.smulRightL ℝ ℝ E 1).integrable_comp h

/-- If `κ` is a.e. strongly measurable, so is the kernel `τ ↦ toSpanSingleton ℝ (κ τ)`. -/
theorem aestronglyMeasurable_toSpanSingleton {κ : ℝ → E} {μ : Measure ℝ}
    (h : AEStronglyMeasurable κ μ) :
    AEStronglyMeasurable (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ)) μ :=
  (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous.comp_aestronglyMeasurable h

/-- `G` is the primitive of `G'` on `[0, ∞)` up to one jump `J` at the time `T`:
`G(τ) = G(0) + ∫₀^τ G' + 1_{T ≤ τ} J` for `τ ≥ 0`, with `G'` integrable on bounded intervals.
This is the weak form of `∂_τ G = G' + J δ_T`; it allows kernels that are only Lipschitz in time,
such as piecewise polynomial interpolants. -/
structure HasDerivWithJump (G G' : ℝ → E) (T : ℝ) (J : E) : Prop where
  /-- The derivative is integrable on every `[0, τ]`. -/
  integrableOn : ∀ τ, IntegrableOn G' (Icc 0 τ)
  /-- The integrated form on `[0, ∞)`. -/
  eq_add : ∀ τ, 0 ≤ τ → G τ = G 0 + (∫ r in 0..τ, G' r) + if T ≤ τ then J else 0

/-- Finite linear combinations of primitives with jumps at the same time are primitives with the
combined jump. -/
theorem hasDerivWithJump_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {G G' : ι → ℝ → E}
    {T : ℝ} {J : ι → E} (h : ∀ k ∈ s, HasDerivWithJump (G k) (G' k) T (J k)) :
    HasDerivWithJump (fun τ ↦ ∑ k ∈ s, c k • G k τ) (fun τ ↦ ∑ k ∈ s, c k • G' k τ) T
      (∑ k ∈ s, c k • J k) where
  integrableOn τ := integrable_finsetSum _ fun k hk ↦ ((h k hk).integrableOn τ).smul (c k)
  eq_add τ hτ := by
    have hint : ∀ k ∈ s, IntervalIntegrable (fun r ↦ c k • G' k r) volume 0 τ := fun k hk ↦
      (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2 (((h k hk).integrableOn τ).smul (c k))
    rw [intervalIntegral.integral_finsetSum hint]
    simp_rw [intervalIntegral.integral_smul]
    have hG : ∀ k ∈ s, c k • G k τ =
        c k • ((G k 0 + ∫ r in 0..τ, G' k r) + if T ≤ τ then J k else 0) := fun k hk ↦ by
      rw [(h k hk).eq_add τ hτ]
    rw [Finset.sum_congr rfl hG]
    split_ifs <;> simp [smul_add, Finset.sum_add_distrib]

/-- Sums of primitives with jumps at the same time. -/
theorem HasDerivWithJump.add {G₁ G₁' G₂ G₂' : ℝ → E} {T : ℝ} {J₁ J₂ : E}
    (h₁ : HasDerivWithJump G₁ G₁' T J₁) (h₂ : HasDerivWithJump G₂ G₂' T J₂) :
    HasDerivWithJump (fun t ↦ G₁ t + G₂ t) (fun t ↦ G₁' t + G₂' t) T (J₁ + J₂) where
  integrableOn τ := (h₁.integrableOn τ).add (h₂.integrableOn τ)
  eq_add τ hτ := by
    have hi : ∀ {G' : ℝ → E}, (∀ τ, IntegrableOn G' (Icc 0 τ)) →
        IntervalIntegrable G' volume 0 τ := fun h ↦
      (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2 (h τ)
    rw [h₁.eq_add τ hτ, h₂.eq_add τ hτ, intervalIntegral.integral_add (hi h₁.integrableOn)
      (hi h₂.integrableOn)]
    split_ifs <;> abel

variable [CompleteSpace E] in
/-- A scalar primitive with a jump times a fixed vector. -/
theorem HasDerivWithJump.smul_const {a a' : ℝ → ℝ} {T J : ℝ} (h : HasDerivWithJump a a' T J)
    (v : E) : HasDerivWithJump (fun t ↦ a t • v) (fun t ↦ a' t • v) T (J • v) where
  integrableOn τ := (h.integrableOn τ).smul_const v
  eq_add τ hτ := by
    rw [h.eq_add τ hτ, intervalIntegral.integral_smul_const]
    split_ifs <;> simp [add_smul]

/-- Two functions that agree at positive times off a countable set are both derivatives in the
integrated form. -/
theorem HasDerivWithJump.congr_of_countable {G G₁ G₂ : ℝ → E} {T : ℝ} {J : E}
    (h : HasDerivWithJump G G₁ T J) {C : Set ℝ} (hC : C.Countable)
    (heq : ∀ t, 0 < t → t ∉ C → G₁ t = G₂ t) :
    HasDerivWithJump G G₂ T J := by
  have hae : ∀ τ, G₁ =ᵐ[volume.restrict (Icc 0 τ)] G₂ := fun τ ↦ by
    have hnull : volume (C ∪ {0}) = 0 := (hC.union (countable_singleton 0)).measure_zero _
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with t ht hτ
    simp only [mem_union, mem_singleton_iff, not_or] at ht
    exact heq t (lt_of_le_of_ne hτ.1 (Ne.symm ht.2)) ht.1
  refine ⟨fun τ ↦ (h.integrableOn τ).congr_fun_ae (hae τ), fun τ hτ ↦ ?_⟩
  rw [h.eq_add τ hτ]
  congr 2
  refine intervalIntegral.integral_congr_ae ?_
  have := hae τ
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at this
  filter_upwards [this] with t ht htm
  rw [Set.uIoc_of_le hτ] at htm
  exact ht ⟨htm.1.le, htm.2⟩

/-- **The response of a kernel with a jump in primitive form.** If
`G = G(0) + ∫ G' + 1_{T ≤ ·} J` on `[0, ∞)` with `T ≥ 0` and the coefficients are continuous on
`[0, τ]`, then
`∫₀^τ G(τ - s) a(s) ds = ∫₀^τ G(0) a(s) ds + ∫₀^τ (∫₀ᵘ G'(u - s) a(s) ds) du
+ 1_{T ≤ τ} ∫₀^{τ - T} J a(s) ds`, by Fubini's theorem on the triangle `0 ≤ s ≤ u ≤ τ`
(`responseIntegral_primitive`). -/
theorem responseIntegral_eq_add_of_hasDerivWithJump {G G' : ℝ → F →L[ℝ] E} {T : ℝ}
    {J : F →L[ℝ] E} {a : ℝ → F} (hG : HasDerivWithJump G G' T J) (hT : 0 ≤ T) {τ : ℝ}
    (hτ : 0 ≤ τ) (ha : ContinuousOn a (Icc 0 τ)) :
    responseIntegral G a τ =
      (∫ s in 0..τ, G 0 (a s)) + (∫ u in 0..τ, responseIntegral G' a u) +
        if T ≤ τ then ∫ s in 0..(τ - T), J (a s) else 0 := by
  have hI0 : IntervalIntegrable (fun s ↦ G 0 (a s)) volume 0 τ :=
    ((G 0).continuous.comp_continuousOn ha).intervalIntegrable_of_Icc hτ
  have hcΦ : ContinuousOn (fun ρ ↦ ∫ r in 0..ρ, G' r) (Icc 0 τ) := by
    have := intervalIntegral.continuousOn_primitive_interval'
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2 (hG.integrableOn τ))
      (left_mem_uIcc (b := τ))
    simpa [uIcc_of_le hτ] using this
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcΦ
  have hΦ : IntervalIntegrable (fun s ↦ (∫ r in 0..(τ - s), G' r) (a s)) volume 0 τ :=
    intervalIntegrable_response hτ (hcΦ.aestronglyMeasurable measurableSet_Icc) hM ha
  have hind : (fun s ↦ if T ≤ τ - s then J (a s) else 0) =
      (Iic (τ - T)).indicator (fun s ↦ J (a s)) := by
    funext s
    simp only [indicator_apply, mem_Iic]
    exact if_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ rfl rfl
  have hJ : IntervalIntegrable (fun s ↦ if T ≤ τ - s then J (a s) else 0) volume 0 τ := by
    rw [hind, intervalIntegrable_iff_integrableOn_Icc_of_le hτ]
    exact ((J.continuous.comp_continuousOn ha).integrableOn_compact isCompact_Icc).indicator
      measurableSet_Iic
  calc responseIntegral G a τ
      = ∫ s in 0..τ, (G 0 (a s) + (∫ r in 0..(τ - s), G' r) (a s) +
          if T ≤ τ - s then J (a s) else 0) := by
        refine intervalIntegral.integral_congr fun s hs ↦ ?_
        rw [uIcc_of_le hτ] at hs
        show G (τ - s) (a s) = _
        rw [hG.eq_add (τ - s) (sub_nonneg.2 hs.2)]
        split_ifs <;>
          simp only [add_apply, add_zero]
    _ = (∫ s in 0..τ, G 0 (a s)) + (∫ s in 0..τ, (∫ r in 0..(τ - s), G' r) (a s)) +
          ∫ s in 0..τ, if T ≤ τ - s then J (a s) else 0 := by
        rw [intervalIntegral.integral_add (hI0.add hΦ) hJ, intervalIntegral.integral_add hI0 hΦ]
    _ = _ := by
        congr 1
        · congr 1
          exact responseIntegral_primitive hτ (hG.integrableOn τ)
            (ha.integrableOn_compact isCompact_Icc)
        · rw [hind, intervalIntegral.integral_of_le hτ, integral_indicator measurableSet_Iic,
            Measure.restrict_restrict measurableSet_Iic]
          by_cases hTτ : T ≤ τ
          · rw [Iic_inter_Ioc_of_le (by linarith)]
            simp only [ite_eq_left hTτ]
            rw [intervalIntegral.integral_of_le (by linarith)]
          · have : Iic (τ - T) ∩ Ioc 0 τ = ∅ := by
              ext s
              simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
              intro h
              linarith [h.1, h.2.1, not_le.1 hTτ]
            rw [this, Measure.restrict_empty, integral_zero_measure]
            simp only [ite_eq_right hTτ]

variable [CompleteSpace E] in
/-- **The time derivative of a response with a jump.** If `G = G(0) + ∫ G' + 1_{T ≤ ·} J` on
`[0, ∞)` and the coefficients are continuous, then at every `t > 0` other than `T` the response
`∫₀ᵗ G(t - s) a(s) ds` has the derivative
`G(0) a(t) + ∫₀ᵗ G'(t - s) a(s) ds + 1_{T ≤ t} J a(t - T)`. The indicator is the right-continuous
one of `hasDerivWithinAt_responseIntegral_of_hasDerivWithJump`; away from `T` it equals
`1_{T < t}`. -/
theorem hasDerivAt_responseIntegral_of_hasDerivWithJump {G G' : ℝ → F →L[ℝ] E} {T : ℝ}
    {J : F →L[ℝ] E} {a : ℝ → F} (hG : HasDerivWithJump G G' T J) (hT : 0 < T)
    (ha : ContinuousOn a (Ici 0)) {t : ℝ} (ht : 0 < t) (htT : t ≠ T) :
    HasDerivAt (responseIntegral G a)
      (G 0 (a t) + responseIntegral G' a t + if T ≤ t then J (a (t - T)) else 0) t := by
  have hcontAt : ∀ x, 0 < x → ContinuousAt a x := fun x hx ↦
    ha.continuousAt (Ici_mem_nhds hx)
  have hd₁ : HasDerivAt (fun τ ↦ ∫ s in 0..τ, G 0 (a s)) (G 0 (a t)) t :=
    intervalIntegral.integral_hasDerivAt_right
      (((G 0).continuous.comp_continuousOn (ha.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc
        ht.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        ((G 0).continuous.comp_continuousOn (ha.mono Ioi_subset_Ici_self)) t ht)
      ((G 0).continuous.continuousAt.comp (hcontAt t ht))
  have hcR : ContinuousOn (responseIntegral G' a) (Ici 0) :=
    continuousOn_responseIntegral_Ici hG.integrableOn ha
  have hd₂ : HasDerivAt (fun τ ↦ ∫ u in 0..τ, responseIntegral G' a u)
      (responseIntegral G' a t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hcR.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hcR.mono Ioi_subset_Ici_self) t ht)
      (hcR.continuousAt (Ici_mem_nhds ht))
  have hd₃ : HasDerivAt (fun τ ↦ if T ≤ τ then ∫ s in 0..(τ - T), J (a s) else 0)
      (if T ≤ t then J (a (t - T)) else 0) t := by
    rcases lt_or_gt_of_ne htT with htT' | htT'
    · rw [ite_eq_right (not_le.2 htT')]
      refine (hasDerivAt_const t (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds htT'] with τ hτ
      simp only [ite_eq_right (not_le.2 (mem_Iio.1 hτ))]
    · rw [ite_eq_left htT'.le]
      have hk : HasDerivAt (fun x ↦ ∫ s in 0..x, J (a s)) (J (a (t - T))) (t - T) := by
        have hpos : 0 < t - T := sub_pos.2 htT'
        exact intervalIntegral.integral_hasDerivAt_right
          ((J.continuous.comp_continuousOn (ha.mono Icc_subset_Ici_self)).intervalIntegrable_of_Icc
            hpos.le)
          (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
            (J.continuous.comp_continuousOn (ha.mono Ioi_subset_Ici_self)) _ hpos)
          (J.continuous.continuousAt.comp (hcontAt _ hpos))
      refine hk.comp_sub_const t T |>.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds htT'] with τ hτ
      simp only [ite_eq_left (le_of_lt (mem_Ioi.1 hτ))]
  refine ((hd₁.add hd₂).add hd₃).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with τ hτ
  exact responseIntegral_eq_add_of_hasDerivWithJump hG hT.le hτ.le (ha.mono Icc_subset_Ici_self)

variable [CompleteSpace E] in
/-- **The right time derivative of a response with a jump.** If `G = G(0) + ∫ G' + 1_{T ≤ ·} J`
on `[0, ∞)` with `T > 0` and the coefficients are continuous on `[0, u]`, then at every
`t ∈ [0, u)`, the jump time and `t = 0` included, the response `∫₀ᵗ G(t - s) a(s) ds` has the
right derivative `G(0) a(t) + ∫₀ᵗ G'(t - s) a(s) ds + 1_{T ≤ t} J a(t - T)`. At `t = T` the jump
contributes `J a(0)`: the right-continuous indicator `1_{T ≤ t}` gives the right derivative. -/
theorem hasDerivWithinAt_responseIntegral_of_hasDerivWithJump {G G' : ℝ → F →L[ℝ] E} {T : ℝ}
    {J : F →L[ℝ] E} {a : ℝ → F} (hG : HasDerivWithJump G G' T J) (hT : 0 < T) {u : ℝ}
    (ha : ContinuousOn a (Icc 0 u)) {t : ℝ} (ht : 0 ≤ t) (htu : t < u) :
    HasDerivWithinAt (responseIntegral G a)
      (G 0 (a t) + responseIntegral G' a t + if T ≤ t then J (a (t - T)) else 0) (Ici t) t := by
  -- `[0, u]` is a right neighbourhood of every point of `[0, u)`
  have hmem : ∀ x, 0 ≤ x → x < u → Icc 0 u ∈ 𝓝[>] x := fun x hx hxu ↦
    mem_of_superset (Ioo_mem_nhdsGT hxu) fun y hy ↦ ⟨hx.trans hy.1.le, hy.2.le⟩
  have hright : ∀ {g : ℝ → E} {x : ℝ}, 0 ≤ x → x < u → ContinuousOn g (Icc 0 u) →
      HasDerivWithinAt (fun τ ↦ ∫ s in 0..τ, g s) (g x) (Ici x) x := by
    intro g x hx hxu hg
    exact intervalIntegral.integral_hasDerivWithinAt_right
      ((hg.mono (Icc_subset_Icc_right hxu.le)).intervalIntegrable_of_Icc hx)
      ((hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem (hmem x hx hxu)))
      ((hg x ⟨hx, hxu.le⟩).mono_of_mem_nhdsWithin (hmem x hx hxu))
  have hd₁ : HasDerivWithinAt (fun τ ↦ ∫ s in 0..τ, G 0 (a s)) (G 0 (a t)) (Ici t) t :=
    hright ht htu ((G 0).continuous.comp_continuousOn ha)
  have hd₂ : HasDerivWithinAt (fun τ ↦ ∫ v in 0..τ, responseIntegral G' a v)
      (responseIntegral G' a t) (Ici t) t :=
    hright ht htu (continuousOn_responseIntegral_Icc (hG.integrableOn u) ha)
  have hd₃ : HasDerivWithinAt (fun τ ↦ if T ≤ τ then ∫ s in 0..(τ - T), J (a s) else 0)
      (if T ≤ t then J (a (t - T)) else 0) (Ici t) t := by
    by_cases hTt : T ≤ t
    · rw [ite_eq_left hTt]
      have hk : HasDerivWithinAt (fun x ↦ ∫ s in 0..x, J (a s)) (J (a (t - T))) (Ici (t - T))
          (t - T) :=
        hright (sub_nonneg.2 hTt) (by linarith) (J.continuous.comp_continuousOn ha)
      have hshift : HasDerivWithinAt (fun τ : ℝ ↦ τ - T) 1 (Ici t) t :=
        (hasDerivWithinAt_id t _).sub_const T
      have h := hk.scomp t hshift fun τ (hτ : t ≤ τ) ↦ (show t - T ≤ τ - T by linarith)
      simp only [one_smul] at h
      refine h.congr (fun τ (hτ : t ≤ τ) ↦ ?_) ?_
      · simp only [Function.comp_apply, ite_eq_left (hTt.trans hτ)]
      · simp only [Function.comp_apply, ite_eq_left hTt]
    · rw [ite_eq_right hTt]
      refine (hasDerivAt_const t (0 : E)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.1 hTt))] with τ hτ
        simp only [ite_eq_right (not_le.2 (mem_Iio.1 hτ))]
      · simp only [ite_eq_right hTt]
  refine ((hd₁.add hd₂).add hd₃).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds htu))] with τ hτ
    exact responseIntegral_eq_add_of_hasDerivWithJump hG hT.le (ht.trans hτ.1)
      (ha.mono (Icc_subset_Icc_right (mem_Iio.1 hτ.2).le))
  · exact responseIntegral_eq_add_of_hasDerivWithJump hG hT.le ht
      (ha.mono (Icc_subset_Icc_right htu.le))

/-- A jump `J` of `κ` at `T` is a jump `toSpanSingleton ℝ J` of the kernel
`τ ↦ toSpanSingleton ℝ (κ τ)`, whose weak derivative is `τ ↦ toSpanSingleton ℝ (κ' τ)`. -/
theorem hasDerivWithJump_toSpanSingleton {κ κ' : ℝ → E} {T : ℝ} {J : E}
    (h : HasDerivWithJump κ κ' T J) :
    HasDerivWithJump (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ))
      (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ' τ)) T
      (ContinuousLinearMap.toSpanSingleton ℝ J) where
  integrableOn τ := integrableOn_toSpanSingleton (h.integrableOn τ)
  eq_add τ hτ := by
    have hint : IntervalIntegrable (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ' τ))
        volume 0 τ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2
        (integrableOn_toSpanSingleton (h.integrableOn τ))
    refine ContinuousLinearMap.ext fun c ↦ ?_
    rw [add_apply, add_apply, ContinuousLinearMap.intervalIntegral_apply hint,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.toSpanSingleton_apply,
      h.eq_add τ hτ]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, intervalIntegral.integral_smul,
      smul_add]
    split_ifs <;> simp

variable [CompleteSpace E] in
/-- **The time derivative of a scalar Duhamel integral with a jump.** If
`κ = κ(0) + ∫ κ' + 1_{T ≤ ·} J` on `[0, ∞)` and `a` is continuous on `[0, ∞)`, then at every
`t > 0` other than `T`,
`d/dt ∫₀ᵗ a(s) κ(t - s) ds = a(t) κ(0) + ∫₀ᵗ a(s) κ'(t - s) ds + 1_{T ≤ t} a(t - T) J`. -/
theorem hasDerivAt_integral_smul_of_hasDerivWithJump {κ κ' : ℝ → E} {T : ℝ} {J : E}
    {a : ℝ → ℝ} (h : HasDerivWithJump κ κ' T J) (hT : 0 < T) (ha : ContinuousOn a (Ici 0))
    {t : ℝ} (ht : 0 < t) (htT : t ≠ T) :
    HasDerivAt (fun t ↦ ∫ s in 0..t, a s • κ (t - s))
      (a t • κ 0 + (∫ s in 0..t, a s • κ' (t - s)) + if T ≤ t then a (t - T) • J else 0) t := by
  have hfun : (fun t ↦ ∫ s in 0..t, a s • κ (t - s)) =
      responseIntegral (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ)) a :=
    funext fun t ↦ (responseIntegral_toSpanSingleton κ a t).symm
  have := hasDerivAt_responseIntegral_of_hasDerivWithJump (hasDerivWithJump_toSpanSingleton h)
    hT ha ht htT
  rw [hfun]
  convert this using 1
  rw [ContinuousLinearMap.toSpanSingleton_apply, responseIntegral_toSpanSingleton]
  split_ifs <;> simp

variable [CompleteSpace E] in
/-- **The right time derivative of a scalar Duhamel integral with a jump.** If
`κ = κ(0) + ∫ κ' + 1_{T ≤ ·} J` on `[0, ∞)`, `T > 0` and `a` is continuous on `[0, u]`, then at
every `t ∈ [0, u)`, `T` included,
`d⁺/dt ∫₀ᵗ a(s) κ(t - s) ds = a(t) κ(0) + ∫₀ᵗ a(s) κ'(t - s) ds + 1_{T ≤ t} a(t - T) J`. -/
theorem hasDerivWithinAt_integral_smul_of_hasDerivWithJump {κ κ' : ℝ → E} {T : ℝ} {J : E}
    {a : ℝ → ℝ} (h : HasDerivWithJump κ κ' T J) (hT : 0 < T) {u : ℝ}
    (ha : ContinuousOn a (Icc 0 u)) {t : ℝ} (ht : 0 ≤ t) (htu : t < u) :
    HasDerivWithinAt (fun t ↦ ∫ s in 0..t, a s • κ (t - s))
      (a t • κ 0 + (∫ s in 0..t, a s • κ' (t - s)) + if T ≤ t then a (t - T) • J else 0)
      (Ici t) t := by
  have hfun : (fun t ↦ ∫ s in 0..t, a s • κ (t - s)) =
      responseIntegral (fun τ ↦ ContinuousLinearMap.toSpanSingleton ℝ (κ τ)) a :=
    funext fun t ↦ (responseIntegral_toSpanSingleton κ a t).symm
  have := hasDerivWithinAt_responseIntegral_of_hasDerivWithJump
    (hasDerivWithJump_toSpanSingleton h) hT ha ht htu
  rw [hfun]
  convert this using 1
  rw [ContinuousLinearMap.toSpanSingleton_apply, responseIntegral_toSpanSingleton]
  split_ifs <;> simp

end PDE.Analysis.Evolution
