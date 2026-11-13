/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiating a characteristic identity in its label

Let `X` be a flow on `[0, T]` whose label derivative is the Jacobian
`J a s = exp (∫₀ˢ c (X a r) r dr)`, and suppose a field `φ` satisfies, along every
characteristic,

  `φ (X a t) t = φ₀ a + ∫₀ᵗ G (X a s) s ds`.

If the spatial slices of `φ`, `φ₀` and `G` are differentiable and the spatial derivative `G'` is
bounded and jointly measurable, the spatial derivative `φ'` satisfies

  `φ' (X a t) t = φ₀' a + ∫₀ᵗ (G' (X a s) s - c (X a s) s * φ' (X a s) s) ds`.

Differentiating under the integral first gives the identity weighted by the Jacobian,
`J a t * φ' (X a t) t = φ₀' a + ∫₀ᵗ J a s * G' (X a s) s ds`. Its right side is absolutely
continuous in time and the reciprocal Jacobian is `C¹`, so integration by parts for absolutely
continuous functions removes the weight. No time derivative of `φ'` is assumed.

## Main results

* `eq_add_integral_of_mul_exp_eq`: removing a `C¹` exponential weight from an integral identity.
* `deriv_characteristic_integral`: the characteristic identity for the spatial derivative.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.Analysis.ODE

/-- If `Φ t * exp (∫₀ᵗ κ) = Φ₀ + ∫₀ᵗ h` on `[0, T]` for a continuous `κ` and an integrable `h`,
then `Φ t = Φ₀ + ∫₀ᵗ (h s * exp (-∫₀ˢ κ) - κ s * Φ s) ds` on `[0, T]`. -/
theorem eq_add_integral_of_mul_exp_eq {T Φ₀ : ℝ} {Φ h κ : ℝ → ℝ} (hκ : Continuous κ)
    (hh : IntervalIntegrable h volume 0 T)
    (heq : ∀ t ∈ Icc 0 T, Φ t * Real.exp (∫ s in 0..t, κ s) = Φ₀ + ∫ s in 0..t, h s) :
    ∀ t ∈ Icc 0 T,
      Φ t = Φ₀ + ∫ s in 0..t, (h s * Real.exp (-∫ r in 0..s, κ r) - κ s * Φ s) := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  have hht : IntervalIntegrable h volume 0 t :=
    hh.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le ht.1 ht.2))
  let Ψ : ℝ → ℝ := fun s ↦ Φ₀ + ∫ r in 0..s, h r
  let P : ℝ → ℝ := fun s ↦ ∫ r in 0..s, κ r
  let g : ℝ → ℝ := fun s ↦ Real.exp (-P s)
  have hP (s : ℝ) : HasDerivAt P (κ s) s := (hκ.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hg (s : ℝ) : HasDerivAt g (-(κ s) * g s) s := by
    simpa only [g, mul_comm] using (hP s).fun_neg.exp
  have hgC : ContDiff ℝ 1 g := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s ↦ (hg s).differentiableAt, ?_⟩
    rw [show deriv g = fun s ↦ -(κ s) * g s from funext fun s ↦ (hg s).deriv]
    exact (hκ.neg).mul (continuous_iff_continuousAt.mpr fun s ↦ (hg s).continuousAt)
  have hΨac : AbsolutelyContinuousOnInterval Ψ 0 t :=
    (contDiffOn_const (c := Φ₀)).absolutelyContinuousOnInterval.add
      (hht.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  have hgac : AbsolutelyContinuousOnInterval g 0 t :=
    hgC.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hΨac.integral_deriv_mul_eq_sub hgac
  have hΨΦ (s : ℝ) (hs : s ∈ Icc 0 T) : Ψ s * g s = Φ s := by
    simp only [Ψ, g]
    rw [← heq s hs, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hΨ0 : Ψ 0 * g 0 = Φ₀ := by
    simp only [Ψ, g, P, intervalIntegral.integral_same, add_zero, neg_zero, Real.exp_zero,
      mul_one]
  rw [hΨΦ t ht, hΨ0] at hibp
  have hcongr : ∫ s in 0..t, (deriv Ψ s * g s + Ψ s * deriv g s) =
      ∫ s in 0..t, (h s * Real.exp (-∫ r in 0..s, κ r) - κ s * Φ s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hht.ae_hasDerivAt_integral] with s hs hsI
    have hsI' : s ∈ uIcc 0 t := uIoc_subset_uIcc hsI
    have hΨd : HasDerivAt Ψ (h s) s := (hs hsI' 0 (by simp)).const_add Φ₀
    rw [hΨd.deriv, (hg s).deriv]
    have := hΨΦ s (hsub hsI')
    simp only [g, P] at this ⊢
    rw [← this]
    ring
  rw [← hcongr, hibp]
  ring

/-- The spatial derivative of a field transported along a flow satisfies the characteristic
identity obtained by differentiating in the label. The flow `X` has label derivative
`exp (∫₀ˢ c (X a r) r dr)` on `[0, T]` with a bounded jointly continuous `c`; the source `G` has
bounded, jointly measurable spatial derivative `G'`. -/
theorem deriv_characteristic_integral {T K C : ℝ} {X c φ φ' G G' : ℝ → ℝ → ℝ}
    {φ₀ φ₀' : ℝ → ℝ}
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2))
    (hXa : ∀ a, ∀ s ∈ Icc 0 T,
      HasDerivAt (fun b ↦ X b s) (Real.exp (∫ r in 0..s, c (X a r) r)) a)
    (hc : Continuous (Function.uncurry c)) (hcb : ∀ x s, |c x s| ≤ C)
    (hφ : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (fun y ↦ φ y t) (φ' x t) x)
    (hφ₀ : ∀ x, HasDerivAt φ₀ (φ₀' x) x)
    (hG : ∀ s ∈ Icc 0 T, ∀ x, HasDerivAt (fun y ↦ G y s) (G' x s) x)
    (hGm : Measurable (fun p : ℝ × ℝ ↦ G p.1 p.2))
    (hG'm : Measurable (fun p : ℝ × ℝ ↦ G' p.1 p.2))
    (hGb : ∀ s ∈ Icc 0 T, ∀ x, |G x s| ≤ K) (hG'b : ∀ s ∈ Icc 0 T, ∀ x, |G' x s| ≤ K)
    (heq : ∀ a, ∀ t ∈ Icc 0 T, φ (X a t) t = φ₀ a + ∫ s in 0..t, G (X a s) s) :
    ∀ a, ∀ t ∈ Icc 0 T, φ' (X a t) t =
      φ₀' a + ∫ s in 0..t, (G' (X a s) s - c (X a s) s * φ' (X a s) s) := by
  intro a₀
  rcases lt_or_ge T 0 with hT | hT
  · exact fun t ht ↦ absurd (ht.1.trans ht.2) hT.not_ge
  have hC : 0 ≤ C := (abs_nonneg _).trans (hcb 0 0)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hG'b 0 ⟨le_rfl, hT⟩ 0)
  have hXc (a : ℝ) : ContinuousOn (X a) (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hX.comp (continuous_const.prodMk continuous_id)
  have hpath (a : ℝ) : ContinuousOn (fun s ↦ (X a s, s)) (Icc 0 T) :=
    (hXc a).prodMk continuousOn_id
  have hmeasIcc {H : ℝ → ℝ → ℝ} (hH : Measurable (fun p : ℝ × ℝ ↦ H p.1 p.2)) (a : ℝ) :
      AEStronglyMeasurable (fun s ↦ H (X a s) s) (volume.restrict (Icc 0 T)) :=
    (hH.comp_aemeasurable ((hpath a).aemeasurable measurableSet_Icc)).aestronglyMeasurable
  -- The Jacobian along the base characteristic.
  let κ : ℝ → ℝ := fun r ↦ c (X a₀ (projIcc 0 T hT r)) (projIcc 0 T hT r)
  have hκ : Continuous κ :=
    hc.comp (((hX.comp ((continuous_const (y := a₀)).prodMk (continuous_projIcc (h := hT)))).prodMk
      (continuous_subtype_val.comp (continuous_projIcc (h := hT)))))
  have hκeq (s : ℝ) (hs : s ∈ Icc 0 T) :
      ∫ r in 0..s, c (X a₀ r) r = ∫ r in 0..s, κ r :=
    intervalIntegral.integral_congr fun r hr ↦ by
      rw [uIcc_of_le hs.1] at hr
      simp only [κ, projIcc_of_mem hT ⟨hr.1, hr.2.trans hs.2⟩]
  have hJm : AEStronglyMeasurable (fun s ↦ Real.exp (∫ r in 0..s, c (X a₀ r) r))
      (volume.restrict (Icc 0 T)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Icc
    refine (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr fun s ↦
      (hκ.integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt)).continuousOn.congr fun s hs ↦ ?_
    simp only [Function.comp_apply, hκeq s hs]
  -- `‖G' J‖ ≤ K exp (C T)` on `[0, T]`, from `|∫₀ˢ c| ≤ C s`
  have hFb (a s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖G' (X a s) s * Real.exp (∫ r in 0..s, c (X a r) r)‖ ≤ K * Real.exp (C * T) := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
      (f := fun r ↦ c (X a r) r) (C := C) fun r _ ↦ (Real.norm_eq_abs _).trans_le (hcb _ _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hn
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (hG'b s hs _) (Real.exp_le_exp.mpr ((le_abs_self _).trans
      (hn.trans (mul_le_mul_of_nonneg_left hs.2 hC)))) (Real.exp_pos _).le hK
  -- Differentiation of both sides in the label at `a₀`.
  have hweighted (t : ℝ) (ht : t ∈ Icc 0 T) :
      φ' (X a₀ t) t * Real.exp (∫ r in 0..t, c (X a₀ r) r) =
        φ₀' a₀ + ∫ s in 0..t, G' (X a₀ s) s * Real.exp (∫ r in 0..s, c (X a₀ r) r) := by
    have hsub : Ι 0 t ⊆ Icc 0 T := by
      rw [uIoc_of_le ht.1]
      exact fun s hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩
    have hrestrict {f : ℝ → ℝ}
        (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 T))) :
        AEStronglyMeasurable f (volume.restrict (Ι 0 t)) :=
      hf.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := t) (x₀ := a₀) (s := univ)
      (F := fun a s ↦ G (X a s) s)
      (F' := fun a s ↦ G' (X a s) s * Real.exp (∫ r in 0..s, c (X a r) r))
      (bound := fun _ ↦ K * Real.exp (C * T)) univ_mem
      (Eventually.of_forall fun a ↦ hrestrict (hmeasIcc hGm a))
      (by
        apply (intervalIntegrable_const (c := K)).mono_fun' (hrestrict (hmeasIcc hGm a₀))
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        rw [Real.norm_eq_abs]
        exact hGb s (hsub hs) _)
      (hrestrict ((hmeasIcc hG'm a₀).mul hJm))
      (Eventually.of_forall fun s hs a _ ↦ hFb a s (hsub hs))
      intervalIntegrable_const
      (Eventually.of_forall fun s hs a _ ↦ by
        simpa only [Function.comp_def] using (hG s (hsub hs) (X a s)).comp a (hXa a s (hsub hs)))
    -- the left side through the chain rule, the right side under the integral
    have hleft : HasDerivAt (fun a ↦ φ₀ a + ∫ s in 0..t, G (X a s) s)
        (φ' (X a₀ t) t * Real.exp (∫ r in 0..t, c (X a₀ r) r)) a₀ := by
      simpa only [Function.comp_def, (heq · t ht)] using (hφ t ht (X a₀ t)).comp a₀ (hXa a₀ t ht)
    exact hleft.unique ((hφ₀ a₀).add hdiff.2)
  -- Removal of the weight.
  have hhint : IntervalIntegrable
      (fun s ↦ G' (X a₀ s) s * Real.exp (∫ r in 0..s, c (X a₀ r) r)) volume 0 T := by
    have hm : AEStronglyMeasurable
        (fun s ↦ G' (X a₀ s) s * Real.exp (∫ r in 0..s, c (X a₀ r) r))
        (volume.restrict (Ι 0 T)) :=
      ((hmeasIcc hG'm a₀).mul hJm).mono_measure
        (Measure.restrict_mono (by rw [uIoc_of_le hT]; exact Ioc_subset_Icc_self) le_rfl)
    apply (intervalIntegrable_const (c := K * Real.exp (C * T))).mono_fun' hm
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hT] at hs
    exact hFb a₀ s ⟨hs.1.le, hs.2⟩
  have hremove := eq_add_integral_of_mul_exp_eq (Φ := fun t ↦ φ' (X a₀ t) t)
    (Φ₀ := φ₀' a₀) hκ hhint fun t ht ↦ by simpa only [hκeq t ht] using hweighted t ht
  intro t ht
  rw [hremove t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [κ, projIcc_of_mem hT hs']
  rw [← hκeq s hs', mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end PDE.Analysis.ODE
