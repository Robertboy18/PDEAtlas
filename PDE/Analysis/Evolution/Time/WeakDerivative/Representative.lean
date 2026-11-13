/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.LocalConstant
public import PDE.Analysis.Evolution.Time.WeakDerivative.Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous representatives of weakly differentiable Banach-valued curves

An integrable weak derivative on a bounded interval determines a continuous
representative, including its endpoint values. Subtracting its Bochner primitive
leaves a function with zero weak derivative, hence an almost everywhere constant
function. The fundamental theorem then holds at every pair of times.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- An integrable weak derivative gives a continuous representative and the
fundamental theorem at all times in the closed interval. -/
theorem exists_continuous_representative_Icc
    {a b : ℝ} (hab : a < b) {u g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hg : IntegrableOn g (Ioo a b)) :
    ∃ v : ℝ → X, Continuous v ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ r in s..t, g r := by
  let G : ℝ → X := (Icc a b).indicator g
  have hG : Integrable G volume :=
    ((integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).mpr hg).integrable_indicator
      measurableSet_Icc
  have heq : G =ᵐ[volume.restrict (Ioo a b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact indicator_of_mem (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩) g
  let F : ℝ → X := fun t ↦ ∫ r in a..t, G r
  have hF : HasWeakTimeDerivativeOn (Ioo a b) F g :=
    ((hasWeakTimeDerivativeOn_intervalPrimitive hG.locallyIntegrable a).mono
      (subset_univ _)).congr_ae_restrict measurableSet_Ioo Filter.EventuallyEq.rfl heq
  have hz : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ u t - F t) 0 := by
    simpa only [sub_self, Pi.zero_def] using hweak.sub hF
  obtain ⟨c, hc⟩ := hz.exists_ae_eq_const_on_Ioo_of_zero hab
  have hFcont : Continuous F :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hG.intervalIntegrable) a
  refine ⟨fun t ↦ F t + c, hFcont.add continuous_const, ?_, ?_⟩
  · filter_upwards [hc] with t ht
    exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  · intro s hs t ht
    rw [add_sub_add_right_eq_sub]
    change (∫ r in a..t, G r) - (∫ r in a..s, G r) = _
    rw [intervalIntegral.integral_interval_sub_left hG.intervalIntegrable hG.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro r hr
    exact indicator_of_mem (uIcc_subset_Icc hs ht hr) g

/-- A continuous curve with continuous weak derivative has the corresponding
derivative throughout the closed interval, including its two endpoints. -/
theorem hasDerivWithinAt_of_continuousOn
    {a b : ℝ} (hab : a < b) {v w : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) v w)
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt v (w t) (Icc a b) t := by
  obtain ⟨z, hz, heq, hFTC⟩ := hweak.exists_continuous_representative_Icc hab
    (hw.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  have heqcc : v =ᵐ[volume.restrict (Icc a b)] z := by
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have heqOn := Measure.eqOn_Icc_of_ae_eq volume hab.ne heqcc hv hz.continuousOn
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hprimitive (r : ℝ) (hr : r ∈ Icc a b) :
      v r = (∫ q in a..r, w q) + v a := by
    apply sub_eq_iff_eq_add.mp
    rw [heqOn hr, heqOn ha]
    exact hFTC a ha r hr
  have hint : IntervalIntegrable w volume a t :=
    (hw.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc a b) (t := Icc a b) hint
    (hw.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hw t ht)
  exact (hd.add_const (v a)).congr_of_mem hprimitive ht

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A continuous classical derivative on the interior gives the local weak
derivative. Only continuity, rather than an ambient derivative, is needed at
the two endpoints. -/
theorem hasWeakTimeDerivativeOn_of_continuousOn_hasDerivAt [CompleteSpace X]
    {a b : ℝ} {v w : ℝ → X}
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt v (w t) t) :
    HasWeakTimeDerivativeOn (Ioo a b) v w := by
  let G : ℝ → X := (Icc a b).indicator w
  have hG : Integrable G volume :=
    hw.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have heq : G =ᵐ[volume.restrict (Ioo a b)] w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact indicator_of_mem (Ioo_subset_Icc_self ht) w
  have hc : HasWeakTimeDerivativeOn univ (fun _ : ℝ ↦ v a) (fun _ ↦ (0 : X)) :=
    .of_absolutelyContinuousOnInterval continuous_const.locallyIntegrable
      continuous_const.locallyIntegrable
      (fun _ _ ↦ (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval)
      (.of_forall fun t ↦ hasDerivAt_const t (v a))
  have hF : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ (∫ r in a..t, G r) + v a) G := by
    simpa only [add_zero] using
      ((hasWeakTimeDerivativeOn_intervalPrimitive hG.locallyIntegrable a).add hc).mono
        (subset_univ _)
  apply hF.congr_ae_restrict measurableSet_Ioo _ heq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hint : IntervalIntegrable w volume a t :=
    (hw.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1.le
    (hv.mono (Icc_subset_Icc le_rfl ht.2.le))
    (fun r hr ↦ hd r ⟨hr.1, hr.2.trans ht.2⟩) hint
  have hGw : (∫ r in a..t, G r) = ∫ r in a..t, w r := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact indicator_of_mem (uIcc_subset_Icc ⟨le_rfl, ht.1.le.trans ht.2.le⟩
      (Ioo_subset_Icc_self ht) hr) w
  rw [hGw, hFTC, sub_add_cancel]

/-- Averaging the fundamental theorem over the second time bounds every value
by the mean norm of the curve and the integral norm of its derivative. -/
theorem norm_le_average_add_integral_of_intervalIntegral
    {a b : ℝ} (hab : a < b) {u g v : ℝ → X}
    (hu : IntegrableOn u (Ioo a b)) (hg : IntegrableOn g (Ioo a b))
    (huv : u =ᵐ[volume.restrict (Ioo a b)] v)
    (hFTC : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t - v s = ∫ r in s..t, g r)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖v t‖ ≤ (b - a)⁻¹ * (∫ r in Ioo a b, ‖u r‖) + ∫ r in Ioo a b, ‖g r‖ := by
  have hgcc : IntegrableOn g (Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).mpr hg
  have hbound (s : ℝ) (hs : s ∈ Icc a b) :
      ‖v t‖ ≤ ‖v s‖ + ∫ r in Ioo a b, ‖g r‖ := by
    calc
      ‖v t‖ ≤ ‖v s‖ + ‖v t - v s‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖v s‖ + ‖∫ r in s..t, g r‖ := by rw [hFTC s hs t ht]
      _ ≤ ‖v s‖ + ∫ r in uIoc s t, ‖g r‖ :=
        add_le_add_right intervalIntegral.norm_integral_le_integral_norm_uIoc _
      _ ≤ ‖v s‖ + ∫ r in Icc a b, ‖g r‖ := by
        apply add_le_add_right
        exact setIntegral_mono_set hgcc.norm (.of_forall fun _ ↦ norm_nonneg _)
          (.of_forall fun r hr ↦ uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr))
      _ = ‖v s‖ + ∫ r in Ioo a b, ‖g r‖ := by
        rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hboundAE : ∀ᵐ s ∂volume.restrict (Ioo a b),
      ‖v t‖ ≤ ‖u s‖ + ∫ r in Ioo a b, ‖g r‖ := by
    filter_upwards [huv, ae_restrict_mem measurableSet_Ioo] with s hs hsab
    rw [hs]
    exact hbound s ⟨hsab.1.le, hsab.2.le⟩
  have hmean := integral_mono_ae (integrable_const ‖v t‖)
    (hu.norm.add (integrable_const (∫ r in Ioo a b, ‖g r‖))) hboundAE
  simp only [Pi.add_apply] at hmean
  rw [integral_add hu.norm (integrable_const _), integral_const, integral_const,
    measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le hab.le] at hmean
  simp only [smul_eq_mul] at hmean
  calc
    ‖v t‖ ≤ ((∫ r in Ioo a b, ‖u r‖) +
        (b - a) * ∫ r in Ioo a b, ‖g r‖) / (b - a) :=
      (le_div_iff₀ (sub_pos.mpr hab)).mpr (by simpa only [mul_comm] using hmean)
    _ = _ := by
      rw [add_div, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hab.ne'), div_eq_mul_inv,
        mul_comm (∫ r in Ioo a b, ‖u r‖)]

end PDE.Analysis.Evolution
