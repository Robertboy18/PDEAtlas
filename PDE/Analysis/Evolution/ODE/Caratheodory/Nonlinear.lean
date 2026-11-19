/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Volterra
public import PDE.Analysis.Evolution.Time.FundamentalTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Nonlinear Carathéodory construction

On a finite interval, measurable time sections and a uniform state Lipschitz
bound suffice to construct the integral curve. Only the value at zero needs
an integrable bound: along any continuous curve, the remaining growth is at
most `K` times its bounded norm. Joint measurability follows from Mathlib's
Carathéodory measurability theorem, using a separable Banach state space.

Time measurability is stated for the zero extension of each section, so the
field is unrestricted outside the interval. The shared Volterra estimate
constructs a unique fixed point. The Banach-valued FTC identifies this curve
with every absolutely continuous solution of the almost-everywhere equation.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

open PDE.Analysis.ODE

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Zero extension of the nonlinear field along a continuous curve. -/
def nonlinearIntegrandOn {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E) (u : C(Set.Icc a b, E)) : ℝ → E :=
  Set.indicator (Set.Icc a b) (fun t ↦ F t (Set.IccExtend hab u t))

omit [NormedSpace ℝ E] in
/-- Measurable time sections and state continuity give a measurable integrand.
The zero extension lets the argument use only state regularity on `[a,b]`. -/
theorem measurable_nonlinearIntegrandOn {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (u : C(Set.Icc a b, E)) : Measurable (nonlinearIntegrandOn hab F u) := by
  let G : E → ℝ → E := fun x ↦ Set.indicator (Set.Icc a b) (fun t ↦ F t x)
  have hGcont (t : ℝ) : Continuous (fun x ↦ G x t) := by
    by_cases ht : t ∈ Set.Icc a b
    · simpa only [G, Set.indicator_of_mem ht] using (hK t ht).continuous
    · simpa only [G, Set.indicator_of_notMem ht] using
        (continuous_const : Continuous (fun _x : E ↦ (0 : E)))
  have hG : Measurable (Function.uncurry G) :=
    measurable_uncurry_of_continuous_of_measurable hGcont hF
  exact hG.comp ((u.continuous.Icc_extend' (h := hab)).measurable.prodMk measurable_id)

omit [NormedSpace ℝ E] in
/-- The Lipschitz bound reduces trajectory integrability to the value at zero. -/
theorem integrable_nonlinearIntegrandOn {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    (u : C(Set.Icc a b, E)) : Integrable (nonlinearIntegrandOn hab F u) volume := by
  have hmeas : AEStronglyMeasurable (nonlinearIntegrandOn hab F u) volume :=
    (measurable_nonlinearIntegrandOn hab F hF K hK u).aestronglyMeasurable
  have hbound : Integrable
      (Set.indicator (Set.Icc a b) (fun t ↦ (K : ℝ) * ‖u‖ + ‖F t 0‖)) volume :=
    ((integrableOn_const (C := (K : ℝ) * ‖u‖)
      (hs := measure_Icc_lt_top.ne)).add hzero.norm).integrable_indicator measurableSet_Icc
  apply hbound.mono' hmeas
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc a b
  · simp only [nonlinearIntegrandOn, Set.indicator_of_mem ht,
      Set.IccExtend_of_mem hab u ht]
    calc
      ‖F t (u ⟨t, ht⟩)‖ ≤ ‖F t (u ⟨t, ht⟩) - F t 0‖ + ‖F t 0‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (F t (u ⟨t, ht⟩) - F t 0) (F t 0)
      _ ≤ (K : ℝ) * ‖u ⟨t, ht⟩‖ + ‖F t 0‖ := by
        have h := (hK t ht).dist_le_mul (u ⟨t, ht⟩) 0
        simpa only [dist_eq_norm, sub_zero] using add_le_add h (le_refl ‖F t 0‖)
      _ ≤ (K : ℝ) * ‖u‖ + ‖F t 0‖ := by
        gcongr
        exact ContinuousMap.norm_coe_le_norm u ⟨t, ht⟩
  · simp only [nonlinearIntegrandOn, Set.indicator_of_notMem ht, norm_zero, le_refl]

omit [NormedSpace ℝ E] in
/-- Along any curve `u` continuous on `[a, b]`, the function `t ↦ F t (u t)` is
integrable on `[a, b]`. -/
theorem integrableOn_field_apply_continuousOn {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    {u : ℝ → E} (hu : ContinuousOn u (Set.Icc a b)) :
    IntegrableOn (fun t ↦ F t (u t)) (Set.Icc a b) volume := by
  let v : C(Set.Icc a b, E) := ⟨fun t ↦ u t, continuousOn_iff_continuous_domRestrict.mp hu⟩
  have hv := integrable_nonlinearIntegrandOn hab F hF K hK hzero v
  apply hv.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [nonlinearIntegrandOn, Set.indicator_of_mem ht,
    Set.IccExtend_of_mem hab v ht]
  rfl

section Complete

variable [CompleteSpace E]

/-- The nonlinear Picard operator on the complete space of continuous curves. -/
def nonlinearPicardMap {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    (x₀ : E) : C(Set.Icc a b, E) → C(Set.Icc a b, E) := fun u ↦
  ⟨fun t ↦ x₀ + ∫ s in a..t.1, nonlinearIntegrandOn hab F u s,
    continuous_const.add
      (Continuous.comp
        ((integrable_nonlinearIntegrandOn hab F hF K hK hzero u).continuous_primitive a)
        continuous_subtype_val)⟩

/-- The shared factorial estimate constructs the unique nonlinear fixed point
on any finite interval, with no smallness condition on its length. -/
theorem existsUnique_isFixedPt_nonlinearPicardMap {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    (x₀ : E) :
    ∃! u : C(Set.Icc a b, E),
      IsFixedPt (nonlinearPicardMap hab F hF K hK hzero x₀) u := by
  apply existsUnique_isFixedPt_volterra ⟨_, le_rfl, hab⟩
    (nonlinearPicardMap hab F hF K hK hzero x₀) (nonlinearIntegrandOn hab F) x₀ K
    (fun u ↦ (integrable_nonlinearIntegrandOn hab F hF K hK hzero u).integrableOn)
    (fun _ _ ↦ rfl)
  intro u v t
  simpa only [nonlinearIntegrandOn, Set.indicator_of_mem t.2,
    Set.IccExtend_of_mem hab u t.2, Set.IccExtend_of_mem hab v t.2,
    dist_eq_norm] using (hK t t.2).dist_le_mul (u t) (v t)

/-- The integral curve is unique among continuous curves. The integrand
in the equation is the original field, without its zero extension. -/
theorem existsUnique_nonlinear_integralCurve {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    (x₀ : E) :
    ∃! u : C(Set.Icc a b, E), ∀ t : Set.Icc a b,
      u t = x₀ + ∫ s in a..t.1, F s (Set.IccExtend hab u s) := by
  have heq (u : C(Set.Icc a b, E)) (t : Set.Icc a b) :
      (∫ s in a..t.1, nonlinearIntegrandOn hab F u s) =
        ∫ s in a..t.1, F s (Set.IccExtend hab u s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI := (Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2) hs
    exact Set.indicator_of_mem hsI _
  have hiff (u : C(Set.Icc a b, E)) :
      IsFixedPt (nonlinearPicardMap hab F hF K hK hzero x₀) u ↔
        ∀ t : Set.Icc a b,
          u t = x₀ + ∫ s in a..t.1, F s (Set.IccExtend hab u s) := by
    constructor
    · intro hu t
      have ht := congrArg (fun w : C(Set.Icc a b, E) ↦ w t) hu
      change x₀ + (∫ s in a..t.1, nonlinearIntegrandOn hab F u s) = u t at ht
      rw [heq] at ht
      exact ht.symm
    · intro hu
      apply ContinuousMap.ext
      intro t
      change x₀ + (∫ s in a..t.1, nonlinearIntegrandOn hab F u s) = u t
      rw [heq]
      exact (hu t).symm
  obtain ⟨u, hu, huniq⟩ := existsUnique_isFixedPt_nonlinearPicardMap hab F hF K hK hzero x₀
  exact ⟨u, (hiff u).mp hu, fun v hv ↦ huniq v ((hiff v).mpr hv)⟩

/-- Recover the integral equation of any absolutely continuous a.e. solution.
Continuity and the data imply integrability of its derivative, allowing the
Banach-valued FTC to apply on every initial subinterval. -/
theorem integral_eq_of_nonlinear_ae_equation {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    {u : ℝ → E} {x₀ : E} (hu : AbsolutelyContinuousOnInterval u a b)
    (hinitial : u a = x₀)
    (hderiv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt u (F t (u t)) t) :
    ∀ t ∈ Set.Icc a b, u t = x₀ + ∫ s in a..t, F s (u s) := by
  have hucont : ContinuousOn u (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using hu.continuousOn
  have hg := integrableOn_field_apply_continuousOn hab F hF K hK hzero hucont
  intro t ht
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc_right ht.2
  have huAt := hu.mono (Set.uIcc_subset_uIcc_left (by
    simpa only [Set.uIcc_of_le hab] using ht))
  have hdAt : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), HasDerivAt u (F s (u s)) s :=
    hderiv.filter_mono (MeasureTheory.ae_mono
      ((volume : Measure ℝ).restrict_mono_set
        (show Set.Ioc a t ⊆ Set.Ioc a b from fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩)))
  have hFTC :=
    AbsolutelyContinuousOnInterval.intervalIntegral_eq_sub_of_ae_hasDerivAt_normedSpace
      ht.1 huAt (hg.mono_set hsub) hdAt
  rw [hFTC, hinitial]
  abel

/-- Any two absolutely continuous a.e. solutions with the same initial value
agree on the interval. This uses the Banach FTC and the constructed unique
integral curve, so no finite-dimensional hypothesis is needed. -/
theorem eqOn_of_nonlinear_ae_equation {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    {u v : ℝ → E} {x₀ : E}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hua : u a = x₀) (hva : v a = x₀)
    (hdu : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt u (F t (u t)) t)
    (hdv : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt v (F t (v t)) t) :
    Set.EqOn u v (Set.Icc a b) := by
  have hucont : ContinuousOn u (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using hu.continuousOn
  have hvcont : ContinuousOn v (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using hv.continuousOn
  let U : C(Set.Icc a b, E) := ⟨fun t ↦ u t, continuousOn_iff_continuous_domRestrict.mp hucont⟩
  let V : C(Set.Icc a b, E) := ⟨fun t ↦ v t, continuousOn_iff_continuous_domRestrict.mp hvcont⟩
  have hU := integral_eq_of_nonlinear_ae_equation hab F hF K hK hzero hu hua hdu
  have hV := integral_eq_of_nonlinear_ae_equation hab F hF K hK hzero hv hva hdv
  have hcurve (w : ℝ → E) (W : C(Set.Icc a b, E))
      (hw : ∀ t : Set.Icc a b, W t = w t)
      (heq : ∀ t ∈ Set.Icc a b, w t = x₀ + ∫ s in a..t, F s (w s)) :
      ∀ t : Set.Icc a b,
        W t = x₀ + ∫ s in a..t.1, F s (Set.IccExtend hab W s) := by
    intro t
    rw [hw, heq t t.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI := (Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2) hs
    change F s (w s) = F s (Set.IccExtend hab W s)
    rw [Set.IccExtend_of_mem hab W hsI, hw]
  obtain ⟨w, _, huniq⟩ := existsUnique_nonlinear_integralCurve hab F hF K hK hzero x₀
  have hUV : U = V :=
    (huniq U (hcurve u U (fun _ ↦ rfl) hU)).trans
      (huniq V (hcurve v V (fun _ ↦ rfl) hV)).symm
  intro t ht
  exact congrArg (fun W : C(Set.Icc a b, E) ↦ W ⟨t, ht⟩) hUV

/-- Construct an absolutely continuous trajectory and its a.e. differential
 equation. The same representative is a global primitive of the zero-extended
 field along itself, which also identifies its Bochner integrand. -/
theorem exists_nonlinear_caratheodory_trajectory {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → E → E)
    (hF : ∀ x, Measurable (Set.indicator (Set.Icc a b) (fun t ↦ F t x)))
    (K : NNReal) (hK : ∀ t ∈ Set.Icc a b, LipschitzWith K (F t))
    (hzero : IntegrableOn (fun t ↦ F t 0) (Set.Icc a b) volume)
    (x₀ : E) :
    ∃ U : ℝ → E, U a = x₀ ∧ AbsolutelyContinuousOnInterval U a b ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt U (F t (U t)) t) ∧
      Integrable (Set.indicator (Set.Icc a b) (fun t ↦ F t (U t))) volume ∧
      (∀ t, U t = x₀ + ∫ s in a..t,
        Set.indicator (Set.Icc a b) (fun r ↦ F r (U r)) s) := by
  obtain ⟨u, hu, _⟩ := existsUnique_isFixedPt_nonlinearPicardMap hab F hF K hK hzero x₀
  let g := nonlinearIntegrandOn hab F u
  have hg : Integrable g volume := integrable_nonlinearIntegrandOn hab F hF K hK hzero u
  let U : ℝ → E := fun t ↦ x₀ + ∫ s in a..t, g s
  have hUu (t : Set.Icc a b) : U t = u t :=
    congrArg (fun w : C(Set.Icc a b, E) ↦ w t) hu
  have hfield : g = Set.indicator (Set.Icc a b) (fun t ↦ F t (U t)) := by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp only [g, nonlinearIntegrandOn, Set.indicator_of_mem ht,
        Set.IccExtend_of_mem hab u ht, hUu ⟨t, ht⟩]
    · simp only [g, nonlinearIntegrandOn, Set.indicator_of_notMem ht]
  have hUac : AbsolutelyContinuousOnInterval U a b := by
    have hprimitive :
        AbsolutelyContinuousOnInterval (fun t ↦ ∫ s in a..t, g s) a b :=
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
        (hg.intervalIntegrable (a := a) (b := b)) (c := a) Set.left_mem_uIcc
    have hconst : AbsolutelyContinuousOnInterval (fun _t : ℝ ↦ x₀) a b :=
      (LipschitzWith.const x₀).lipschitzOnWith.absolutelyContinuousOnInterval
    apply (hconst.add hprimitive).congr
    intro t _
    rfl
  have hd : ∀ᵐ t ∂volume, HasDerivAt U (g t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with t ht
    simpa only [U] using (ht a).const_add x₀
  have hdOn : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt U (F t (U t)) t := by
    have hd' : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt U (g t) t :=
      hd.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
    filter_upwards [hd', ae_restrict_mem measurableSet_Ioc] with t ht htI
    have htC : t ∈ Set.Icc a b := ⟨htI.1.le, htI.2⟩
    simpa only [hfield, Set.indicator_of_mem htC] using ht
  refine ⟨U, by simp [U], hUac, hdOn, ?_, ?_⟩
  · rwa [← hfield]
  · intro t
    exact congrArg (fun h : ℝ → E ↦ x₀ + ∫ s in a..t, h s) hfield

end Complete

end PDE.Analysis.Evolution
