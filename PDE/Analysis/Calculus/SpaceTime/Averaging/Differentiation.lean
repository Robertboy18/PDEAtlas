/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ParametricIntervalRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Differentiation of time averages

A fixed-width time average differentiates in time by the difference of its
endpoint values. Jointly continuous spatial derivatives pass through the
average by compact-interval differentiation. These facts use ordinary
interval integrals and do not require mixed derivatives of the original field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology Interval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Translating an interval average differentiates a continuous Banach-valued
function by its endpoint difference. The averaging width may have either sign. -/
theorem hasDerivAt_timeAverage
    {f : ℝ → F} {I : Set ℝ} {t h : ℝ}
    (hI : IsOpen I) (hf : ContinuousOn f I) (hh : h ≠ 0)
    (hsegment : uIcc t (t + h) ⊆ I) :
    HasDerivAt (fun r ↦ ∫ s in (0 : ℝ)..1, f (r + h * s))
      (h⁻¹ • (f (t + h) - f t)) t := by
  have ht := hsegment left_mem_uIcc
  have hth := hsegment right_mem_uIcc
  have hFTC := intervalIntegral.integral_hasFDerivAt (hf.mono hsegment).intervalIntegrable
    (hf.stronglyMeasurableAtFilter hI t ht)
    (hf.stronglyMeasurableAtFilter hI (t + h) hth)
    (hf.continuousAt (hI.mem_nhds ht)) (hf.continuousAt (hI.mem_nhds hth))
  have hends : HasDerivAt (fun r : ℝ ↦ (r, r + h)) (1, 1) t :=
    (hasDerivAt_id t).prodMk ((hasDerivAt_id t).add_const h)
  have hderiv := (hFTC.comp_hasDerivAt t hends).const_smul h⁻¹
  simpa only [intervalIntegral.integral_comp_add_mul f hh, mul_zero, add_zero, mul_one,
    FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_smul,
    Pi.smul_apply, Function.comp_def] using! hderiv

/-- When the original time derivative is continuous, the derivative of the
average is its average. The endpoint formula and the fundamental theorem
of calculus identify the same derivative. -/
theorem hasDerivAt_timeAverage_of_derivative
    {f D : ℝ → F} {I : Set ℝ} {t h : ℝ}
    (hI : IsOpen I) (hD : ContinuousOn D I)
    (hd : ∀ r ∈ I, HasDerivAt f (D r) r) (hh : h ≠ 0)
    (hsegment : uIcc t (t + h) ⊆ I) :
    HasDerivAt (fun r ↦ ∫ s in (0 : ℝ)..1, f (r + h * s))
      (∫ s in (0 : ℝ)..1, D (t + h * s)) t := by
  rw [intervalIntegral.integral_comp_add_mul D hh, mul_zero, add_zero, mul_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr ↦ hd r (hsegment hr)) (hD.mono hsegment).intervalIntegrable]
  exact hasDerivAt_timeAverage hI
    (fun r hr ↦ (hd r hr).continuousAt.continuousWithinAt) hh hsegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [CompleteSpace F] [NormedSpace ℝ E] in
/-- Joint continuity passes to the time average on every open product on
which the entire averaging window stays inside the original domain. -/
theorem continuousOn_timeAverage
    {Ω : Set E} {I J : Set ℝ} {u : E × ℝ → F} {h : ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hJ : IsOpen J)
    (hu : ContinuousOn u (Ω ×ˢ I))
    (hwindow : ∀ t ∈ J, ∀ s ∈ Icc (0 : ℝ) 1, t + h * s ∈ I) :
    ContinuousOn (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, u (p.1, p.2 + h * s))
      (Ω ×ˢ J) := by
  have hshift : Continuous (fun q : (E × ℝ) × ℝ ↦ (q.1.1, q.1.2 + h * q.2)) :=
    continuous_fst.fst.prodMk (continuous_fst.snd.add (continuous_const.mul continuous_snd))
  intro p hp
  apply ContinuousAt.continuousWithinAt
  apply PDE.Calculus.continuousAt_intervalAverage_of_joint
    (fun q : (E × ℝ) × ℝ ↦ u (q.1.1, q.1.2 + h * q.2)) (hΩ.prod hJ) _ hp
  intro q hq s hs
  have hmem : (q.1, q.2 + h * s) ∈ Ω ×ˢ I := ⟨hq.1, hwindow q.2 hq.2 s hs⟩
  simpa only [Function.comp_def] using!
    (hu.continuousAt ((hΩ.prod hI).mem_nhds hmem)).comp
      (f := fun r : (E × ℝ) × ℝ ↦ (r.1.1, r.1.2 + h * r.2))
      (hshift.continuousAt (x := (q, s)))

omit [CompleteSpace F] in
/-- A continuous spatial derivative passes through a time average.
No time derivative of that spatial derivative is assumed. -/
theorem hasFDerivAt_timeAverage_space
    {Ω : Set E} {I : Set ℝ} {u : E × ℝ → F} {Dx : E × ℝ → E →L[ℝ] F}
    {x : E} {t h : ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hu : ContinuousOn u (Ω ×ˢ I)) (hDx : ContinuousOn Dx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u (y, p.2)) (Dx p) p.1)
    (hx : x ∈ Ω) (hwindow : ∀ s ∈ Icc (0 : ℝ) 1, t + h * s ∈ I) :
    HasFDerivAt (fun y ↦ ∫ s in (0 : ℝ)..1, u (y, t + h * s))
      (∫ s in (0 : ℝ)..1, Dx (x, t + h * s)) x := by
  have hshift : Continuous (fun q : E × ℝ ↦ (q.1, t + h * q.2)) :=
    continuous_fst.prodMk (continuous_const.add (continuous_const.mul continuous_snd))
  apply PDE.Calculus.hasFDerivAt_intervalAverage_of_joint
    (fun q : E × ℝ ↦ u (q.1, t + h * q.2))
    (fun q : E × ℝ ↦ Dx (q.1, t + h * q.2)) hΩ _ _ _ hx
  · intro y hy s hs
    exact (hu.continuousAt ((hΩ.prod hI).mem_nhds ⟨hy, hwindow s hs⟩)).comp
      hshift.continuousAt
  · intro y hy s hs
    exact (hDx.continuousAt ((hΩ.prod hI).mem_nhds ⟨hy, hwindow s hs⟩)).comp
      hshift.continuousAt
  · intro y hy s hs
    exact hd (y, t + h * s) ⟨hy, hwindow s hs⟩

end PDE.Analysis
