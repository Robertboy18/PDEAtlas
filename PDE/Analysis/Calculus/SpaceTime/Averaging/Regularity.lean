/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Averaging.Differentiation
public import PDE.Analysis.Calculus.PartialRegularity

/-!
# Joint regularity of time averages

Time averaging adds one time derivative without asking for one in the input.
Continuous spatial first derivatives therefore give joint C¹ regularity of
the average. For a jointly C¹ field with continuous second spatial derivatives,
the average is jointly C². This supplies the regularization of raw C²,¹ jets
without mixed or second time derivatives of the original field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped ContDiff Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous field with continuous spatial derivative has a jointly C¹
time average, even when the original field has no time derivative. -/
theorem contDiffOn_one_timeAverage
    {Ω : Set E} {I J : Set ℝ} {u : E × ℝ → F} {Dx : E × ℝ → E →L[ℝ] F}
    {h : ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I) (hJ : IsOpen J) (hh : 0 < h)
    (hu : ContinuousOn u (Ω ×ˢ I)) (hDx : ContinuousOn Dx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u (y, p.2)) (Dx p) p.1)
    (hsegment : ∀ t ∈ J, uIcc t (t + h) ⊆ I) :
    ContDiffOn ℝ 1
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, u (p.1, p.2 + h * s)) (Ω ×ˢ J) := by
  have hwindow (t : ℝ) (ht : t ∈ J) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      t + h * s ∈ I := by
    apply hsegment t ht
    rw [uIcc_of_le (le_add_of_nonneg_right hh.le)]
    exact ⟨le_add_of_nonneg_right (mul_nonneg hh.le hs.1),
      add_le_add le_rfl (mul_le_of_le_one_right hh.le hs.2)⟩
  have hsub : Ω ×ˢ J ⊆ Ω ×ˢ I :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 left_mem_uIcc⟩
  have hshift : MapsTo (fun p : E × ℝ ↦ (p.1, p.2 + h)) (Ω ×ˢ J) (Ω ×ˢ I) :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 right_mem_uIcc⟩
  have hdiff : ContinuousOn (fun p : E × ℝ ↦ h⁻¹ • (u (p.1, p.2 + h) - u p))
      (Ω ×ˢ J) :=
    ((hu.comp (continuous_fst.prodMk (continuous_snd.add_const h)).continuousOn hshift).sub
      (hu.mono hsub)).const_smul h⁻¹
  apply contDiffOn_one_of_partial_derivatives (hΩ.prod hJ)
    (D₁ := fun p ↦ ∫ s in (0 : ℝ)..1, Dx (p.1, p.2 + h * s))
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (h⁻¹ • (u (p.1, p.2 + h) - u p)))
  · exact continuousOn_timeAverage hΩ hI hJ hDx hwindow
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp_continuousOn hdiff
  · intro p hp
    exact hasFDerivAt_timeAverage_space hΩ hI hu hDx hd hp.1 (hwindow p.2 hp.2)
  · intro p hp
    have hslice : ContinuousOn (fun t ↦ u (p.1, t)) I :=
      hu.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht ↦ ⟨hp.1, ht⟩)
    exact (hasDerivAt_timeAverage hI hslice hh.ne' (hsegment p.2 hp.2)).hasFDerivAt

/-- Continuous second spatial derivatives and joint C¹ regularity suffice
for a jointly C² time average. The original field needs neither mixed
derivatives nor a second time derivative. -/
theorem contDiffOn_two_timeAverage
    {Ω : Set E} {I J : Set ℝ} {u : E × ℝ → F}
    {Dx : E × ℝ → E →L[ℝ] F} {Dxx : E × ℝ → E →L[ℝ] E →L[ℝ] F}
    {h : ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I) (hJ : IsOpen J) (hh : 0 < h)
    (hu : ContDiffOn ℝ 1 u (Ω ×ˢ I))
    (hDx : ContinuousOn Dx (Ω ×ˢ I)) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u (y, p.2)) (Dx p) p.1)
    (hdd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1)
    (hsegment : ∀ t ∈ J, uIcc t (t + h) ⊆ I) :
    ContDiffOn ℝ 2
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, u (p.1, p.2 + h * s)) (Ω ×ˢ J) := by
  have hwindow (t : ℝ) (ht : t ∈ J) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      t + h * s ∈ I := by
    apply hsegment t ht
    rw [uIcc_of_le (le_add_of_nonneg_right hh.le)]
    exact ⟨le_add_of_nonneg_right (mul_nonneg hh.le hs.1),
      add_le_add le_rfl (mul_le_of_le_one_right hh.le hs.2)⟩
  have hsub : Ω ×ˢ J ⊆ Ω ×ˢ I :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 left_mem_uIcc⟩
  have hshift : MapsTo (fun p : E × ℝ ↦ (p.1, p.2 + h)) (Ω ×ˢ J) (Ω ×ˢ I) :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 right_mem_uIcc⟩
  have hdiff : ContDiffOn ℝ 1
      (fun p : E × ℝ ↦ h⁻¹ • (u (p.1, p.2 + h) - u p)) (Ω ×ˢ J) :=
    ((hu.comp (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)) hshift).sub
      (hu.mono hsub)).const_smul h⁻¹
  apply contDiffOn_succ_of_partial_derivatives (m := 1) (hΩ.prod hJ)
    (D₁ := fun p ↦ ∫ s in (0 : ℝ)..1, Dx (p.1, p.2 + h * s))
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (h⁻¹ • (u (p.1, p.2 + h) - u p)))
  · exact contDiffOn_one_timeAverage hΩ hI hJ hh hDx hDxx hdd hsegment
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).contDiff.comp_contDiffOn hdiff
  · intro p hp
    exact hasFDerivAt_timeAverage_space hΩ hI hu.continuousOn hDx hd hp.1
      (hwindow p.2 hp.2)
  · intro p hp
    have hslice : ContinuousOn (fun t ↦ u (p.1, t)) I :=
      hu.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht ↦ ⟨hp.1, ht⟩)
    exact (hasDerivAt_timeAverage hI hslice hh.ne' (hsegment p.2 hp.2)).hasFDerivAt

end PDE.Analysis
