/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Averaging.Differentiation
public import PDE.Analysis.Calculus.PartialRegularity

/-!
# Joint regularity of time averages

Time averaging adds one time derivative: if the field is jointly `Cᵐ` with a continuous spatial
derivative whose time average is jointly `Cᵐ`, the average of the field is jointly `Cᵐ⁺¹`
(`contDiffOn_succ_timeAverage`). No time derivative of the field beyond order `m` is asked for,
and none at all when `m = 0`.
Continuous spatial first derivatives therefore give joint C¹ regularity of
the average (`contDiffOn_one_timeAverage`). For a jointly C¹ field with continuous second
spatial derivatives, the average is jointly C² (`contDiffOn_two_timeAverage`). This supplies the
regularization of raw C²,¹ jets without mixed or second time derivatives of the original field.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped ContDiff Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- If the window `[t, t + h]`, `h > 0`, lies in `I`, so does every time `t + h s` with
`0 ≤ s ≤ 1`. -/
private theorem add_mul_mem_of_uIcc_subset {I : Set ℝ} {t h : ℝ} (hh : 0 < h)
    (hsegment : uIcc t (t + h) ⊆ I) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : t + h * s ∈ I := by
  apply hsegment
  rw [uIcc_of_le (le_add_of_nonneg_right hh.le)]
  exact ⟨le_add_of_nonneg_right (mul_nonneg hh.le hs.1),
    add_le_add le_rfl (mul_le_of_le_one_right hh.le hs.2)⟩

/-- **One more order per step.** If `u` is jointly `Cᵐ` on `Ω × I` and has there the spatial
derivative `Dx`, which is continuous, and if the time average of `Dx` is jointly `Cᵐ` on `Ω × J`,
then the time average of `u` is jointly `Cᵐ⁺¹` on `Ω × J`. Its time derivative is the difference
quotient `h⁻¹ (u (x, t + h) - u (x, t))`, so no time derivative of `u` beyond the order `m` of
the hypothesis is used. -/
theorem contDiffOn_succ_timeAverage
    {Ω : Set E} {I J : Set ℝ} {u : E × ℝ → F} {Dx : E × ℝ → E →L[ℝ] F} {m : ℕ}
    {h : ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I) (hJ : IsOpen J) (hh : 0 < h)
    (hu : ContDiffOn ℝ m u (Ω ×ˢ I)) (hDx : ContinuousOn Dx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u (y, p.2)) (Dx p) p.1)
    (hDavg : ContDiffOn ℝ m
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, Dx (p.1, p.2 + h * s)) (Ω ×ˢ J))
    (hsegment : ∀ t ∈ J, uIcc t (t + h) ⊆ I) :
    ContDiffOn ℝ (m + 1 : ℕ)
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, u (p.1, p.2 + h * s)) (Ω ×ˢ J) := by
  have hsub : Ω ×ˢ J ⊆ Ω ×ˢ I :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 left_mem_uIcc⟩
  have hshift : MapsTo (fun p : E × ℝ ↦ (p.1, p.2 + h)) (Ω ×ˢ J) (Ω ×ˢ I) :=
    fun p hp ↦ ⟨hp.1, hsegment p.2 hp.2 right_mem_uIcc⟩
  have hdiff : ContDiffOn ℝ m
      (fun p : E × ℝ ↦ h⁻¹ • (u (p.1, p.2 + h) - u p)) (Ω ×ˢ J) :=
    ((hu.comp (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)) hshift).sub
      (hu.mono hsub)).const_smul h⁻¹
  apply contDiffOn_succ_of_partial_derivatives (m := m) (hΩ.prod hJ)
    (D₁ := fun p ↦ ∫ s in (0 : ℝ)..1, Dx (p.1, p.2 + h * s))
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (h⁻¹ • (u (p.1, p.2 + h) - u p)))
  · exact hDavg
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).contDiff.comp_contDiffOn hdiff
  · intro p hp
    exact hasFDerivAt_timeAverage_space hΩ hI hu.continuousOn hDx hd hp.1
      fun s hs ↦ add_mul_mem_of_uIcc_subset hh (hsegment p.2 hp.2) hs
  · intro p hp
    have hslice : ContinuousOn (fun t ↦ u (p.1, t)) I :=
      hu.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht ↦ ⟨hp.1, ht⟩)
    exact (hasDerivAt_timeAverage hI hslice hh.ne' (hsegment p.2 hp.2)).hasFDerivAt

/-- A continuous field with continuous spatial derivative has a jointly C¹
time average, even when the original field has no time derivative. This is
`contDiffOn_succ_timeAverage` at order zero. -/
theorem contDiffOn_one_timeAverage
    {Ω : Set E} {I J : Set ℝ} {u : E × ℝ → F} {Dx : E × ℝ → E →L[ℝ] F}
    {h : ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I) (hJ : IsOpen J) (hh : 0 < h)
    (hu : ContinuousOn u (Ω ×ˢ I)) (hDx : ContinuousOn Dx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u (y, p.2)) (Dx p) p.1)
    (hsegment : ∀ t ∈ J, uIcc t (t + h) ⊆ I) :
    ContDiffOn ℝ 1
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..1, u (p.1, p.2 + h * s)) (Ω ×ˢ J) := by
  exact_mod_cast contDiffOn_succ_timeAverage (m := 0) hΩ hI hJ hh (contDiffOn_zero.mpr hu) hDx
    hd (contDiffOn_zero.mpr (continuousOn_timeAverage hΩ hI hJ hDx
      fun t ht s hs ↦ add_mul_mem_of_uIcc_subset hh (hsegment t ht) hs)) hsegment

/-- Continuous second spatial derivatives and joint C¹ regularity suffice
for a jointly C² time average. The original field needs neither mixed
derivatives nor a second time derivative. This is `contDiffOn_succ_timeAverage` at order one,
with `contDiffOn_one_timeAverage` for the average of the spatial derivative. -/
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
  exact_mod_cast contDiffOn_succ_timeAverage (m := 1) hΩ hI hJ hh (by exact_mod_cast hu) hDx hd
    (by exact_mod_cast contDiffOn_one_timeAverage hΩ hI hJ hh hDx hDxx hdd hsegment) hsegment

end PDE.Analysis
