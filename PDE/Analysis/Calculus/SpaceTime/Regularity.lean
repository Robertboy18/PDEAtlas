/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PartialRegularity
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Unbundled spatial and temporal regularity

For a field on `Ω ×ˢ I`, continuous spatial derivatives and a continuous time
derivative within `I` give joint C¹ regularity on `Ω ×ˢ interior I`. A continuous
second spatial derivative gives C² regularity of every spatial slice.

The derivative data are ordinary continuous linear maps, identified by Mathlib's
`HasFDerivAt` and `HasDerivWithinAt` statements. Taking `I = Ici 0` permits a
one-sided derivative at the initial time. There is no mixed derivative or
second time derivative hypothesis. On `ℝ × I` with `I` convex, `C^n` partial derivatives, the time
derivative taken within `I`, give `C^{n+1}` regularity up to the endpoints of `I`
(`contDiffOn_succ_of_space_time_derivatives`). Joint continuity of the field on `Ω ×ˢ I`,
when needed at a temporal boundary, remains an ordinary `ContinuousOn` hypothesis.
-/

@[expose] public section

namespace PDE.Analysis

open Set
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous first spatial and time derivatives give joint C¹ regularity
away from the boundary of the time set. The time derivative is only required
within that set, including at an initial or terminal endpoint. -/
theorem contDiffOn_one_of_space_time_derivatives
    {Ω : Set E} {I : Set ℝ} {u : E → ℝ → F}
    {Dx : E × ℝ → E →L[ℝ] F} {Dt : E × ℝ → F}
    (hΩ : IsOpen Ω)
    (hDx : ContinuousOn Dx (Ω ×ˢ I)) (hDt : ContinuousOn Dt (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ I, HasDerivWithinAt (u p.1) (Dt p) I p.2) :
    ContDiffOn ℝ 1 (Function.uncurry u) (Ω ×ˢ interior I) := by
  have hsub : Ω ×ˢ interior I ⊆ Ω ×ˢ I := prod_mono Subset.rfl interior_subset
  apply contDiffOn_one_of_partial_derivatives (hΩ.prod isOpen_interior)
    (hDx.mono hsub)
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (Dt p))
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.continuousOn.comp
      (hDt.mono hsub) (mapsTo_univ _ _)
  · exact fun p hp ↦ hspace p (hsub hp)
  · intro p hp
    exact ((htime p (hsub hp)).hasDerivAt (mem_interior_iff_mem_nhds.mp hp.2)).hasFDerivAt

/-- A jointly continuous second spatial derivative gives C² spatial slices.
The time set is arbitrary: no time derivative, mixed derivative, extension
across a temporal endpoint, or completeness assumption is needed. -/
theorem contDiffOn_two_slice_of_space_derivatives
    {Ω : Set E} {I : Set ℝ} {u : E → ℝ → F}
    {Dx : E × ℝ → E →L[ℝ] F} {Dxx : E × ℝ → E →L[ℝ] E →L[ℝ] F}
    (hΩ : IsOpen Ω) (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hspace : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    {t : ℝ} (ht : t ∈ I) :
    ContDiffOn ℝ 2 (fun x ↦ u x t) Ω := by
  have hDxxSlice : ContinuousOn (fun x ↦ Dxx (x, t)) Ω :=
    hDxx.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx ↦ ⟨hx, ht⟩)
  have hDxSlice : ContDiffOn ℝ 1 (fun x ↦ Dx (x, t)) Ω := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn]
    exact ⟨by simp, (fun x ↦ Dxx (x, t)), contDiffOn_zero.mpr hDxxSlice,
      fun x hx ↦ (hhessian (x, t) ⟨hx, ht⟩).hasFDerivWithinAt⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn]
  exact ⟨by simp, (fun x ↦ Dx (x, t)), hDxSlice,
    fun x hx ↦ (hspace (x, t) ⟨hx, ht⟩).hasFDerivWithinAt⟩

open Filter Asymptotics in
/-- A function on `ℝ × I` with `C^n` partial derivatives, the time derivative taken within the
convex set `I`, is `C^{n+1}` on `ℝ × I`. -/
theorem contDiffOn_succ_of_space_time_derivatives {f : ℝ × ℝ → ℝ} {dx dt : ℝ × ℝ → ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (hIu : UniqueDiffOn ℝ I) {n : ℕ}
    (hdx : ContDiffOn ℝ n dx (univ ×ˢ I)) (hdt' : ContDiffOn ℝ n dt (univ ×ˢ I))
    (hx : ∀ z ∈ univ ×ˢ I, HasDerivAt (fun y ↦ f (y, z.2)) (dx z) z.1)
    (ht : ∀ z ∈ univ ×ˢ I, HasDerivWithinAt (fun s ↦ f (z.1, s)) (dt z) I z.2) :
    ContDiffOn ℝ (n + 1) f (univ ×ˢ I) := by
  have hdt : ContinuousOn dt (univ ×ˢ I) := hdt'.continuousOn
  set S : Set (ℝ × ℝ) := univ ×ˢ I with hS
  let D : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z ↦
    dx z • ContinuousLinearMap.fst ℝ ℝ ℝ + dt z • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hD : ContDiffOn ℝ n D S :=
    (hdx.smul contDiffOn_const).add (hdt'.smul contDiffOn_const)
  have hU : UniqueDiffOn ℝ S := uniqueDiffOn_univ.prod hIu
  let R : ℝ → ℝ →L[ℝ] ℝ := fun c ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c
  have hR : Continuous R :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous
  have hderiv : ∀ z ∈ S, HasFDerivWithinAt f (D z) S z := by
    intro z hz
    rw [hasFDerivWithinAt_iff_isLittleO]
    have hfst : Tendsto (fun w : ℝ × ℝ ↦ w.1) (𝓝[S] z) (𝓝 z.1) :=
      (continuous_fst.tendsto z).mono_left nhdsWithin_le_nhds
    have hsnd : Tendsto (fun w : ℝ × ℝ ↦ w.2) (𝓝[S] z) (𝓝 z.2) :=
      (continuous_snd.tendsto z).mono_left nhdsWithin_le_nhds
    have htime : (fun w : ℝ × ℝ ↦ f (w.1, w.2) - f (w.1, z.2) - R (dt z) (w.2 - z.2))
        =o[𝓝[S] z] (fun w : ℝ × ℝ ↦ w.2 - z.2) := by
      rw [isLittleO_iff]
      intro ε hε
      obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hdt z hz) ε hε
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ)] with w hw hwball
      have hseg : uIcc z.2 w.2 ⊆ I :=
        hI.ordConnected.uIcc_subset hz.2 hw.2
      have hderivSeg : ∀ s ∈ uIcc z.2 w.2,
          HasDerivWithinAt (fun r ↦ f (w.1, r) - dt z * r) (dt (w.1, s) - dt z)
            (uIcc z.2 w.2) s := by
        intro s hs
        have h := (ht (w.1, s) ⟨mem_univ _, hseg hs⟩).mono hseg
        have h2 : HasDerivWithinAt (fun r : ℝ ↦ dt z * r) (dt z) (uIcc z.2 w.2) s := by
          have h3 := ((hasDerivAt_id' s).const_mul (dt z)).hasDerivWithinAt (s := uIcc z.2 w.2)
          rwa [mul_one] at h3
        exact h.sub h2
      have hbound : ∀ s ∈ uIcc z.2 w.2, ‖dt (w.1, s) - dt z‖ ≤ ε := by
        intro s hs
        have hmem : ((w.1, s) : ℝ × ℝ) ∈ S := ⟨mem_univ _, hseg hs⟩
        have hdist : dist ((w.1, s) : ℝ × ℝ) z < δ := by
          have hw' : dist w z < δ := hwball
          rw [Prod.dist_eq] at hw' ⊢
          have hs' : dist s z.2 ≤ dist w.2 z.2 := by
            rw [Real.dist_eq, Real.dist_eq]
            rcases le_total z.2 w.2 with h | h
            · rw [uIcc_of_le h] at hs
              rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]
              linarith [hs.2]
            · rw [uIcc_of_ge h] at hs
              rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]
              linarith [hs.1]
          exact lt_of_le_of_lt (max_le_max le_rfl hs') hw'
        exact (hclose hmem hdist).le
      have hmv := (convex_uIcc z.2 w.2).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderivSeg hbound left_mem_uIcc right_mem_uIcc
      calc ‖f (w.1, w.2) - f (w.1, z.2) - R (dt z) (w.2 - z.2)‖
          = ‖(f (w.1, w.2) - dt z * w.2) - (f (w.1, z.2) - dt z * z.2)‖ := by
            congr 1
            simp [R]
            ring
        _ ≤ ε * ‖w.2 - z.2‖ := hmv
    have hspace : (fun w : ℝ × ℝ ↦ f (w.1, z.2) - f z - (w.1 - z.1) • dx z)
        =o[𝓝[S] z] (fun w : ℝ × ℝ ↦ w.1 - z.1) := by
      have h := (hasDerivAt_iff_isLittleO.mp (hx z hz)).comp_tendsto hfst
      simpa only [Function.comp_def, Prod.mk.eta] using h
    have hbig1 : (fun w : ℝ × ℝ ↦ w.2 - z.2) =O[𝓝[S] z] (fun w : ℝ × ℝ ↦ w - z) :=
      isBigO_of_le _ fun w ↦ by
        simpa only [Prod.snd_sub] using norm_snd_le (w - z)
    have hbig2 : (fun w : ℝ × ℝ ↦ w.1 - z.1) =O[𝓝[S] z] (fun w : ℝ × ℝ ↦ w - z) :=
      isBigO_of_le _ fun w ↦ by
        simpa only [Prod.fst_sub] using norm_fst_le (w - z)
    refine ((htime.trans_isBigO hbig1).add (hspace.trans_isBigO hbig2)).congr_left ?_
    intro w
    simp [D, R]
    ring
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU]
  exact ⟨by simp, D, hD, hderiv⟩

end PDE.Analysis
