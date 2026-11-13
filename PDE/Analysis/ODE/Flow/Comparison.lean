/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Estimates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Comparison of the flows of two fields

Let `v` and `v'` be two fields whose flows keep a convex set `S`, with `‖Dv‖ ≤ K₁` on `S`. If
`‖v - v'‖ ≤ ε₀(r)` on `S` at time `r`, the flow lines through the same point differ after the
time span `s - t` by at most `exp (K₁ (s - t)) ∫ₜˢ ε₀`. If moreover `Dv` has a modulus of
continuity `ψ` on `S`, `‖Dv - Dv'‖ ≤ ε₁(r)` on `S` and `‖Dv'‖ ≤ K₁'` on `S`, the first variations
differ by at most `exp ((K₁ + K₁') (s - t)) ∫ₜˢ (ψ (D r) + ε₁ r)`, where `D` is any monotone
majorant of the distance of the two flow lines. The forcing enters through its integral, not
its supremum, which is the form needed by Osgood's lemma. Backward versions hold for `s ≤ t`.

The integral form of Grönwall's inequality behind these bounds,
`le_exp_mul_integral_of_le_integral`, only asks for an integrable nonnegative forcing; it is
applied to monotone forcings, which are interval integrable.

## Main results

* `le_exp_mul_integral_of_le_integral`, `le_exp_mul_integral_of_le_integral_left`: Grönwall's
  inequality `g s ≤ ∫ (K g + ε) ⇒ g s ≤ exp (K |s - t|) ∫ ε`, forward and backward.
* `IsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant`,
  `IsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant_left`: comparison of flow lines.
* `IsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant`,
  `IsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant_left`: comparison of first
  variations.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped NNReal Topology

namespace PDE.Analysis.ODE

/-! ### Grönwall's inequality with an integrable forcing -/

/-- **Grönwall's inequality in integral form.** If `g` is continuous on `[t, T]`, `0 ≤ K`, the
forcing `ε ≥ 0` is integrable on `[t, T]`, and `g s ≤ ∫ₜˢ (K g + ε)` for `s ∈ [t, T]`, then
`g s ≤ exp (K (s - t)) ∫ₜˢ ε` for `s ∈ [t, T]`. -/
theorem le_exp_mul_integral_of_le_integral {g ε : ℝ → ℝ} {t T K : ℝ} (hK : 0 ≤ K)
    (hg : ContinuousOn g (Icc t T)) (hε : IntervalIntegrable ε volume t T)
    (hε₀ : ∀ r ∈ Icc t T, 0 ≤ ε r)
    (hle : ∀ s ∈ Icc t T, g s ≤ ∫ r in t..s, (K * g r + ε r)) :
    ∀ s ∈ Icc t T, g s ≤ Real.exp (K * (s - t)) * ∫ r in t..s, ε r := by
  intro s₀ hs₀
  have htT : t ≤ T := hs₀.1.trans hs₀.2
  set ĝ : ℝ → ℝ := fun r ↦ g (projIcc t T htT r) with hĝdef
  have hĝ : Continuous ĝ :=
    hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r ↦ (projIcc t T htT r).2
  have hĝg {r : ℝ} (hr : r ∈ Icc t T) : ĝ r = g r := by
    simp only [hĝdef, projIcc_of_mem htT hr]
  set G : ℝ → ℝ := fun x ↦ ∫ r in t..x, ĝ r with hGdef
  have hG (x : ℝ) : HasDerivAt G (ĝ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hĝ.intervalIntegrable _ _)
      (hĝ.stronglyMeasurableAtFilter _ _) hĝ.continuousAt
  have hεsub {x : ℝ} (hx : x ∈ Icc t T) : IntervalIntegrable ε volume t x :=
    hε.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le htT]; exact hx))
  set E₀ := ∫ r in t..s₀, ε r with hE₀def
  have hint {x : ℝ} (hx : x ∈ Icc t T) :
      ∫ r in t..x, (K * g r + ε r) = K * G x + ∫ r in t..x, ε r := by
    have hcongr : ∫ r in t..x, (K * g r + ε r) = ∫ r in t..x, (K * ĝ r + ε r) := by
      refine intervalIntegral.integral_congr fun r hr ↦ ?_
      have hr' : r ∈ Icc t T := by
        rw [uIcc_of_le hx.1] at hr
        exact ⟨hr.1, hr.2.trans hx.2⟩
      simp only [hĝg hr']
    rw [hcongr, intervalIntegral.integral_add ((hĝ.intervalIntegrable _ _).const_mul K)
      (hεsub hx), intervalIntegral.integral_const_mul]
  have hEle {x : ℝ} (hx : x ∈ Icc t s₀) : ∫ r in t..x, ε r ≤ E₀ := by
    have hxT : x ∈ Icc t T := ⟨hx.1, hx.2.trans hs₀.2⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hεsub hxT)
      ((hεsub hs₀).mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hs₀.1]; exact hx)
        right_mem_uIcc))
    have hnonneg : 0 ≤ ∫ r in x..s₀, ε r :=
      intervalIntegral.integral_nonneg hx.2 fun r hr ↦ hε₀ r ⟨hx.1.trans hr.1, hr.2.trans hs₀.2⟩
    rw [hE₀def, ← hadd]
    linarith
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := ĝ) (δ := 0) (K := K)
    (ε := E₀) (a := t) (b := s₀) (fun x _ ↦ (hG x).continuousAt.continuousWithinAt)
    (fun x _ r hr ↦ by
      simpa only [slope_def_field, div_eq_inv_mul] using
        (hG x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hGdef])
    (fun x hx ↦ by
      have hxT : x ∈ Icc t T := ⟨hx.1, hx.2.le.trans hs₀.2⟩
      rw [hĝg hxT]
      have h := hle x hxT
      rw [hint hxT] at h
      linarith [hEle ⟨hx.1, hx.2.le⟩]) s₀ ⟨hs₀.1, le_rfl⟩
  have h := hle s₀ hs₀
  rw [hint hs₀] at h
  have hK' : K * G s₀ ≤ K * gronwallBound 0 K E₀ (s₀ - t) := mul_le_mul_of_nonneg_left hgron hK
  have hid : K * gronwallBound 0 K E₀ (s₀ - t) + E₀ = Real.exp (K * (s₀ - t)) * E₀ := by
    by_cases hK0 : K = 0
    · subst hK0
      simp [gronwallBound_K0]
    · rw [gronwallBound_of_K_ne_0 hK0]
      field_simp
      ring
  linarith

/-- **Grönwall's inequality in integral form, backward in time.** If `g` is continuous on
`[T, t]`, `0 ≤ K`, the forcing `ε ≥ 0` is integrable on `[T, t]`, and `g s ≤ ∫ₛᵗ (K g + ε)` for
`s ∈ [T, t]`, then `g s ≤ exp (K (t - s)) ∫ₛᵗ ε` for `s ∈ [T, t]`. -/
theorem le_exp_mul_integral_of_le_integral_left {g ε : ℝ → ℝ} {T t K : ℝ} (hK : 0 ≤ K)
    (hg : ContinuousOn g (Icc T t)) (hε : IntervalIntegrable ε volume T t)
    (hε₀ : ∀ r ∈ Icc T t, 0 ≤ ε r)
    (hle : ∀ s ∈ Icc T t, g s ≤ ∫ r in s..t, (K * g r + ε r)) :
    ∀ s ∈ Icc T t, g s ≤ Real.exp (K * (t - s)) * ∫ r in s..t, ε r := by
  have hneg {q : ℝ} (hq : q ∈ Icc (-t) (-T)) : -q ∈ Icc T t :=
    ⟨le_neg.mp hq.2, neg_le.mp hq.1⟩
  have hcomp (f : ℝ → ℝ) (q : ℝ) : ∫ r in -t..q, f (-r) = ∫ r in -q..t, f r := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  intro s hs
  have h := le_exp_mul_integral_of_le_integral (g := fun q ↦ g (-q)) (ε := fun q ↦ ε (-q))
    (t := -t) (T := -T) hK
    (hg.comp continuous_neg.continuousOn fun q hq ↦ hneg hq)
    ((IntervalIntegrable.iff_comp_neg (by simp)).mp hε).symm
    (fun q hq ↦ hε₀ (-q) (hneg hq))
    (fun q hq ↦ by
      have h := hle (-q) (hneg hq)
      rw [← hcomp (fun r ↦ K * g r + ε r) q] at h
      simpa using h) (-s) ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩
  rw [hcomp ε (-s), neg_neg, show -s - -t = t - s by ring] at h
  simpa using h

/-! ### Comparison of two flows -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v v' : ℝ → E → E} {Dv Dv' : ℝ → E → E →L[ℝ] E} {a b : ℝ} {K₀ K₀' : ℝ≥0} {S : Set E}
  {K₁ K₁' : ℝ}

omit [FiniteDimensional ℝ E] in
/-- On a convex set where `‖Dv‖ ≤ K₁`, the field is `K₁`-Lipschitz. -/
theorem IsC1FieldOn.norm_sub_le_of_convex (hv : IsC1FieldOn v Dv a b K₀) (hSc : Convex ℝ S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {r : ℝ} (hr : r ∈ Icc a b) {y z : E}
    (hy : y ∈ S) (hz : z ∈ S) : ‖v r y - v r z‖ ≤ K₁ * ‖y - z‖ :=
  hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := v r) (f' := Dv r)
    (fun q _ ↦ (hv.hasFDerivAt r hr q).hasFDerivWithinAt) (fun q hq ↦ hDv r hr q hq) hz hy

/-- The integral form of a derivative bound: if `e` has derivative `e'` at every time of
`[a, b]`, `e'` is continuous there, and `‖e' r‖ ≤ h r` between `t` and `s` with `h` integrable,
then `‖e s - e t‖ ≤ ∫ₜˢ h` for `t ≤ s` and `≤ ∫ₛᵗ h` for `s ≤ t`. -/
theorem norm_sub_le_integral_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {e e' : ℝ → F} {h : ℝ → ℝ} {t s : ℝ} (hts : t ≤ s)
    (he : ∀ r ∈ Icc t s, HasDerivAt e (e' r) r) (he' : ContinuousOn e' (Icc t s))
    (hh : IntervalIntegrable h volume t s) (hbound : ∀ r ∈ Icc t s, ‖e' r‖ ≤ h r) :
    ‖e s - e t‖ ≤ ∫ r in t..s, h r := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr ↦ he r (by
    rwa [uIcc_of_le hts] at hr)) ((he'.mono (by rw [uIcc_of_le hts])).intervalIntegrable)]
  exact intervalIntegral.norm_integral_le_of_norm_le hts
    (Eventually.of_forall fun r hr ↦ hbound r (Ioc_subset_Icc_self hr)) hh

namespace IsC1FieldOn

/-- The velocity along a flow line is continuous in time. -/
theorem continuousOn_comp_flowOn (hv : IsC1FieldOn v Dv a b K₀) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : ContinuousOn (fun r ↦ v r (flowOn v a b r t x)) (Icc a b) :=
  hv.continuousOn.comp (continuousOn_id.prodMk
    (hv.isLipschitzFieldOn.continuousOn_flowOn_time ht x)) fun _ hr ↦ ⟨hr, mem_univ _⟩

/-- **Comparison of flow lines, forward.** If both flows keep the convex set `S`, `‖Dv‖ ≤ K₁`
on `S` and `‖v r y - v' r y‖ ≤ ε₀ r` on `S` for `r ∈ [t, b]` with `ε₀ ≥ 0` monotone, then for
`s ∈ [t, b]` the flow lines through `x ∈ S` at time `t` satisfy
`‖Φ s - Φ' s‖ ≤ exp (K₁ (s - t)) ∫ₜˢ ε₀`. -/
theorem norm_flowOn_sub_flowOn_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hv' : IsC1FieldOn v' Dv' a b K₀') (hSc : Convex ℝ S)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hS' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {t : ℝ} (ht : t ∈ Icc a b) {ε₀ : ℝ → ℝ}
    (hε₀ : MonotoneOn ε₀ (Icc t b)) (hε₀₀ : ∀ r ∈ Icc t b, 0 ≤ ε₀ r)
    (hvv' : ∀ r ∈ Icc t b, ∀ y ∈ S, ‖v r y - v' r y‖ ≤ ε₀ r) {x : E} (hx : x ∈ S) {s : ℝ}
    (hs : s ∈ Icc t b) :
    ‖flowOn v a b s t x - flowOn v' a b s t x‖ ≤ Real.exp (K₁ * (s - t)) * ∫ r in t..s, ε₀ r := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
  have hε₀i : IntervalIntegrable ε₀ volume t b :=
    MonotoneOn.intervalIntegrable (by rwa [uIcc_of_le ht.2])
  set g : ℝ → ℝ := fun r ↦ ‖flowOn v a b r t x - flowOn v' a b r t x‖ with hgdef
  have hg : ContinuousOn g (Icc t b) :=
    ((hL.continuousOn_flowOn_time ht x).sub (hL'.continuousOn_flowOn_time ht x)).norm.mono hsub
  refine le_exp_mul_integral_of_le_integral hK₁ hg hε₀i hε₀₀ (fun q hq ↦ ?_) s hs
  have hsub' : Icc t q ⊆ Icc a b := (Icc_subset_Icc_right hq.2).trans hsub
  have hint : IntervalIntegrable (fun r ↦ K₁ * g r + ε₀ r) volume t q :=
    ((hg.mono (Icc_subset_Icc_right hq.2)).intervalIntegrable_of_Icc hq.1 |>.const_mul K₁).add
      (hε₀i.mono_set (by rw [uIcc_of_le hq.1, uIcc_of_le ht.2]; exact Icc_subset_Icc_right hq.2))
  have h := norm_sub_le_integral_of_hasDerivAt (e := fun r ↦ flowOn v a b r t x -
      flowOn v' a b r t x) (e' := fun r ↦ v r (flowOn v a b r t x) - v' r (flowOn v' a b r t x))
    (h := fun r ↦ K₁ * g r + ε₀ r) hq.1
    (fun r hr ↦ (hL.hasDerivAt_flowOn (hsub' hr) ht x).sub (hL'.hasDerivAt_flowOn (hsub' hr) ht x))
    (((hv.continuousOn_comp_flowOn ht x).sub (hv'.continuousOn_comp_flowOn ht x)).mono hsub') hint
    (fun r hr ↦ by
      have hr' := hsub' hr
      have hΦ := hS r hr' t ht hx
      have hΦ' := hS' r hr' t ht hx
      calc ‖v r (flowOn v a b r t x) - v' r (flowOn v' a b r t x)‖
          ≤ ‖v r (flowOn v a b r t x) - v r (flowOn v' a b r t x)‖ +
            ‖v r (flowOn v' a b r t x) - v' r (flowOn v' a b r t x)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K₁ * g r + ε₀ r := add_le_add (hv.norm_sub_le_of_convex hSc hDv hr' hΦ hΦ')
            (hvv' r ⟨hr.1, hr.2.trans hq.2⟩ _ hΦ'))
  simpa [hgdef, hL.flowOn_self ht, hL'.flowOn_self ht] using h

/-- **Comparison of flow lines, backward.** Under the hypotheses of
`norm_flowOn_sub_flowOn_le_of_invariant` on `[a, t]` with `ε₀ ≥ 0` antitone there, for
`s ∈ [a, t]`, `‖Φ s - Φ' s‖ ≤ exp (K₁ (t - s)) ∫ₛᵗ ε₀`. -/
theorem norm_flowOn_sub_flowOn_le_of_invariant_left (hv : IsC1FieldOn v Dv a b K₀)
    (hv' : IsC1FieldOn v' Dv' a b K₀') (hSc : Convex ℝ S)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hS' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {t : ℝ} (ht : t ∈ Icc a b) {ε₀ : ℝ → ℝ}
    (hε₀ : AntitoneOn ε₀ (Icc a t)) (hε₀₀ : ∀ r ∈ Icc a t, 0 ≤ ε₀ r)
    (hvv' : ∀ r ∈ Icc a t, ∀ y ∈ S, ‖v r y - v' r y‖ ≤ ε₀ r) {x : E} (hx : x ∈ S) {s : ℝ}
    (hs : s ∈ Icc a t) :
    ‖flowOn v a b s t x - flowOn v' a b s t x‖ ≤ Real.exp (K₁ * (t - s)) * ∫ r in s..t, ε₀ r := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hε₀i : IntervalIntegrable ε₀ volume a t :=
    AntitoneOn.intervalIntegrable (by rwa [uIcc_of_le ht.1])
  set g : ℝ → ℝ := fun r ↦ ‖flowOn v a b r t x - flowOn v' a b r t x‖ with hgdef
  have hg : ContinuousOn g (Icc a t) :=
    ((hL.continuousOn_flowOn_time ht x).sub (hL'.continuousOn_flowOn_time ht x)).norm.mono hsub
  refine le_exp_mul_integral_of_le_integral_left hK₁ hg hε₀i hε₀₀ (fun q hq ↦ ?_) s hs
  have hsub' : Icc q t ⊆ Icc a b := (Icc_subset_Icc_left hq.1).trans hsub
  have hint : IntervalIntegrable (fun r ↦ K₁ * g r + ε₀ r) volume q t :=
    ((hg.mono (Icc_subset_Icc_left hq.1)).intervalIntegrable_of_Icc hq.2 |>.const_mul K₁).add
      (hε₀i.mono_set (by rw [uIcc_of_le hq.2, uIcc_of_le ht.1]; exact Icc_subset_Icc_left hq.1))
  have h := norm_sub_le_integral_of_hasDerivAt (e := fun r ↦ flowOn v a b r t x -
      flowOn v' a b r t x) (e' := fun r ↦ v r (flowOn v a b r t x) - v' r (flowOn v' a b r t x))
    (h := fun r ↦ K₁ * g r + ε₀ r) hq.2
    (fun r hr ↦ (hL.hasDerivAt_flowOn (hsub' hr) ht x).sub (hL'.hasDerivAt_flowOn (hsub' hr) ht x))
    (((hv.continuousOn_comp_flowOn ht x).sub (hv'.continuousOn_comp_flowOn ht x)).mono hsub') hint
    (fun r hr ↦ by
      have hr' := hsub' hr
      have hΦ := hS r hr' t ht hx
      have hΦ' := hS' r hr' t ht hx
      calc ‖v r (flowOn v a b r t x) - v' r (flowOn v' a b r t x)‖
          ≤ ‖v r (flowOn v a b r t x) - v r (flowOn v' a b r t x)‖ +
            ‖v r (flowOn v' a b r t x) - v' r (flowOn v' a b r t x)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K₁ * g r + ε₀ r := add_le_add (hv.norm_sub_le_of_convex hSc hDv hr' hΦ hΦ')
            (hvv' r ⟨hq.1.trans hr.1, hr.2⟩ _ hΦ'))
  rw [norm_sub_rev] at h
  simpa [hgdef, hL.flowOn_self ht, hL'.flowOn_self ht] using h

/-- The first variation along a flow line is continuous in time, together with its
derivative `Dv(r, Φ) ∘ J`. -/
theorem continuousOn_variationOn_deriv (hv : IsC1FieldOn v Dv a b K₀) {t : ℝ}
    (ht : t ∈ Icc a b) (x : E) :
    ContinuousOn (fun r ↦ (Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x))
      (Icc a b) :=
  (hv.continuousOn_deriv_flowOn ht x).clm_comp (hv.continuousOn_variationOn_time ht x)

/-- The pointwise bound behind the comparison of first variations. -/
private theorem norm_deriv_comp_sub_le (hv : IsC1FieldOn v Dv a b K₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hS' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hDv' : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv' r y‖ ≤ K₁')
    {ψ : ℝ → ℝ} (hψ : MonotoneOn ψ (Ici 0))
    (hDvψ : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ‖Dv r y - Dv r z‖ ≤ ψ ‖y - z‖)
    {t : ℝ} (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) {r : ℝ} (hr : r ∈ Icc a b) {e₁ d L : ℝ}
    (hDvv' : ‖Dv r (flowOn v' a b r t x) - Dv' r (flowOn v' a b r t x)‖ ≤ e₁)
    (hd : ‖flowOn v a b r t x - flowOn v' a b r t x‖ ≤ d) (hJ : Real.exp (K₁ * |r - t|) ≤ L) :
    ‖(Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x) -
        (Dv' r (flowOn v' a b r t x)).comp (variationOn v' Dv' a b r t x)‖ ≤
      K₁' * ‖variationOn v Dv a b r t x - variationOn v' Dv' a b r t x‖ +
        L * (ψ d + e₁) := by
  have hΦ := hS r hr t ht hx
  have hΦ' := hS' r hr t ht hx
  set J := variationOn v Dv a b r t x
  set J' := variationOn v' Dv' a b r t x
  set A := Dv r (flowOn v a b r t x)
  set A' := Dv' r (flowOn v' a b r t x)
  have hsplit : A.comp J - A'.comp J' = A'.comp (J - J') + (A - A').comp J := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  have hAA' : ‖A - A'‖ ≤ ψ d + e₁ := by
    calc ‖A - A'‖ ≤ ‖A - Dv r (flowOn v' a b r t x)‖ + ‖Dv r (flowOn v' a b r t x) - A'‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ψ d + e₁ := add_le_add ((hDvψ r hr _ hΦ _ hΦ').trans
          (hψ (norm_nonneg _) ((norm_nonneg _).trans hd) hd)) hDvv'
  have hJL : ‖J‖ ≤ L := (hv.norm_variationOn_le_of_invariant hS hDv hr ht hx).trans hJ
  have he₁ : 0 ≤ ψ d + e₁ := (norm_nonneg _).trans hAA'
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (A'.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right (hDv' r hr _ hΦ')
      (norm_nonneg _))
  · calc ‖(A - A').comp J‖ ≤ ‖A - A'‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (ψ d + e₁) * L := mul_le_mul hAA' hJL (norm_nonneg _) he₁
      _ = L * (ψ d + e₁) := mul_comm _ _

/-- **Comparison of first variations, forward.** Let both flows keep `S`, `‖Dv‖ ≤ K₁` and
`‖Dv'‖ ≤ K₁'` on `S`, `‖Dv r y - Dv r z‖ ≤ ψ ‖y - z‖` on `S` with `ψ` monotone and nonnegative on
`[0, ∞)`, and `‖Dv r y - Dv' r y‖ ≤ ε₁ r` on `S` for `r ∈ [t, b]` with `ε₁ ≥ 0` monotone. If `D`
is a monotone majorant of the distance of the flow lines through `x ∈ S` at time `t`, then for
`s ∈ [t, b]`, `‖J s - J' s‖ ≤ exp ((K₁ + K₁') (s - t)) ∫ₜˢ (ψ (D r) + ε₁ r)`. -/
theorem norm_variationOn_sub_variationOn_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hv' : IsC1FieldOn v' Dv' a b K₀')
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hS' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hDv' : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv' r y‖ ≤ K₁')
    {ψ : ℝ → ℝ} (hψ : MonotoneOn ψ (Ici 0)) (hψ₀ : ∀ q, 0 ≤ q → 0 ≤ ψ q)
    (hDvψ : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ‖Dv r y - Dv r z‖ ≤ ψ ‖y - z‖)
    {t : ℝ} (ht : t ∈ Icc a b) {ε₁ : ℝ → ℝ} (hε₁ : MonotoneOn ε₁ (Icc t b))
    (hε₁₀ : ∀ r ∈ Icc t b, 0 ≤ ε₁ r) (hDvv' : ∀ r ∈ Icc t b, ∀ y ∈ S, ‖Dv r y - Dv' r y‖ ≤ ε₁ r)
    {x : E} (hx : x ∈ S) {D : ℝ → ℝ} (hD : MonotoneOn D (Icc t b))
    (hDflow : ∀ r ∈ Icc t b, ‖flowOn v a b r t x - flowOn v' a b r t x‖ ≤ D r) {s : ℝ}
    (hs : s ∈ Icc t b) :
    ‖variationOn v Dv a b s t x - variationOn v' Dv' a b s t x‖ ≤
      Real.exp ((K₁ + K₁') * (s - t)) * ∫ r in t..s, (ψ (D r) + ε₁ r) := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hK₁' : 0 ≤ K₁' := (norm_nonneg _).trans (hDv' t ht x hx)
  have hsub : Icc t s ⊆ Icc a b := (Icc_subset_Icc_right hs.2).trans (Icc_subset_Icc_left ht.1)
  have hsubb : Icc t s ⊆ Icc t b := Icc_subset_Icc_right hs.2
  set L := Real.exp (K₁ * (s - t)) with hLdef
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have hD₀ : ∀ r ∈ Icc t b, 0 ≤ D r := fun r hr ↦ (norm_nonneg _).trans (hDflow r hr)
  have hmono : MonotoneOn (fun r ↦ ψ (D r) + ε₁ r) (Icc t b) := by
    intro r hr r' hr' hrr'
    exact add_le_add (hψ (hD₀ r hr) (hD₀ r' hr') (hD hr hr' hrr')) (hε₁ hr hr' hrr')
  set ε : ℝ → ℝ := fun r ↦ L * (ψ (D r) + ε₁ r) with hεdef
  have hεmono : MonotoneOn ε (Icc t s) := fun r hr r' hr' hrr' ↦
    mul_le_mul_of_nonneg_left (hmono (hsubb hr) (hsubb hr') hrr') hL
  have hεi : IntervalIntegrable ε volume t s :=
    MonotoneOn.intervalIntegrable (by rwa [uIcc_of_le hs.1])
  have hε₀ : ∀ r ∈ Icc t s, 0 ≤ ε r := fun r hr ↦
    mul_nonneg hL (add_nonneg (hψ₀ _ (hD₀ r (hsubb hr))) (hε₁₀ r (hsubb hr)))
  set g : ℝ → ℝ := fun r ↦ ‖variationOn v Dv a b r t x - variationOn v' Dv' a b r t x‖
    with hgdef
  have hg : ContinuousOn g (Icc t s) :=
    ((hv.continuousOn_variationOn_time ht x).sub
      (hv'.continuousOn_variationOn_time ht x)).norm.mono hsub
  have hmain := le_exp_mul_integral_of_le_integral hK₁' hg hεi hε₀ (fun q hq ↦ by
    have hsub' : Icc t q ⊆ Icc a b := (Icc_subset_Icc_right hq.2).trans hsub
    have hint : IntervalIntegrable (fun r ↦ K₁' * g r + ε r) volume t q :=
      ((hg.mono (Icc_subset_Icc_right hq.2)).intervalIntegrable_of_Icc hq.1 |>.const_mul K₁').add
        (hεi.mono_set (by rw [uIcc_of_le hq.1, uIcc_of_le hs.1]; exact Icc_subset_Icc_right hq.2))
    have h := norm_sub_le_integral_of_hasDerivAt
      (e := fun r ↦ variationOn v Dv a b r t x - variationOn v' Dv' a b r t x)
      (e' := fun r ↦ (Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x) -
        (Dv' r (flowOn v' a b r t x)).comp (variationOn v' Dv' a b r t x))
      (h := fun r ↦ K₁' * g r + ε r) hq.1
      (fun r hr ↦ (hv.hasDerivAt_variationOn (hsub' hr) ht x).sub
        (hv'.hasDerivAt_variationOn (hsub' hr) ht x))
      (((hv.continuousOn_variationOn_deriv ht x).sub
        (hv'.continuousOn_variationOn_deriv ht x)).mono hsub') hint
      (fun r hr ↦ by
        have hrs : r ∈ Icc t s := ⟨hr.1, hr.2.trans hq.2⟩
        have hJ : Real.exp (K₁ * |r - t|) ≤ L := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK₁)
          rw [abs_of_nonneg (by linarith [hr.1])]
          linarith [hrs.2]
        exact norm_deriv_comp_sub_le hv hS hS' hDv hDv' hψ hDvψ ht hx (hsub' hr)
          (hDvv' r (hsubb hrs) _ (hS' r (hsub' hr) t ht hx)) (hDflow r (hsubb hrs)) hJ)
    simpa [hgdef, hv.variationOn_self ht, hv'.variationOn_self ht] using h) s ⟨hs.1, le_rfl⟩
  refine hmain.trans_eq ?_
  rw [hεdef, intervalIntegral.integral_const_mul, hLdef, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Comparison of first variations, backward.** Under the hypotheses of
`norm_variationOn_sub_variationOn_le_of_invariant` on `[a, t]`, with `ε₁ ≥ 0` and the majorant
`D` antitone there, for `s ∈ [a, t]`,
`‖J s - J' s‖ ≤ exp ((K₁ + K₁') (t - s)) ∫ₛᵗ (ψ (D r) + ε₁ r)`. -/
theorem norm_variationOn_sub_variationOn_le_of_invariant_left (hv : IsC1FieldOn v Dv a b K₀)
    (hv' : IsC1FieldOn v' Dv' a b K₀')
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hS' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v' a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hDv' : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv' r y‖ ≤ K₁')
    {ψ : ℝ → ℝ} (hψ : MonotoneOn ψ (Ici 0)) (hψ₀ : ∀ q, 0 ≤ q → 0 ≤ ψ q)
    (hDvψ : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ‖Dv r y - Dv r z‖ ≤ ψ ‖y - z‖)
    {t : ℝ} (ht : t ∈ Icc a b) {ε₁ : ℝ → ℝ} (hε₁ : AntitoneOn ε₁ (Icc a t))
    (hε₁₀ : ∀ r ∈ Icc a t, 0 ≤ ε₁ r) (hDvv' : ∀ r ∈ Icc a t, ∀ y ∈ S, ‖Dv r y - Dv' r y‖ ≤ ε₁ r)
    {x : E} (hx : x ∈ S) {D : ℝ → ℝ} (hD : AntitoneOn D (Icc a t))
    (hDflow : ∀ r ∈ Icc a t, ‖flowOn v a b r t x - flowOn v' a b r t x‖ ≤ D r) {s : ℝ}
    (hs : s ∈ Icc a t) :
    ‖variationOn v Dv a b s t x - variationOn v' Dv' a b s t x‖ ≤
      Real.exp ((K₁ + K₁') * (t - s)) * ∫ r in s..t, (ψ (D r) + ε₁ r) := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hK₁' : 0 ≤ K₁' := (norm_nonneg _).trans (hDv' t ht x hx)
  have hsub : Icc s t ⊆ Icc a b := (Icc_subset_Icc_left hs.1).trans (Icc_subset_Icc_right ht.2)
  have hsuba : Icc s t ⊆ Icc a t := Icc_subset_Icc_left hs.1
  set L := Real.exp (K₁ * (t - s)) with hLdef
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have hD₀ : ∀ r ∈ Icc a t, 0 ≤ D r := fun r hr ↦ (norm_nonneg _).trans (hDflow r hr)
  have hanti : AntitoneOn (fun r ↦ ψ (D r) + ε₁ r) (Icc a t) := by
    intro r hr r' hr' hrr'
    exact add_le_add (hψ (hD₀ r' hr') (hD₀ r hr) (hD hr hr' hrr')) (hε₁ hr hr' hrr')
  set ε : ℝ → ℝ := fun r ↦ L * (ψ (D r) + ε₁ r) with hεdef
  have hεanti : AntitoneOn ε (Icc s t) := fun r hr r' hr' hrr' ↦
    mul_le_mul_of_nonneg_left (hanti (hsuba hr) (hsuba hr') hrr') hL
  have hεi : IntervalIntegrable ε volume s t :=
    AntitoneOn.intervalIntegrable (by rwa [uIcc_of_le hs.2])
  have hε₀ : ∀ r ∈ Icc s t, 0 ≤ ε r := fun r hr ↦
    mul_nonneg hL (add_nonneg (hψ₀ _ (hD₀ r (hsuba hr))) (hε₁₀ r (hsuba hr)))
  set g : ℝ → ℝ := fun r ↦ ‖variationOn v Dv a b r t x - variationOn v' Dv' a b r t x‖
    with hgdef
  have hg : ContinuousOn g (Icc s t) :=
    ((hv.continuousOn_variationOn_time ht x).sub
      (hv'.continuousOn_variationOn_time ht x)).norm.mono hsub
  have hmain := le_exp_mul_integral_of_le_integral_left hK₁' hg hεi hε₀ (fun q hq ↦ by
    have hsub' : Icc q t ⊆ Icc a b := (Icc_subset_Icc_left hq.1).trans hsub
    have hint : IntervalIntegrable (fun r ↦ K₁' * g r + ε r) volume q t :=
      ((hg.mono (Icc_subset_Icc_left hq.1)).intervalIntegrable_of_Icc hq.2 |>.const_mul K₁').add
        (hεi.mono_set (by rw [uIcc_of_le hq.2, uIcc_of_le hs.2]; exact Icc_subset_Icc_left hq.1))
    have h := norm_sub_le_integral_of_hasDerivAt
      (e := fun r ↦ variationOn v Dv a b r t x - variationOn v' Dv' a b r t x)
      (e' := fun r ↦ (Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x) -
        (Dv' r (flowOn v' a b r t x)).comp (variationOn v' Dv' a b r t x))
      (h := fun r ↦ K₁' * g r + ε r) hq.2
      (fun r hr ↦ (hv.hasDerivAt_variationOn (hsub' hr) ht x).sub
        (hv'.hasDerivAt_variationOn (hsub' hr) ht x))
      (((hv.continuousOn_variationOn_deriv ht x).sub
        (hv'.continuousOn_variationOn_deriv ht x)).mono hsub') hint
      (fun r hr ↦ by
        have hrs : r ∈ Icc s t := ⟨hq.1.trans hr.1, hr.2⟩
        have hJ : Real.exp (K₁ * |r - t|) ≤ L := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK₁)
          rw [abs_of_nonpos (by linarith [hr.2])]
          linarith [hrs.1]
        exact norm_deriv_comp_sub_le hv hS hS' hDv hDv' hψ hDvψ ht hx (hsub' hr)
          (hDvv' r (hsuba hrs) _ (hS' r (hsub' hr) t ht hx)) (hDflow r (hsuba hrs)) hJ)
    rw [norm_sub_rev] at h
    simpa [hgdef, hv.variationOn_self ht, hv'.variationOn_self ht] using h) s ⟨le_rfl, hs.2⟩
  refine hmain.trans_eq ?_
  rw [hεdef, intervalIntegral.integral_const_mul, hLdef, ← mul_assoc, ← Real.exp_add]
  ring_nf

end IsC1FieldOn

end PDE.Analysis.ODE
