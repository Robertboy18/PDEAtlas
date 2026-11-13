/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Convex.Deriv
public import PDE.Analysis.Calculus.Piecewise

/-!
# Positive parts with a vanishing first jet on the zero set

A real C2 function whose derivative vanishes at every zero has a C2 positive part.
The domain can be any real normed space, and the hypotheses are local. Positive
or negative directional curvature at a critical zero forces a locally one-sided
germ, by strict convexity on nearby parallel lines. At the remaining zeros the
symmetric Hessian vanishes. Matching derivatives then glue the positive part.

The Hessian of the positive part is either the original Hessian or zero; the
strict-positive-set indicator formula is false at a quadratic minimum.
`contDiffOn_two_max_zero_of_zero_jet` gives the result on any open domain.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict convexity from explicitly supplied first and second derivatives. -/
theorem strictConvexOn_of_hasDerivAt_second_pos {f d : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (d t) t)
    (hd : ∀ t ∈ Icc a b, HasDerivAt d (deriv d t) t)
    (hpos : ∀ t ∈ Icc a b, 0 < deriv d t) : StrictConvexOn ℝ (Icc a b) f := by
  have hm : StrictMonoOn d (Icc a b) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ hpos t (interior_subset ht))
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc a b)
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
  intro x hx y hy hxy
  rw [(hf x (interior_subset hx)).deriv, (hf y (interior_subset hy)).deriv]
  exact hm (interior_subset hx) (interior_subset hy) hxy

/-- A convex function with only critical zeros cannot cross from negative to positive. -/
theorem nonneg_of_convexOn_of_zero_deriv {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ConvexOn ℝ (Icc 0 b) f) (hf : ContinuousOn f (Icc 0 b))
    (hz : ∀ t ∈ Icc 0 b, f t = 0 → HasDerivAt f 0 t)
    (hp : 0 < f b) : 0 ≤ f 0 := by
  by_contra hn
  have hn' : f 0 < 0 := lt_of_not_ge hn
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hb.le hf ⟨hn'.le, hp.le⟩
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by intro he; subst t; linarith)
  have hs := hc.slope_le_of_hasDerivAt ⟨le_rfl, hb.le⟩ ht ht0 (hz t ht hft)
  simp only [slope_def_field, hft, zero_sub, sub_zero] at hs
  have := (div_le_iff₀ ht0).mp hs
  linarith

/-- Restricting a twice differentiable map to an affine line gives its directional Hessian. -/
theorem hasDerivAt_fderiv_affine_line {v : E → ℝ} {y e : E} {t : ℝ}
    (hv : ContDiffAt ℝ 2 v (y + t • e)) :
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ v (y + s • e) e)
      (fderiv ℝ (fderiv ℝ v) (y + t • e) e e) t := by
  have hl : HasDerivAt (fun s : ℝ ↦ y + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add y
  have hd : DifferentiableAt ℝ (fderiv ℝ v) (y + t • e) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc : HasDerivAt (fun s : ℝ ↦ fderiv ℝ v (y + s • e))
      (fderiv ℝ (fderiv ℝ v) (y + t • e) e) t :=
    hd.hasFDerivAt.comp_hasDerivAt t hl
  simpa using hc.clm_apply (hasDerivAt_const t e)

/-- Positive directional curvature at a critical zero forces local nonnegativity,
provided every nearby zero is critical. -/
theorem eventually_nonneg_of_second_pos {v : E → ℝ} {x e : E}
    (hv : ContDiffAt ℝ 2 v x) (hx : v x = 0)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0)
    (he : 0 < fderiv ℝ (fderiv ℝ v) x e e) :
    ∀ᶠ y in 𝓝 x, 0 ≤ v y := by
  have hH : ContinuousAt (fun y ↦ fderiv ℝ (fderiv ℝ v) y e e) x :=
    ((hv.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).continuousAt_fderiv
      one_ne_zero).clm_apply continuousAt_const |>.clm_apply continuousAt_const
  have hregular : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 v y ∧
      (v y = 0 → fderiv ℝ v y = 0) ∧ 0 < fderiv ℝ (fderiv ℝ v) y e e :=
    (hv.eventually (by simp)).and (hz.and (hH.eventually (Ioi_mem_nhds he)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hregular
  let d : ℝ := r / (4 * (‖e‖ + 1))
  have hd : 0 < d := div_pos hr (by positivity)
  have hdn : d * ‖e‖ < r / 2 := by
    have he1 : 0 < ‖e‖ + 1 := by positivity
    have heq : d * (4 * (‖e‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
    nlinarith [norm_nonneg e]
  have hline : ∀ y ∈ Metric.ball x (r / 2), ∀ t ∈ Icc 0 d,
      y + t • e ∈ Metric.ball x r := by
    intro y hy t ht
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    have htriangle : ‖y + t • e - x‖ ≤ ‖y - x‖ + t * ‖e‖ := by
      calc
        ‖y + t • e - x‖ = ‖(y - x) + t • e‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖t • e‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hmul := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg e)
    linarith
  have hfline : ∀ y ∈ Metric.ball x (r / 2), ∀ t ∈ Icc 0 d,
      HasDerivAt (fun s : ℝ ↦ v (y + s • e)) (fderiv ℝ v (y + t • e) e) t := by
    intro y hy t ht
    apply ((hball (hline y hy t ht)).1.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt
    simpa using ((hasDerivAt_id t).smul_const e).const_add y
  have hconv : ∀ y ∈ Metric.ball x (r / 2),
      StrictConvexOn ℝ (Icc 0 d) (fun t : ℝ ↦ v (y + t • e)) := by
    intro y hy
    apply strictConvexOn_of_hasDerivAt_second_pos (hfline y hy)
    · intro t ht
      exact (hasDerivAt_fderiv_affine_line (hball (hline y hy t ht)).1).congr_deriv
        (hasDerivAt_fderiv_affine_line (hball (hline y hy t ht)).1).deriv.symm
    · intro t ht
      rw [(hasDerivAt_fderiv_affine_line (hball (hline y hy t ht)).1).deriv]
      exact (hball (hline y hy t ht)).2.2
  have hxb : x ∈ Metric.ball x (r / 2) := Metric.mem_ball_self (by positivity)
  have hzero : HasDerivAt (fun t : ℝ ↦ v (x + t • e)) 0 0 := by
    simpa [hz.self_of_nhds hx] using hfline x hxb 0 ⟨le_rfl, hd.le⟩
  have hp : 0 < v (x + d • e) := by
    have hs := (hconv x hxb).lt_slope_of_hasDerivAt ⟨le_rfl, hd.le⟩
      ⟨hd.le, le_rfl⟩ hd hzero
    simp only [slope_def_field, zero_smul, add_zero, hx, sub_zero] at hs
    exact (div_pos_iff.mp hs).elim (fun h ↦ h.1) (fun h ↦ (not_lt_of_ge hd.le h.2).elim)
  have hshift : ContinuousAt (fun y : E ↦ y + d • e) x :=
    continuousAt_id.add continuousAt_const
  have hcont : ContinuousAt (fun y ↦ v (y + d • e)) x :=
    (hball (hline x hxb d ⟨hd.le, le_rfl⟩)).1.continuousAt.comp (f := fun y : E ↦ y + d • e) hshift
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < r / 2),
    hcont.eventually (Ioi_mem_nhds hp)] with y hy hyp
  have hc := hconv y hy
  have hnonneg := nonneg_of_convexOn_of_zero_deriv hd hc.convexOn
    (fun t ht ↦ (hfline y hy t ht).continuousAt.continuousWithinAt) (fun t ht hzt ↦ ?_) hyp
  · simpa using hnonneg
  · simpa [(hball (hline y hy t ht)).2.1 hzt] using hfline y hy t ht

/-- The derivative of the positive part when the first derivative vanishes at a zero. -/
theorem hasFDerivAt_max_zero_of_zero_jet {v : E → ℝ} {x : E}
    (hv : DifferentiableAt ℝ v x) (hz : v x = 0 → fderiv ℝ v x = 0) :
    HasFDerivAt (fun y ↦ max (v y) 0)
      (if 0 < v x then fderiv ℝ v x else 0) x := by
  classical
  rcases lt_trichotomy 0 (v x) with hp | hzv | hn
  · rw [ite_eq_left hp]
    apply hv.hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [hv.continuousAt.eventually (Ioi_mem_nhds hp)] with y hy
    exact max_eq_left hy.le
  · have hv0 : v x = 0 := hzv.symm
    have hd : HasFDerivAt v (0 : E →L[ℝ] ℝ) x := by simpa [hz hv0] using hv.hasFDerivAt
    have heq : (fun y ↦ if 0 < v y then v y else 0) = (fun y ↦ max (v y) 0) := by
      funext y
      split_ifs with hy
      · exact (max_eq_left hy.le).symm
      · exact (max_eq_right (le_of_not_gt hy)).symm
    simpa only [hv0, lt_self_iff_false, ite_false, heq] using
      hasFDerivAt_if_of_eq (fun y ↦ 0 < v y) hd (hasFDerivAt_const 0 x) hv0
  · rw [ite_eq_right (not_lt_of_ge hn.le)]
    apply (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq
    filter_upwards [hv.continuousAt.eventually (Iio_mem_nhds hn)] with y hy
    exact max_eq_right hy.le

/-- At a zero with zero Hessian, the derivative of the positive part has derivative zero. -/
theorem hasFDerivAt_fderiv_max_zero_of_second_zero {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x) (hx : v x = 0)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0)
    (hH : fderiv ℝ (fderiv ℝ v) x = 0) :
    HasFDerivAt (fderiv ℝ (fun y ↦ max (v y) 0))
      (0 : E →L[ℝ] E →L[ℝ] ℝ) x := by
  classical
  have hd : HasFDerivAt (fderiv ℝ v) (0 : E →L[ℝ] E →L[ℝ] ℝ) x := by
    simpa only [hH] using
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hglue := hasFDerivAt_if_of_eq (fun y ↦ 0 < v y) hd
    (hasFDerivAt_const (0 : E →L[ℝ] ℝ) x) (hz.self_of_nhds hx)
  apply hglue.congr_of_eventuallyEq
  filter_upwards [hv.eventually (by simp), hz] with y hy hyz
  exact (hasFDerivAt_max_zero_of_zero_jet (hy.differentiableAt two_ne_zero) hyz).fderiv

/-- At a critical zero, either the function has one sign locally or its Hessian vanishes. -/
theorem eventually_one_sign_or_second_eq_zero {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x) (hx : v x = 0)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    (∀ᶠ y in 𝓝 x, 0 ≤ v y) ∨ (∀ᶠ y in 𝓝 x, v y ≤ 0) ∨
      fderiv ℝ (fderiv ℝ v) x = 0 := by
  classical
  by_cases hp : ∀ᶠ y in 𝓝 x, 0 ≤ v y
  · exact Or.inl hp
  right
  by_cases hn : ∀ᶠ y in 𝓝 x, v y ≤ 0
  · exact Or.inl hn
  right
  have hneg : fderiv ℝ (fderiv ℝ (fun y ↦ -v y)) x =
      -fderiv ℝ (fderiv ℝ v) x := by
    have heq : fderiv ℝ (fun y ↦ -v y) = -fderiv ℝ v := funext fun y ↦ fderiv_neg
    rw [heq, fderiv_neg]
  have hdiag (e : E) : fderiv ℝ (fderiv ℝ v) x e e = 0 := by
    apply le_antisymm
    · exact le_of_not_gt fun he ↦ hp (eventually_nonneg_of_second_pos hv hx hz he)
    · apply le_of_not_gt
      intro he
      have hnz : ∀ᶠ y in 𝓝 x, -v y = 0 → fderiv ℝ (fun z ↦ -v z) y = 0 := by
        filter_upwards [hz] with y hy hzy
        rw [fderiv_fun_neg, hy (neg_eq_zero.mp hzy), neg_zero]
      have hne : 0 < fderiv ℝ (fderiv ℝ (fun y ↦ -v y)) x e e := by
        simpa only [hneg, neg_apply, neg_pos] using he
      exact hn ((eventually_nonneg_of_second_pos hv.neg (by simp [hx]) hnz hne).mono
        fun y hy ↦ neg_nonneg.mp hy)
  ext e z
  have hs := hv.isSymmSndFDerivAt (by simp) e z
  have hsum := hdiag (e + z)
  simp only [map_add, add_apply, hdiag, hs] at hsum
  change fderiv ℝ (fderiv ℝ v) x e z = 0
  linarith

/-- Positive-part germs are either an original branch, the zero branch, or a flat second jet. -/
theorem max_zero_germ_or_flat {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    ((fun y ↦ max (v y) 0) =ᶠ[𝓝 x] v) ∨
    ((fun y ↦ max (v y) 0) =ᶠ[𝓝 x] fun _ ↦ 0) ∨
    (v x = 0 ∧ fderiv ℝ (fderiv ℝ v) x = 0) := by
  rcases lt_trichotomy (v x) 0 with hn | hx | hp
  · exact Or.inr (Or.inl ((hv.continuousAt.eventually (Iio_mem_nhds hn)).mono
      fun y hy ↦ max_eq_right hy.le))
  · rcases eventually_one_sign_or_second_eq_zero hv hx hz with hp | hn | hH
    · exact Or.inl (hp.mono fun y hy ↦ max_eq_left hy)
    · exact Or.inr (Or.inl (hn.mono fun y hy ↦ max_eq_right hy))
    · exact Or.inr (Or.inr ⟨hx, hH⟩)
  · exact Or.inl ((hv.continuousAt.eventually (Ioi_mem_nhds hp)).mono
      fun y hy ↦ max_eq_left hy.le)

/-- The Hessian of the positive part is pointwise either the original Hessian or zero.
At a locally nonnegative quadratic zero it is the original Hessian. -/
theorem second_fderiv_max_zero_eq_or {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    fderiv ℝ (fderiv ℝ (fun y ↦ max (v y) 0)) x = fderiv ℝ (fderiv ℝ v) x ∨
      fderiv ℝ (fderiv ℝ (fun y ↦ max (v y) 0)) x = 0 := by
  rcases max_zero_germ_or_flat hv hz with h | h | ⟨hx, hH⟩
  · exact Or.inl h.fderiv.fderiv_eq
  · right
    have hconst : fderiv ℝ (fun _ : E ↦ (0 : ℝ)) =
        fun _ ↦ (0 : E →L[ℝ] ℝ) := funext fun _ ↦ fderiv_const_apply _
    simpa only [hconst, fderiv_const_apply] using
      (h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  · exact Or.inr (hasFDerivAt_fderiv_max_zero_of_second_zero hv hx hz hH).fderiv

/-- The first derivative of the positive part is differentiable under the zero-jet condition. -/
theorem differentiableAt_fderiv_max_zero {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    DifferentiableAt ℝ (fderiv ℝ (fun y ↦ max (v y) 0)) x := by
  rcases max_zero_germ_or_flat hv hz with h | h | ⟨hx, hH⟩
  · have hd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact hd.congr_of_eventuallyEq (h.fderiv (𝕜 := ℝ))
  · have hc : DifferentiableAt ℝ (fderiv ℝ (fun _ : E ↦ (0 : ℝ))) x := by
      exact ((contDiffAt_const (c := (0 : ℝ)) (x := x) (n := (2 : ℕ∞ω))).fderiv_right
        (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact hc.congr_of_eventuallyEq h.fderiv
  · exact (hasFDerivAt_fderiv_max_zero_of_second_zero hv hx hz hH).differentiableAt

/-- The Hessian of the positive part is continuous, including at sign-changing zeros. -/
theorem continuousAt_second_fderiv_max_zero {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    ContinuousAt (fderiv ℝ (fderiv ℝ (fun y ↦ max (v y) 0))) x := by
  have hc : ContinuousAt (fderiv ℝ (fderiv ℝ v)) x :=
    (hv.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv one_ne_zero
  rcases max_zero_germ_or_flat hv hz with h | h | ⟨hx, hH⟩
  · exact hc.congr_of_eventuallyEq h.fderiv.fderiv
  · have hc0 : ContinuousAt (fderiv ℝ (fderiv ℝ (fun _ : E ↦ (0 : ℝ)))) x := by
      exact ((contDiffAt_const (c := (0 : ℝ)) (x := x) (n := (2 : ℕ∞ω))).fderiv_right
        (m := 1) (by norm_num)).continuousAt_fderiv one_ne_zero
    exact hc0.congr_of_eventuallyEq h.fderiv.fderiv
  · have he : fderiv ℝ (fderiv ℝ (fun y ↦ max (v y) 0)) x = 0 :=
      (hasFDerivAt_fderiv_max_zero_of_second_zero hv hx hz hH).fderiv
    rw [ContinuousAt, he]
    have hlimit : Tendsto (fderiv ℝ (fderiv ℝ v)) (𝓝 x) (𝓝 0) := by
      simpa only [ContinuousAt, hH] using hc
    apply tendsto_def.mpr
    intro t ht
    filter_upwards [hlimit.eventually ht, hv.eventually (by simp),
      eventually_eventually_nhds.mpr hz] with y hyt hy hyz
    change fderiv ℝ (fderiv ℝ (fun z ↦ max (v z) 0)) y ∈ t
    rcases second_fderiv_max_zero_eq_or hy hyz with h | h
    · rwa [h]
    · rw [h]
      exact mem_of_mem_nhds ht

/-- Taking the positive part preserves C2 regularity if every nearby zero has zero first jet. -/
theorem contDiffAt_two_max_zero_of_zero_jet {v : E → ℝ} {x : E}
    (hv : ContDiffAt ℝ 2 v x)
    (hz : ∀ᶠ y in 𝓝 x, v y = 0 → fderiv ℝ v y = 0) :
    ContDiffAt ℝ 2 (fun y ↦ max (v y) 0) x := by
  let s : Set E := {y | ContDiffAt ℝ 2 v y ∧
    ∀ᶠ z in 𝓝 y, v z = 0 → fderiv ℝ v z = 0}
  have hs : s ∈ 𝓝 x := (hv.eventually (by simp)).and (eventually_eventually_nhds.mpr hz)
  have hfirst : ∀ y ∈ s, HasFDerivAt (fun z ↦ max (v z) 0)
      (fderiv ℝ (fun z ↦ max (v z) 0) y) y := by
    intro y hy
    exact (hasFDerivAt_max_zero_of_zero_jet (hy.1.differentiableAt two_ne_zero)
      hy.2.self_of_nhds).differentiableAt.hasFDerivAt
  have hsecond : ContDiffAt ℝ 1 (fderiv ℝ (fun y ↦ max (v y) 0)) x := by
    rw [contDiffAt_one_iff]
    refine ⟨fderiv ℝ (fderiv ℝ (fun y ↦ max (v y) 0)), s, hs, ?_, ?_⟩
    · exact fun y hy ↦ (continuousAt_second_fderiv_max_zero hy.1 hy.2).continuousWithinAt
    · exact fun y hy ↦ (differentiableAt_fderiv_max_zero hy.1 hy.2).hasFDerivAt
  exact (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨fderiv ℝ (fun y ↦ max (v y) 0), ⟨s, hs, hfirst⟩, hsecond⟩

/-- Positive-part regularity on an arbitrary open domain, with no boundary extension premise. -/
theorem contDiffOn_two_max_zero_of_zero_jet {v : E → ℝ} {s : Set E}
    (hs : IsOpen s) (hv : ContDiffOn ℝ 2 v s)
    (hz : ∀ x ∈ s, v x = 0 → fderiv ℝ v x = 0) :
    ContDiffOn ℝ 2 (fun x ↦ max (v x) 0) s := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_two_max_zero_of_zero_jet ((hv x hx).contDiffAt (hs.mem_nhds hx))
  filter_upwards [hs.mem_nhds hx] with y hy
  exact hz y hy

end PDE.Analysis
