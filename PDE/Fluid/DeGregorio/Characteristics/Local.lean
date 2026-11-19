/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Characteristics
import PDE.Representations.Similarity.Dynamic
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local characteristics and the stretching integral

A given jointly `C¹` velocity has a local characteristic through every spacetime point.
We apply Mathlib's local ODE existence theorem to the autonomous vector field
`(x, t) ↦ (a u(x, t), 1)`, and prove that its time coordinate is the independent variable.

The spatial velocity derivative is continuous, so its integral along a characteristic
is a primitive of the stretching coefficient. For fields satisfying the De Gregorio
transport equation with this velocity, the constructed path therefore carries the
vorticity formula and the sign preservation of `PDE.Fluid.DeGregorio.Characteristics`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open PDE.Representations.Similarity

namespace DeGregorio

/-- A jointly `C¹` velocity admits a local characteristic through every initial point.
The path is constructed by the ODE existence theorem for the autonomous spacetime field. -/
theorem exists_local_characteristic_of_contDiff
    (a x₀ t₀ : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 1 (Function.uncurry u)) :
    ∃ path : ℝ → ℝ, path t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt path (a * u (path t) t) t := by
  have hF : ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ (a * u p.1 p.2, (1 : ℝ))) (x₀, t₀) :=
    ((contDiff_const.mul hu).prodMk contDiff_const).contDiffAt
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have hzero : ∀ s ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun r ↦ (α r).2 - r) 0 s := by
    intro s hs
    have hsnd : HasDerivAt (fun r ↦ (α r).2) 1 s := by
      simpa using (hα s hs).hasFDerivAt.snd.hasDerivAt
    convert! hsnd.sub (hasDerivAt_id s) using 1
    simp
  have htime : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), (α t).2 = t := by
    intro t ht
    have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) :=
      ⟨sub_lt_self t₀ hε, lt_add_of_pos_right t₀ hε⟩
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hzero s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hzero s hs).deriv) ht ht₀
    apply sub_eq_zero.mp
    simpa only [hα₀, sub_self] using heq
  refine ⟨fun t ↦ (α t).1, congrArg Prod.fst hα₀, ε, hε, ?_⟩
  intro t ht
  simpa [htime t ht] using (hα t ht).hasFDerivAt.fst.hasDerivAt

/-- The spatial derivative of a jointly `C¹` velocity is jointly continuous. -/
theorem continuous_spatial_deriv_of_contDiff
    {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 1 (Function.uncurry u)) :
    Continuous (fun p : ℝ × ℝ ↦ deriv (fun x ↦ u x p.2) p.1) := by
  have hD : Continuous (fun p : ℝ × ℝ ↦
      fderiv ℝ (Function.uncurry u) p (1, 0)) :=
    (hu.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  convert hD using 1
  funext p
  rw [fderiv_uncurry_apply_prod u p.1 1 p.2 0
    (hu.differentiable (by simp)).differentiableAt]
  simp [fderiv_eq_smul_deriv]

/-- The stretching coefficient is integrable between any two times of a continuous path
in a convex time domain. -/
theorem intervalIntegrable_velocity_deriv_along_path
    {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 1 (Function.uncurry u))
    {path : ℝ → ℝ} {times : Set ℝ} (hconvex : Convex ℝ times)
    (hpath : ContinuousOn path times) {t₀ t : ℝ} (ht₀ : t₀ ∈ times) (ht : t ∈ times) :
    IntervalIntegrable (fun s ↦ deriv (fun x ↦ u x s) (path s)) volume t₀ t := by
  have hcont : ContinuousOn (fun s ↦ deriv (fun x ↦ u x s) (path s)) times :=
    (continuous_spatial_deriv_of_contDiff hu).comp_continuousOn
      (hpath.prodMk continuousOn_id)
  exact (hcont.mono (hconvex.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable

/-- Integrating the stretching coefficient along a continuous path gives its primitive
on an open convex time domain, including times on either side of the base time. -/
theorem hasDerivAt_characteristic_stretching_integral
    {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 1 (Function.uncurry u))
    {path : ℝ → ℝ} {times : Set ℝ} (hopen : IsOpen times) (hconvex : Convex ℝ times)
    (hpath : ContinuousOn path times) {t₀ t : ℝ} (ht₀ : t₀ ∈ times) (ht : t ∈ times) :
    HasDerivAt (fun r ↦ ∫ s in t₀..r, deriv (fun x ↦ u x s) (path s))
      (deriv (fun x ↦ u x t) (path t)) t := by
  have hcont : ContinuousOn (fun s ↦ deriv (fun x ↦ u x s) (path s)) times :=
    (continuous_spatial_deriv_of_contDiff hu).comp_continuousOn
      (hpath.prodMk continuousOn_id)
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_velocity_deriv_along_path hu hconvex hpath ht₀ ht)
    (hcont.stronglyMeasurableAtFilter hopen t ht)
    (hcont.continuousAt (hopen.mem_nhds ht))

/-- Along a characteristic in an open convex time set, `ω(X(t), t)` equals
`ω(X(t₀), t₀) exp (∫ u_x(X(s), s) ds)` from `t₀` to `t`, for `t` on either side of `t₀`. -/
theorem vorticity_characteristic_eq_exp_integral
    {a : ℝ} {fields : Fields} {times : Set ℝ} {path : ℝ → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hopen : IsOpen times) (hconvex : Convex ℝ times)
    (hregularity : HasClassicalRegularityOn fields times)
    (htransport : SatisfiesTransportEquationOn a fields times)
    (hpath : ∀ s ∈ times, HasDerivAt path (a * fields.velocity (path s) s) s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ times) (ht : t ∈ times) :
    fields.vorticity (path t) t = fields.vorticity (path t₀) t₀ *
      Real.exp (∫ s in t₀..t, deriv (fun x ↦ fields.velocity x s) (path s)) := by
  let primitive (r : ℝ) := ∫ s in t₀..r, deriv (fun x ↦ fields.velocity x s) (path s)
  have hcont : ContinuousOn path times :=
    fun s hs ↦ (hpath s hs).continuousAt.continuousWithinAt
  have hzero : ∀ s ∈ times, HasDerivAt
      (fun r ↦ fields.vorticity (path r) r * Real.exp (-primitive r)) 0 s := by
    intro s hs
    exact hasDerivAt_vorticity_integratingFactor hregularity htransport hs (hpath s hs)
      (hasDerivAt_characteristic_stretching_integral hu hopen hconvex hcont ht₀ hs)
  have hconstant := hopen.is_const_of_deriv_eq_zero hconvex.isPreconnected
    (fun s hs ↦ (hzero s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hzero s hs).deriv) ht ht₀
  have hproduct :
      fields.vorticity (path t) t * Real.exp (-primitive t) =
        fields.vorticity (path t₀) t₀ := by
    simpa only [primitive, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one]
      using hconstant
  have hquotient := (eq_div_iff (Real.exp_ne_zero (-primitive t))).mpr hproduct
  simpa only [Real.exp_neg, div_eq_mul_inv, inv_inv] using hquotient

/-- For a jointly `C¹` velocity and fields satisfying the transport equation on an open
time set, a characteristic through `(x₀, t₀)` exists on an interval `(t₀ - ε, t₀ + ε)`
inside that set. Along it the vorticity satisfies the exponential integral formula, so
its zero set and its sign are preserved. -/
theorem exists_local_characteristic_with_vorticity
    (a x₀ t₀ : ℝ) (fields : Fields) (times : Set ℝ)
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hopen : IsOpen times) (ht₀ : t₀ ∈ times)
    (hregularity : HasClassicalRegularityOn fields times)
    (htransport : SatisfiesTransportEquationOn a fields times) :
    ∃ ε > (0 : ℝ), Ioo (t₀ - ε) (t₀ + ε) ⊆ times ∧
      ∃ path : ℝ → ℝ, path t₀ = x₀ ∧
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt path (a * fields.velocity (path t) t) t) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          IntervalIntegrable
            (fun s ↦ deriv (fun x ↦ fields.velocity x s) (path s)) volume t₀ t ∧
          fields.vorticity (path t) t = fields.vorticity x₀ t₀ *
            Real.exp (∫ s in t₀..t, deriv (fun x ↦ fields.velocity x s) (path s)) ∧
          (fields.vorticity (path t) t = 0 ↔ fields.vorticity x₀ t₀ = 0) ∧
          (0 < fields.vorticity (path t) t ↔ 0 < fields.vorticity x₀ t₀) ∧
          (fields.vorticity (path t) t < 0 ↔ fields.vorticity x₀ t₀ < 0) := by
  obtain ⟨path, hpath₀, δ, hδ, hpath⟩ :=
    exists_local_characteristic_of_contDiff a x₀ t₀ fields.velocity hu
  obtain ⟨η, hη, hηtimes⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ht₀)
  rw [Real.ball_eq_Ioo] at hηtimes
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hδsubset : Ioo (t₀ - ε) (t₀ + ε) ⊆ Ioo (t₀ - δ) (t₀ + δ) :=
    Ioo_subset_Ioo (sub_le_sub_left hεδ t₀) (add_le_add le_rfl hεδ)
  have hsubset : Ioo (t₀ - ε) (t₀ + ε) ⊆ times :=
    (Ioo_subset_Ioo (sub_le_sub_left hεη t₀) (add_le_add le_rfl hεη)).trans hηtimes
  have hpath' : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt path (a * fields.velocity (path t) t) t :=
    fun t ht ↦ hpath t (hδsubset ht)
  have hcont : ContinuousOn path (Ioo (t₀ - ε) (t₀ + ε)) :=
    fun t ht ↦ (hpath' t ht).continuousAt.continuousWithinAt
  have hinitial : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) :=
    ⟨sub_lt_self t₀ hε, lt_add_of_pos_right t₀ hε⟩
  have hregularity' : HasClassicalRegularityOn fields (Ioo (t₀ - ε) (t₀ + ε)) :=
    ⟨fun ht ↦ hregularity.vorticity_differentiableAt (hsubset ht),
      fun ht ↦ hregularity.velocity_differentiableAt (hsubset ht)⟩
  have htransport' : SatisfiesTransportEquationOn a fields (Ioo (t₀ - ε) (t₀ + ε)) := by
    intro x t ht
    exact htransport (hsubset ht)
  refine ⟨ε, hε, hsubset, path, hpath₀, hpath', ?_⟩
  intro t ht
  have hformula := vorticity_characteristic_eq_exp_integral hu isOpen_Ioo (convex_Ioo _ _)
    hregularity' htransport' hpath' hinitial ht
  rw [hpath₀] at hformula
  refine ⟨intervalIntegrable_velocity_deriv_along_path hu (convex_Ioo _ _)
    hcont hinitial ht, hformula, ?_, ?_, ?_⟩
  · rw [hformula, mul_eq_zero]
    simp only [Real.exp_ne_zero, or_false]
  · rw [hformula]
    exact mul_pos_iff_of_pos_right (Real.exp_pos _)
  · rw [hformula]
    simpa only [zero_mul] using
      (mul_lt_mul_iff_left₀
        (Real.exp_pos (∫ s in t₀..t, deriv (fun x ↦ fields.velocity x s) (path s))) :
        fields.vorticity x₀ t₀ *
            Real.exp (∫ s in t₀..t, deriv (fun x ↦ fields.velocity x s) (path s)) <
          0 * Real.exp (∫ s in t₀..t, deriv (fun x ↦ fields.velocity x s) (path s)) ↔
        fields.vorticity x₀ t₀ < 0)

end DeGregorio
