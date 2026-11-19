/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Energy.Difference.Bounds
public import PDE.Fluid.DeGregorio.Energy.Difference.Rate
public import PDE.Fluid.DeGregorio.DynamicRescaling

/-!
# Differentiating the coupled difference energy

Joint `C¹` regularity on a compact spatial interval provides the local uniform
majorants required by the integral-energy theorem. The transport equations and
the spatial integration-by-parts identity then determine the energy rate.

We work with prescribed rescaling rates `cl` and `cw`. The linear transport and
amplitude terms add `(2 cw + cl) E` to the rate, and the Hilbert estimate and
nonlinear coupling bounds are the same as for the physical equation, which is the
case of zero rates.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped ContDiff Topology

namespace DeGregorio

/-- At a common time, the vorticity difference of two classical solutions is paired
with the derivative of their velocity difference. -/
theorem isHilbertPair_sub_of_classical {fields other : Fields} {times : Set ℝ} {t : ℝ}
    (hreg : HasClassicalRegularityOn fields times)
    (hregOther : HasClassicalRegularityOn other times)
    (hbs : SatisfiesBiotSavartOn fields times)
    (hbsOther : SatisfiesBiotSavartOn other times) (ht : t ∈ times) :
    IsHilbertPair (fun x ↦ fields.vorticity x t - other.vorticity x t)
      (deriv fun x ↦ fields.velocity x t - other.velocity x t) :=
  isHilbertPair_sub_of_differentiable (fun _ ↦ hreg.velocity_differentiableAt ht)
    (fun _ ↦ hregOther.velocity_differentiableAt ht) (hbs ht) (hbsOther ht)

/-- Two vorticities that vanish outside `(-L, L)` agree outside `(-L, L)`. -/
theorem vorticity_eq_of_not_mem_Ioo {fields other : Fields} {L t : ℝ}
    (hsupp : ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    {x : ℝ} (hx : x ∉ Ioo (-L) L) : fields.vorticity x t = other.vorticity x t :=
  (hsupp x hx).1.trans (hsupp x hx).2.symm

/-- A bound `K E` on the transport integral bounds the full rescaled rate
`I + c E` by `(K + |c|) E`. -/
theorem norm_add_mul_le_of_norm_le {I c E K : ℝ} (hE : 0 ≤ E) (hI : ‖I‖ ≤ K * E) :
    ‖I + c * E‖ ≤ (K + |c|) * E := by
  calc
    _ ≤ ‖I‖ + ‖c * E‖ := norm_add_le _ _
    _ ≤ K * E + |c| * E := by
      rw [norm_mul, Real.norm_eq_abs c, Real.norm_of_nonneg hE]
      exact add_le_add hI le_rfl
    _ = _ := (add_mul _ _ _).symm

/-- Two rescaled solutions with the same rates satisfy the coupled energy
estimate. The rescaling adds the coefficient `|2 cw + cl|`, which comes from integration
by parts of the linear rescaling terms; the rates are not differentiated. -/
theorem norm_deriv_differenceEnergy_le_of_rescaled {fields other : Fields}
    {cl cw : ℝ → ℝ} {times : Set ℝ} {L C t : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw times)
    (hother : IsClassicalRescaledSolutionOn 1 other cl cw times) (ht : t ∈ times)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsupp : ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C) :
    ‖deriv (differenceEnergy fields other L) t‖ ≤
      ((6 + 2 * L ^ 2) * C + |2 * cw t + cl t|) *
        differenceEnergy fields other L t := by
  let d := fun x ↦ fields.vorticity x t - other.vorticity x t
  let u := fun x ↦ fields.velocity x t
  let v := fun x ↦ fields.velocity x t - other.velocity x t
  let w := fun x ↦ other.vorticity x t
  have hd : ContDiff ℝ 1 d := (hf.sub hg).comp (contDiff_id.prodMk contDiff_const)
  have hu' : ContDiff ℝ 1 u := hu.comp (contDiff_id.prodMk contDiff_const)
  have hv' : ContDiff ℝ 1 v := (hu.sub hv).comp (contDiff_id.prodMk contDiff_const)
  have hw : ContDiff ℝ 1 w := hg.comp (contDiff_id.prodMk contDiff_const)
  have hpair : IsHilbertPair d (deriv v) := isHilbertPair_sub_of_classical
    hsol.regularity hother.regularity hsol.biotSavart hother.biotSavart ht
  have hrate : _ = _ := deriv_differenceEnergy_eq (cl := cl t) (cw := cw t)
    (hf.comp (contDiff_id.prodMk contDiff_const)) hw hu'
    (hv.comp (contDiff_id.prodMk contDiff_const))
    (fun _ ↦ hsol.regularity.vorticity_time_differentiableAt ht)
    (fun _ ↦ hother.regularity.vorticity_time_differentiableAt ht)
    (hasDerivAt_differenceEnergy hf hg L t)
    (fun x ↦ by simpa only [one_mul] using hsol.transport (x := x) ht)
    (fun x ↦ by simpa only [one_mul] using hother.transport (x := x) ht)
    (vorticity_eq_of_not_mem_Ioo hsupp (by simp))
    (vorticity_eq_of_not_mem_Ioo hsupp (by simp))
  rw [hrate]
  exact norm_add_mul_le_of_norm_le (differenceEnergy_nonneg fields other L t)
    (norm_integral_coupled_terms_le hd hu' hv' hw hL hC hpair (sub_eq_zero.mpr hzero)
      (fun x hx ↦ sub_eq_zero.mpr
        (vorticity_eq_of_not_mem_Ioo hsupp fun h ↦ hx ⟨h.1.le, h.2.le⟩)) hbound)

/-- The two coupled PDEs imply an energy differential inequality.
Its constant comes from bounds on the first velocity gradient and the second
vorticity and its spatial derivative on the common support interval. -/
theorem norm_deriv_differenceEnergy_le {fields other : Fields} {times : Set ℝ}
    {L C t : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hsol : IsClassicalSolutionOn 1 fields times)
    (hother : IsClassicalSolutionOn 1 other times) (ht : t ∈ times)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsupp : ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C) :
    ‖deriv (differenceEnergy fields other L) t‖ ≤
      ((6 + 2 * L ^ 2) * C) * differenceEnergy fields other L t := by
  simpa only [mul_zero, add_zero, abs_zero] using norm_deriv_differenceEnergy_le_of_rescaled
    hf hg hu hv hsol.toRescaled hother.toRescaled ht hL hC hsupp hzero hbound

/-- Zero difference energy identifies both fields at an interior time. The
velocity conclusion uses the Hilbert relation and normalization. -/
theorem fields_eq_of_differenceEnergy_eq_zero {fields other : Fields}
    {cl cw : ℝ → ℝ} {times : Set ℝ} {L t : ℝ}
    (hf : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t))
    (hg : ContDiff ℝ 1 (fun x ↦ other.vorticity x t))
    (hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw times)
    (hother : IsClassicalRescaledSolutionOn 1 other cl cw times) (ht : t ∈ times)
    (hsupp : ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (henergy : differenceEnergy fields other L t = 0) :
    ∀ x, fields.vorticity x t = other.vorticity x t ∧
      fields.velocity x t = other.velocity x t := by
  let d := fun y ↦ fields.vorticity y t - other.vorticity y t
  have hpair : IsHilbertPair d (deriv fun y ↦ fields.velocity y t - other.velocity y t) :=
    isHilbertPair_sub_of_classical hsol.regularity hother.regularity hsol.biotSavart
      hother.biotSavart ht
  have hintegral : (∫ y, d y ^ 2) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc (-L) L) (f := fun y ↦ d y ^ 2)]
    · exact henergy
    · intro y hy
      simp only [d, vorticity_eq_of_not_mem_Ioo hsupp fun h ↦ hy ⟨h.1.le, h.2.le⟩, sub_self,
        zero_pow (by decide : 2 ≠ 0)]
  have hae : d =ᵐ[volume] 0 := by
    have hsquare := (integral_eq_zero_iff_of_nonneg (fun y ↦ sq_nonneg (d y))
      hpair.memLp_left.integrable_sq).mp hintegral
    exact hsquare.mono fun _ hy ↦ sq_eq_zero_iff.mp hy
  have hdzero : d = 0 := Measure.eq_of_ae_eq hae (hf.sub hg).continuous continuous_const
  intro x
  have hvbound := hpair.sq_le_abs_mul_integral_sq (hu.sub hv)
    (sub_eq_zero.mpr hzero) x
  rw [hintegral, mul_zero] at hvbound
  exact ⟨sub_eq_zero.mp (congrFun hdzero x),
    sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hvbound (sq_nonneg _)))⟩

end DeGregorio
