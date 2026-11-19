/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness.Rescaled.InteriorEnergy
public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Trace
public import PDE.Fluid.DeGregorio.Characteristics.Oddness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Oddness on a closed interval from an open-slab solution

The solution is compared with its signed reflection. An L² bound on the
spatial vorticity derivative closes the interior energy inequality uniformly
in time. Continuous traces then give oddness at both endpoints.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution

namespace DeGregorio

/-- Odd initial data stay odd for a normalized rescaled solution on
an open slab with continuous endpoint traces and uniform spatial energy bounds. -/
theorem IsClassicalRescaledSolutionOn.odd_on_closed_slab_of_initialData
    {fields : Fields} {cl cw : ℝ → ℝ} {a b R C D : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Ioo a b))
    (hω : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ 1 (Function.uncurry fields.velocity) (univ ×ˢ Ioo a b))
    (hab : a < b)
    (hcl : ContinuousOn cl (Icc a b)) (hcw : ContinuousOn cw (Icc a b))
    (hspace : ∀ t ∈ Icc a b, Continuous (fun x ↦ fields.vorticity x t))
    (htraceω : ∀ x, ContinuousOn (fields.vorticity x) (Icc a b))
    (htraceu : ∀ x, ContinuousOn (fields.velocity x) (Icc a b))
    (hvalue : ∀ t ∈ Icc a b, ∀ x, |fields.vorticity x t| ≤ C)
    (hgradient : ∀ t ∈ Ioo a b, ∀ x, |deriv (fun y ↦ fields.velocity y t) x| ≤ C)
    (hderiv : ∀ t ∈ Ioo a b,
      MemLp (deriv (fun x ↦ fields.vorticity x t)) 2 volume ∧
        (∫ x, deriv (fun y ↦ fields.vorticity y t) x ^ 2) ≤ D)
    (henclosure : ∀ t ∈ Ioo a b, ∀ x, x ∉ Ioo (-R) R → fields.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Ioo a b, fields.velocity 0 t = 0)
    (hinitial : Function.Odd (fun x ↦ fields.vorticity x a)) :
    ∀ t ∈ Icc a b,
      Function.Odd (fun x ↦ fields.vorticity x t) ∧
        Function.Odd (fun x ↦ fields.velocity x t) := by
  let other := DeGregorio.reflectedFields fields
  have hω' : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b) :=
    contDiffOn_neg_reflect_slab hω
  have hu' : ContDiffOn ℝ 1 (Function.uncurry other.velocity) (univ ×ˢ Ioo a b) :=
    contDiffOn_neg_reflect_slab hu
  have hsupp (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) (hx : x ∉ Ioo (-R) R) :
      other.vorticity x t = 0 ∧ fields.vorticity x t = 0 :=
    ⟨reflectedFields_vorticity_eq_zero_outside (henclosure t ht) x hx,
      henclosure t ht x hx⟩
  have hzero (t : ℝ) (ht : t ∈ Ioo a b) :
      other.velocity 0 t = fields.velocity 0 t := by
    simp only [other, DeGregorio.reflectedFields, neg_zero, hnormalized t ht]
  let E := differenceEnergy other fields R
  have hcont : ContinuousOn E (Icc a b) :=
    continuousOn_integral_sq_Icc_of_traces
      (f := fun x t ↦ other.vorticity x t - fields.vorticity x t) (C := 2 * C)
      (fun t ht ↦ ((hspace t ht).comp continuous_neg).neg.sub (hspace t ht))
      (fun x ↦ (htraceω (-x)).neg.sub (htraceω x)) (fun t ht x ↦ by
        change |-fields.vorticity (-x) t - fields.vorticity x t| ≤ _
        linarith [abs_sub (-fields.vorticity (-x) t) (fields.vorticity x t),
          abs_neg (fields.vorticity (-x) t), hvalue t ht (-x), hvalue t ht x]) (-R) R
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun t ↦ 2 * cw t + cl t)
    ((continuousOn_const.mul hcw).add hcl)
  have henergy : ∀ t ∈ Icc a b, E t = 0 := by
    refine eq_zero_on_Icc_of_deriv_le_mul hcont
      (fun t _ ↦ differenceEnergy_nonneg other fields R t) (K := 5 * C + 1 + R * D + K)
      (fun t ht ↦ (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
        (f := fun x s ↦ other.vorticity x s - fields.vorticity x s)
        (hω'.sub hω) ht (-R) R).differentiableAt) (fun t ht ↦ ?_) ?_
    · have he := norm_deriv_differenceEnergy_le_on_slab hω' hω hu' hu
        hsol.reflectedFields hsol ht (hsupp t ht) (hzero t ht)
        (fun x _ ↦ ⟨by
          rw [deriv_reflectedFields_velocity]
          exact hgradient t ht (-x), hvalue t (Ioo_subset_Icc_self ht) x⟩)
        (hderiv t ht).1 (hderiv t ht).2
      exact (le_abs_self (deriv E t)).trans (he.trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (hK t (Ioo_subset_Icc_self ht)))
          (differenceEnergy_nonneg other fields R t)))
    · have hi (x : ℝ) : other.vorticity x a = fields.vorticity x a := by
        simp only [other, DeGregorio.reflectedFields, hinitial x, neg_neg]
      simp only [E, differenceEnergy, hi, sub_self, zero_pow (by decide : 2 ≠ 0),
        integral_zero]
  have hodd (t : ℝ) (ht : t ∈ Ioo a b) :
      Function.Odd (fun x ↦ fields.vorticity x t) ∧
        Function.Odd (fun x ↦ fields.velocity x t) := by
    have heq := fields_eq_of_differenceEnergy_eq_zero
      (contDiff_slice_of_contDiffOn_cylinder hω' ht)
      (contDiff_slice_of_contDiffOn_cylinder hω ht)
      (contDiff_slice_of_contDiffOn_cylinder hu' ht)
      (contDiff_slice_of_contDiffOn_cylinder hu ht)
      hsol.reflectedFields hsol ht (hsupp t ht) (hzero t ht)
      (henergy t (Ioo_subset_Icc_self ht))
    exact ⟨fun x ↦ neg_eq_iff_eq_neg.mp (heq x).1,
      fun x ↦ neg_eq_iff_eq_neg.mp (heq x).2⟩
  exact fun t ht ↦ ⟨fun x ↦ eqOn_Icc_of_eqOn_Ioo_of_continuousOn hab
    (htraceω (-x)) (htraceω x).neg (fun s hs ↦ (hodd s hs).1 x) ht,
    fun x ↦ eqOn_Icc_of_eqOn_Ioo_of_continuousOn hab
      (htraceu (-x)) (htraceu x).neg (fun s hs ↦ (hodd s hs).2 x) ht⟩

end DeGregorio
