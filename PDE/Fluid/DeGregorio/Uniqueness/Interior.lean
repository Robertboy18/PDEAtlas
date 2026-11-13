/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.DifferenceEnergy.Interior
import CAS.ExactTactic

/-!
# Coupled uniqueness with continuous energy traces

The difference equation closes in its own energy when both velocities come
from the corresponding vorticities. Interior derivatives and continuous
endpoint energies suffice for uniqueness throughout the interval.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

namespace DeGregorio

/-- Interior coupled classical equations give the homogeneous energy inequality
using spatial C¹ velocity slices and a fixed support enclosure. -/
theorem norm_deriv_differenceEnergy_le_interior
    {fields other : Fields} {L C a b t : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hsol : IsClassicalSolutionOn 1 fields (Ioo a b))
    (hother : IsClassicalSolutionOn 1 other (Ioo a b)) (ht : t ∈ Ioo a b)
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
  have hleft := hsupp (-L) (by simp)
  have hright := hsupp L (by simp)
  have hrate := norm_deriv_frozen_differenceEnergy_le_interior hf hg hu hv
    hsol.transport hother.transport ht (hsol.biotSavart ht) (hother.biotSavart ht)
    hL hC (hleft.1.trans hleft.2.symm) (hright.1.trans hright.2.symm) hzero hbound
  have hint : (∫ x, (fields.vorticity x t - other.vorticity x t) ^ 2) =
      differenceEnergy fields other L t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz := hsupp x (fun h ↦ hx ⟨h.1.le, h.2.le⟩)
    simp only [hz.1, hz.2, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
  rw [hint] at hrate
  convert hrate using 1
  cas

/-- Equal initial data determine the coupled energy on the full closed interval.
Only the energy trace, rather than its derivative, is required at the endpoints. -/
theorem differenceEnergy_eq_zero_of_same_initialData_interior
    {fields other : Fields} {L C a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b))
    (hu : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hsol : IsClassicalSolutionOn 1 fields (Ioo a b))
    (hother : IsClassicalSolutionOn 1 other (Ioo a b))
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsupp : ∀ t ∈ Ioo a b, ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : ∀ t ∈ Ioo a b, fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ t ∈ Ioo a b, ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C)
    (htrace : ContinuousOn (differenceEnergy fields other L) (Icc a b))
    (hinitial : differenceEnergy fields other L a = 0) :
    ∀ t ∈ Icc a b, differenceEnergy fields other L t = 0 := by
  have hestimate := le_gronwallBound_of_deriv_le_interior htrace
    (fun t ht ↦ (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
      (f := fun x s ↦ fields.vorticity x s - other.vorticity x s)
      (hf.sub hg) ht (-L) L).differentiableAt)
    (δ := 0) (K := (6 + 2 * L ^ 2) * C) (ε := 0) hinitial.le (by
      intro t ht
      simpa only [add_zero] using (le_abs_self _).trans
        (norm_deriv_differenceEnergy_le_interior hf hg (hu t ht) (hv t ht)
          hsol hother ht hL hC (hsupp t ht) (hzero t ht) (hbound t ht)))
  intro t ht
  apply le_antisymm _ (differenceEnergy_nonneg fields other L t)
  simpa only [gronwallBound, zero_mul, zero_div, mul_zero, add_zero, ite_self]
    using hestimate t ht

end DeGregorio
