/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Cylinder
public import PDE.Analysis.Evolution.Time.GronwallInterior
public import PDE.Fluid.DeGregorio.Uniqueness.Rescaled.WeakEnergy

/-!
# Interior energy rates for rescaled solutions

The transport and spectral Hilbert equations are used only at an interior
slab time. The background derivative is controlled in L², so the rate estimate
can remain uniform as the time approaches an endpoint.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution

namespace DeGregorio

/-- Rescaled solutions satisfy a difference-energy estimate on the open
slab using an L² bound on the background spatial derivative. -/
theorem norm_deriv_differenceEnergy_le_on_slab {fields other : Fields}
    {cl cw : ℝ → ℝ} {a b L C D t : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ 1 (Function.uncurry fields.velocity) (univ ×ˢ Ioo a b))
    (hv : ContDiffOn ℝ 1 (Function.uncurry other.velocity) (univ ×ˢ Ioo a b))
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Ioo a b))
    (hother : IsClassicalRescaledSolutionOn 1 other cl cw (Ioo a b)) (ht : t ∈ Ioo a b)
    (hsupp : ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C)
    (hderivLp : MemLp (deriv (fun x ↦ other.vorticity x t)) 2 volume)
    (hderivBound : (∫ x, deriv (fun y ↦ other.vorticity y t) x ^ 2) ≤ D) :
    ‖deriv (differenceEnergy fields other L) t‖ ≤
      (5 * C + 1 + L * D + |2 * cw t + cl t|) *
        differenceEnergy fields other L t := by
  let d := fun x ↦ fields.vorticity x t - other.vorticity x t
  let u := fun x ↦ fields.velocity x t
  let v := fun x ↦ fields.velocity x t - other.velocity x t
  let w := fun x ↦ other.vorticity x t
  have hu' : ContDiff ℝ 1 u := contDiff_slice_of_contDiffOn_cylinder hu ht
  have hv' : ContDiff ℝ 1 v := contDiff_slice_of_contDiffOn_cylinder
    (f := fun x s ↦ fields.velocity x s - other.velocity x s) (hu.sub hv) ht
  have hw : ContDiff ℝ 1 w := contDiff_slice_of_contDiffOn_cylinder hg ht
  have hpair : IsHilbertPair d (deriv v) := isHilbertPair_sub_of_classical
    hsol.regularity hother.regularity hsol.biotSavart hother.biotSavart ht
  have hrate : deriv (differenceEnergy fields other L) t =
      (∫ x in Icc (-L) L, 3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x) +
          (2 * cw t + cl t) * differenceEnergy fields other L t := by
    exact deriv_differenceEnergy_eq (cl := cl t) (cw := cw t)
      (contDiff_slice_of_contDiffOn_cylinder hf ht) hw hu' (contDiff_slice_of_contDiffOn_cylinder hv
        ht)
      (fun _ ↦ hsol.regularity.vorticity_time_differentiableAt ht)
      (fun _ ↦ hother.regularity.vorticity_time_differentiableAt ht)
      (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
        (f := fun x s ↦ fields.vorticity x s - other.vorticity x s)
        (hf.sub hg) ht (-L) L)
      (fun x ↦ by simpa only [one_mul] using hsol.transport (x := x) ht)
      (fun x ↦ by simpa only [one_mul] using hother.transport (x := x) ht)
      (vorticity_eq_of_not_mem_Ioo hsupp (by simp))
      (vorticity_eq_of_not_mem_Ioo hsupp (by simp))
  rw [hrate]
  exact norm_add_mul_le_of_norm_le (differenceEnergy_nonneg fields other L t)
    (norm_integral_coupled_terms_le_of_deriv_L2 hv' hw hpair (sub_eq_zero.mpr hzero)
      (fun x hx ↦ sub_eq_zero.mpr
        (vorticity_eq_of_not_mem_Ioo hsupp fun h ↦ hx ⟨h.1.le, h.2.le⟩)) hbound hderivLp
      hderivBound)

end DeGregorio
