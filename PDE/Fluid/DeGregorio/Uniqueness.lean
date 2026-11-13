/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness.Evolution
import PDE.Fluid.DeGregorio.Characteristics.Local
import Mathlib.Analysis.ODE.Gronwall

/-!
# Coupled uniqueness for compact classical De Gregorio solutions

Two jointly `C¹` solutions of the equation with `a = 1`, a common bounded support enclosure, the
same initial vorticity, and normalized velocity coincide throughout a closed time interval
(`IsClassicalSolutionOn.eq_of_same_initialData`). The same holds for the rescaled equation when both
solutions use the same rates, continuous on the closed time interval
(`IsClassicalRescaledSolutionOn.eq_of_same_initialData`).

Existence in the supported H² class is `Iteration.exists_hkCurve_local_solution`.

## How it works

We show that the energy of the difference, `differenceEnergy`, the integral of `(ω - ω')²` over the
support enclosure `[-L, L]`, vanishes (`differenceEnergy_eq_zero_of_same_initialData_of_rescaled`).
Compactness of `[-L, L] × [t₀, T]` bounds the coefficients, including the additional coefficient
`2 cw + cl` of the rescaled equation. With these bounds the coupled PDE and the concrete spectral
Hilbert transform give the energy inequality `|E'| ≤ K E`
(`norm_deriv_differenceEnergy_le_of_rescaled`), and since `E(t₀) = 0`, Grönwall's theorem in the
form `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` of Mathlib gives `E = 0`. Equal
vorticities then give equal velocities through the Hilbert relation and the normalization at the
origin (`fields_eq_of_differenceEnergy_eq_zero`). The argument is written for the rescaled equation;
the physical equation is the case of zero rates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ContDiff

namespace DeGregorio

/-- Equal initial vorticity gives zero difference energy for two rescaled
solutions with the same continuous rates. All coefficient bounds are derived
from continuity on the compact spacetime rectangle. -/
theorem differenceEnergy_eq_zero_of_same_initialData_of_rescaled {fields other : Fields}
    {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Icc t₀ T))
    (hother : IsClassicalRescaledSolutionOn 1 other cl cw (Icc t₀ T))
    (hcl : ContinuousOn cl (Icc t₀ T)) (hcw : ContinuousOn cw (Icc t₀ T))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = other.velocity 0 t)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀) :
    ∀ t ∈ Icc t₀ T, differenceEnergy fields other L t = 0 := by
  have hrate : ContinuousOn (fun p : ℝ × ℝ ↦ 2 * cw p.2 + cl p.2)
      (Icc (-L) L ×ˢ Icc t₀ T) :=
    ((continuousOn_const.mul hcw).add hcl).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦
      (deriv (fun y ↦ fields.velocity y p.2) p.1,
        (other.vorticity p.1 p.2,
          (deriv (fun y ↦ other.vorticity y p.2) p.1, 2 * cw p.2 + cl p.2))))
      (Icc (-L) L ×ˢ Icc t₀ T) :=
    (continuous_spatial_deriv_of_contDiff hu).continuousOn.prodMk
      (hg.continuous.continuousOn.prodMk
        ((continuous_spatial_deriv_of_contDiff hg).continuousOn.prodMk hrate))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (t : ℝ) (ht : t ∈ Icc t₀ T) (x : ℝ) (hx : x ∈ Icc (-L) L) :
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C ∧ |2 * cw t + cl t| ≤ C := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using
      (hB (x, t) ⟨hx, ht⟩).trans (le_max_left B 0)
  have hdiff : Differentiable ℝ (differenceEnergy fields other L) :=
    fun t ↦ (hasDerivAt_differenceEnergy hf hg L t).differentiableAt
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hdiff.continuous.continuousOn
    (fun t _ ↦ (hdiff t).hasDerivAt.hasDerivWithinAt)
    (K := (6 + 2 * L ^ 2) * C + C)
  · simp only [differenceEnergy, hinitial, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
  · intro t ht
    have ht' : t ∈ Icc t₀ T := ⟨ht.1, ht.2.le⟩
    rw [Real.norm_eq_abs (differenceEnergy fields other L t),
      abs_of_nonneg (differenceEnergy_nonneg fields other L t)]
    apply (norm_deriv_differenceEnergy_le_of_rescaled hf hg hu hv hsol hother ht' hL hC
      (hsupp t ht') (hzero t ht') (fun x hx ↦
        ⟨(hbound t ht' x hx).1, (hbound t ht' x hx).2.1,
          (hbound t ht' x hx).2.2.1⟩)).trans
    exact mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (hbound t ht' 0 ⟨neg_nonpos.mpr hL, hL⟩).2.2.2)
      (differenceEnergy_nonneg fields other L t)

/-- Coupled uniqueness for normalized compact classical rescaled solutions with
the same prescribed continuous rates. Equality includes the velocity recovered
through the concrete Hilbert relation and normalization at the origin. -/
theorem IsClassicalRescaledSolutionOn.eq_of_same_initialData {fields other : Fields}
    {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Icc t₀ T))
    (hother : IsClassicalRescaledSolutionOn 1 other cl cw (Icc t₀ T))
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hcl : ContinuousOn cl (Icc t₀ T)) (hcw : ContinuousOn cw (Icc t₀ T))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Icc t₀ T,
      fields.velocity 0 t = 0 ∧ other.velocity 0 t = 0)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀) :
    ∀ t ∈ Icc t₀ T, ∀ x,
      fields.vorticity x t = other.vorticity x t ∧
        fields.velocity x t = other.velocity x t := by
  have hzero (t : ℝ) (ht : t ∈ Icc t₀ T) :
      fields.velocity 0 t = other.velocity 0 t :=
    (hnormalized t ht).1.trans (hnormalized t ht).2.symm
  have henergy := differenceEnergy_eq_zero_of_same_initialData_of_rescaled
    hf hg hu hv hsol hother hcl hcw hL hsupp hzero hinitial
  intro t ht
  exact fields_eq_of_differenceEnergy_eq_zero
    (hf.comp (contDiff_id.prodMk contDiff_const)) (hg.comp (contDiff_id.prodMk contDiff_const))
    (hu.comp (contDiff_id.prodMk contDiff_const)) (hv.comp (contDiff_id.prodMk contDiff_const))
    hsol hother ht (hsupp t ht) (hzero t ht) (henergy t ht)

/-- The difference energy of two compact classical solutions with the same data
vanishes. This is the zero-rate case of the rescaled statement. -/
theorem differenceEnergy_eq_zero_of_same_initialData {fields other : Fields}
    {t₀ T L : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hsol : IsClassicalSolutionOn 1 fields (Icc t₀ T))
    (hother : IsClassicalSolutionOn 1 other (Icc t₀ T))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hzero : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = other.velocity 0 t)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀) :
    ∀ t ∈ Icc t₀ T, differenceEnergy fields other L t = 0 :=
  differenceEnergy_eq_zero_of_same_initialData_of_rescaled hf hg hu hv hsol.toRescaled
    hother.toRescaled continuousOn_const continuousOn_const hL hsupp hzero hinitial

/-- Coupled uniqueness on a closed time interval for jointly `C¹` classical
solutions supported in a common bounded open spatial interval. Both velocities
are normalized to vanish at the origin. The conclusion includes the velocity,
using the concrete Hilbert relation and its normalized primitive estimate. -/
theorem IsClassicalSolutionOn.eq_of_same_initialData {fields other : Fields}
    {t₀ T L : ℝ}
    (hsol : IsClassicalSolutionOn 1 fields (Icc t₀ T))
    (hother : IsClassicalSolutionOn 1 other (Icc t₀ T))
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L →
      fields.vorticity x t = 0 ∧ other.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Icc t₀ T,
      fields.velocity 0 t = 0 ∧ other.velocity 0 t = 0)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀) :
    ∀ t ∈ Icc t₀ T, ∀ x,
      fields.vorticity x t = other.vorticity x t ∧
        fields.velocity x t = other.velocity x t :=
  hsol.toRescaled.eq_of_same_initialData hother.toRescaled hf hg hu hv continuousOn_const
    continuousOn_const hL hsupp hnormalized hinitial

end DeGregorio
