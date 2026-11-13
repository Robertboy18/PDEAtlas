/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness
public import PDE.Fluid.DeGregorio.Reflection
import PDE.Analysis.Calculus.SpaceTimeScalar

/-!
# Preservation of oddness by the coupled equation

For the compact classical uniqueness class, odd initial vorticity and the
normalization `u(0,t)=0` imply oddness of both evolving fields. The comparison
solution is the signed reflection, whose PDE and spectral Biot–Savart
relation are proved in `PDE.Fluid.DeGregorio.Reflection`.

The same argument applies to the rescaled equation when both rates are
prescribed and continuous on the time interval.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace DeGregorio

/-- A symmetric support enclosure also contains the reflected vorticity. -/
theorem reflectedFields_vorticity_eq_zero_outside {fields : Fields} {L t : ℝ}
    (hsupp : ∀ x, x ∉ Ioo (-L) L → fields.vorticity x t = 0) :
    ∀ x, x ∉ Ioo (-L) L → (reflectedFields fields).vorticity x t = 0 := by
  intro x hx
  have hxneg : -x ∉ Ioo (-L) L := by
    intro hy
    apply hx
    exact ⟨by simpa only [neg_neg] using neg_lt_neg hy.2,
      by simpa only [neg_neg] using neg_lt_neg hy.1⟩
  simp only [reflectedFields, hsupp (-x) hxneg, neg_zero]

/-- Odd initial vorticity stays odd for a jointly `C¹` classical solution with
`u(0, t) = 0` and vorticity supported in a fixed interval `(-L, L)`. The velocity is
odd as well. -/
theorem IsClassicalSolutionOn.odd_of_odd_initialData {fields : Fields} {t₀ T L : ℝ}
    (hsol : IsClassicalSolutionOn 1 fields (Icc t₀ T))
    (hω : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L → fields.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = 0)
    (hinitial : Function.Odd (fun x ↦ fields.vorticity x t₀)) :
    ∀ t ∈ Icc t₀ T,
      Function.Odd (fun x ↦ fields.vorticity x t) ∧
        Function.Odd (fun x ↦ fields.velocity x t) := by
  have hcompare := hsol.eq_of_same_initialData hsol.reflectedFields
    hω (PDE.Analysis.Calculus.contDiff_neg_reflect hω)
    hu (PDE.Analysis.Calculus.contDiff_neg_reflect hu) hL
    (fun t ht x hx ↦ ⟨hsupp t ht x hx,
      reflectedFields_vorticity_eq_zero_outside (hsupp t ht) x hx⟩)
    (fun t ht ↦ ⟨hnormalized t ht, by
      simp only [DeGregorio.reflectedFields, neg_zero, hnormalized t ht]⟩)
    (fun x ↦ by simpa only [DeGregorio.reflectedFields, neg_neg] using hinitial (-x))
  intro t ht
  exact ⟨fun x ↦ by
    simpa only [DeGregorio.reflectedFields, neg_neg] using (hcompare t ht (-x)).1,
    fun x ↦ by
    simpa only [DeGregorio.reflectedFields, neg_neg] using (hcompare t ht (-x)).2⟩

/-- Odd initial vorticity gives odd rescaled vorticity and velocity for the
compact normalized classical class, with prescribed continuous rates. The
reflection uses the same rates, so coupled uniqueness supplies the conclusion. -/
theorem IsClassicalRescaledSolutionOn.odd_of_odd_initialData {fields : Fields}
    {cl cw : ℝ → ℝ} {t₀ T L : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Icc t₀ T))
    (hω : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hcl : ContinuousOn cl (Icc t₀ T)) (hcw : ContinuousOn cw (Icc t₀ T))
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, ∀ x, x ∉ Ioo (-L) L → fields.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = 0)
    (hinitial : Function.Odd (fun x ↦ fields.vorticity x t₀)) :
    ∀ t ∈ Icc t₀ T,
      Function.Odd (fun x ↦ fields.vorticity x t) ∧
        Function.Odd (fun x ↦ fields.velocity x t) := by
  have hcompare := hsol.eq_of_same_initialData hsol.reflectedFields
    hω (PDE.Analysis.Calculus.contDiff_neg_reflect hω)
    hu (PDE.Analysis.Calculus.contDiff_neg_reflect hu) hcl hcw hL
    (fun t ht x hx ↦ ⟨hsupp t ht x hx,
      reflectedFields_vorticity_eq_zero_outside (hsupp t ht) x hx⟩)
    (fun t ht ↦ ⟨hnormalized t ht, by
      simp only [DeGregorio.reflectedFields, neg_zero, hnormalized t ht]⟩)
    (fun x ↦ by simpa only [DeGregorio.reflectedFields, neg_neg] using hinitial (-x))
  intro t ht
  exact ⟨fun x ↦ by
    simpa only [DeGregorio.reflectedFields, neg_neg] using (hcompare t ht (-x)).1,
    fun x ↦ by
    simpa only [DeGregorio.reflectedFields, neg_neg] using (hcompare t ht (-x)).2⟩

end DeGregorio
