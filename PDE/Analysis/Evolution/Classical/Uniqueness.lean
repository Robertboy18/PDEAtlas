/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniqueness of continuous representatives on a closed cylinder

Almost-everywhere agreement of spatial slices at almost every interior time
determines a continuous function on the entire closed cylinder. Spatial
continuity first supplies the closure values at almost every time; time
continuity then supplies every time, including the endpoints.
-/

@[expose] public section

open MeasureTheory Set PDE.Common

namespace PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Let `Ω` be open and let `f`, `g` be continuous on `closure Ω × [a, b]`. If for almost
every `t ∈ (a, b)` the slices `f(·, t)` and `g(·, t)` agree almost everywhere on `Ω`, then
`f = g` on all of `closure Ω × [a, b]`. -/
theorem eqOn_closed_cylinder_of_ae_eq
    {f g : ℝ^n × ℝ → Y} (hΩ : IsOpen Ω) (hab : a < b)
    (hf : ContinuousOn f (closure Ω ×ˢ Icc a b))
    (hg : ContinuousOn g (closure Ω ×ˢ Icc a b))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ f (x, t)) =ᵐ[volume.restrict Ω] fun x ↦ g (x, t)) :
    EqOn f g (closure Ω ×ˢ Icc a b) := by
  have hslices : ∀ᵐ t ∂volume.restrict (Ioo a b),
      EqOn (fun x ↦ f (x, t)) (fun x ↦ g (x, t)) (closure Ω) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htmem
    have hfc : ContinuousOn (fun x ↦ f (x, t)) (closure Ω) :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hx ↦ ⟨hx, Ioo_subset_Icc_self htmem⟩)
    have hgc : ContinuousOn (fun x ↦ g (x, t)) (closure Ω) :=
      hg.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hx ↦ ⟨hx, Ioo_subset_Icc_self htmem⟩)
    exact (Measure.eqOn_open_of_ae_eq ht hΩ (hfc.mono subset_closure)
      (hgc.mono subset_closure)).of_subset_closure hfc hgc subset_closure Subset.rfl
  intro p hp
  have heq : (fun t ↦ f (p.1, t)) =ᵐ[volume.restrict (Icc a b)]
      fun t ↦ g (p.1, t) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hslices.mono fun t ht ↦ ht hp.1
  exact Measure.eqOn_Icc_of_ae_eq volume hab.ne heq
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hp.1, ht⟩))
    (hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht ↦ ⟨hp.1, ht⟩))
    hp.2

/-- The same uniqueness principle in canonical Euclidean spacetime coordinates. -/
theorem eqOn_closed_spaceTime_cylinder_of_ae_eq
    {f g : SpaceTime n → Y} (hΩ : IsOpen Ω) (hab : a < b)
    (hf : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    (hg : ContinuousOn g (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ f (timeSpaceCons t x)) =ᵐ[volume.restrict Ω]
        fun x ↦ g (timeSpaceCons t x)) :
    EqOn f g (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  have hj : ContinuousOn (joinSpaceTime (n := n)) (closure Ω ×ˢ Icc a b) :=
    (spaceTimeContinuousLinearEquiv n).symm.continuous.continuousOn
  have hf' : ContinuousOn (fun p ↦ f (joinSpaceTime p)) (closure Ω ×ˢ Icc a b) :=
    hf.comp hj (by intro p hp; simpa using hp)
  have hg' : ContinuousOn (fun p ↦ g (joinSpaceTime p)) (closure Ω ×ˢ Icc a b) :=
    hg.comp hj (by intro p hp; simpa using hp)
  have heq := eqOn_closed_cylinder_of_ae_eq hΩ hab hf' hg' hae
  intro z hz
  simpa only [join_splitSpaceTime] using heq hz

end PDE.Analysis.Evolution
