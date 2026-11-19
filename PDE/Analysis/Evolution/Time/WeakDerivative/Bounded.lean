/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative

/-!
# Lipschitz time traces from bounded weak derivatives

Weak continuity fixes the values of a curve at every time, including the endpoints.
Its integrable weak derivative therefore gives the fundamental theorem for those
same values. An almost everywhere bound on that derivative then gives a Lipschitz
bound in the original Banach norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Weak continuity identifies the original curve with its continuous representative,
so its Bochner fundamental theorem also holds at the prescribed endpoint values. -/
theorem integral_eq_sub_of_weaklyContinuousOn
    {a b : ℝ} (hab : a < b) {u g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hu : ∀ ell : StrongDual ℝ X, ContinuousOn (fun t ↦ ell (u t)) (Icc a b))
    (hg : IntegrableOn g (Ioo a b))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ r in s..t, g r) = u t - u s := by
  obtain ⟨v, hv, hae, hFTC⟩ := hweak.exists_continuous_representative_Icc hab hg
  have heq (r : ℝ) (hr : r ∈ Icc a b) : u r = v r := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ell
    have hell : (fun q ↦ ell (u q)) =ᵐ[volume.restrict (Icc a b)]
        fun q ↦ ell (v q) := by
      filter_upwards [(ae_restrict_congr_set Ioo_ae_eq_Icc).mp hae] with q hq
      rw [hq]
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne hell (hu ell)
      (ell.continuous.comp hv).continuousOn hr
  rw [heq t ht, heq s hs]
  exact (hFTC s hs t ht).symm

/-- A bounded weak time derivative makes the original weakly continuous curve
Lipschitz in norm, with the same derivative bound and no loss at the endpoints. -/
theorem lipschitzOnWith_of_weaklyContinuousOn
    {a b : ℝ} (hab : a < b) {u g : ℝ → X} {K : ℝ≥0}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g)
    (hu : ∀ ell : StrongDual ℝ X, ContinuousOn (fun t ↦ ell (u t)) (Icc a b))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖g t‖ ≤ K) :
    LipschitzOnWith K u (Icc a b) := by
  have hg : IntegrableOn g (Ioo a b) :=
    Integrable.of_bound hweak.locallyIntegrable_g.aestronglyMeasurable
      K hbound
  have hboundcc : ∀ᵐ t ∂volume.restrict (Icc a b), ‖g t‖ ≤ K :=
    (ae_restrict_congr_set Ioo_ae_eq_Icc).mp hbound
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, ← hweak.integral_eq_sub_of_weaklyContinuousOn hab hu hg ht hs]
  have hinterval : ∀ᵐ r ∂volume, r ∈ uIoc t s → ‖g r‖ ≤ K := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hboundcc] with r hr hrt
    exact hr (uIcc_subset_Icc ht hs (uIoc_subset_uIcc hrt))
  simpa only [Real.dist_eq] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hinterval

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
