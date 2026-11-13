/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Contraction

/-!
# Uniqueness of bounded scalar entropy solutions

Local contraction on a countable family of expanding initial intervals gives equality
of spatial slices for almost every positive time. Fubini then gives equality almost
everywhere in spacetime. Exceptional time slices of arbitrary representatives remain
unconstrained.

`IsEntropySolutionWithInitialTrace.unique_ae` is Evans, §11.4.3, Theorem 3, for uniformly
essentially bounded entropy solutions with a `C¹` flux and a strong local `L¹` initial trace,
in place of Evans's class `C([0, ∞), L¹(ℝ)) ∩ L^∞` with a smooth flux. Step 5 of Evans's
proof draws the conclusion from the global contraction (50) instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, the definition of entropy solution and
  Theorem 3, with steps 4-5 of its proof, equation (50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

namespace Kruzhkov

/-- The time-space equivalence also preserves measure on positive time. -/
theorem measurePreserving_spaceTimePair_positive :
    MeasurePreserving spaceTimePair ((volume.restrict (Ioi (0 : ℝ))).prod volume)
      (volume.restrict forwardHalfSpace) := by
  have h := measurePreserving_spaceTimePair.restrict_preimage forwardHalfSpace.isOpen.measurableSet
  simpa only [preimage_forwardHalfSpace, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

/-- Almost-everywhere equality on almost every positive-time slice implies spacetime equality.
Measurability is essential for this converse direction of Fubini. -/
theorem ae_eq_of_ae_slice {u v : ℝ^2 → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict forwardHalfSpace))
    (hv : AEStronglyMeasurable v (volume.restrict forwardHalfSpace))
    (h : ∀ᵐ T : ℝ, 0 < T → (fun x : ℝ ↦ u !₂[T, x]) =ᵐ[volume] (fun x : ℝ ↦ v !₂[T, x])) :
    u =ᵐ[volume.restrict forwardHalfSpace] v := by
  have hp := measurePreserving_spaceTimePair_positive
  have hu' := hu.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have hv' := hv.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have hm : hu'.mk (u ∘ spaceTimePair) =ᵐ[(volume.restrict (Ioi (0 : ℝ))).prod volume]
      hv'.mk (v ∘ spaceTimePair) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hu'.stronglyMeasurable_mk.measurable
        hv'.stronglyMeasurable_mk.measurable)).2
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).2 h, Measure.ae_ae_of_ae_prod hu'.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hv'.ae_eq_mk] with t ht hut hvt
    filter_upwards [ht, hut, hvt] with x hx hux hvx
    simpa only [Function.comp_apply, spaceTimePair_apply] using hux.symm.trans (hx.trans hvx)
  have heq := hu'.ae_eq_mk.trans (hm.trans hv'.ae_eq_mk.symm)
  have hback := (MeasurePreserving.symm spaceTimePair hp).quasiMeasurePreserving.ae heq
  change ∀ᵐ p ∂volume.restrict forwardHalfSpace, u p = v p
  simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using hback

end Kruzhkov

open Kruzhkov

/-- Two uniformly essentially bounded entropy solutions with the same strong initial trace
agree in space almost everywhere at almost every positive time. -/
theorem IsEntropySolutionWithInitialTrace.unique_slice_ae {flux : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    {u₀ : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux u₀ v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) :
    ∀ᵐ T : ℝ, 0 < T → (fun x : ℝ ↦ u !₂[T, x]) =ᵐ[volume] (fun x : ℝ ↦ v !₂[T, x]) := by
  obtain ⟨c, _, hc⟩ := hu.exists_local_l1_contraction_ae hv hf hbu hbv
  have hui := locallyIntegrable_of_ae_bound
    hu.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbu
  have hvi := locallyIntegrable_of_ae_bound
    hv.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbv
  have hN := ae_all_iff.mpr (fun N : ℕ ↦ hc (-(N : ℝ)) N)
  filter_upwards [hN, ae_locallyIntegrable_slice hui, ae_locallyIntegrable_slice hvi]
    with T hT hut hvt hpos
  have heq (N : ℕ) : ∀ᵐ x : ℝ, x ∈ Icc (-(N : ℝ) + c * T) (N - c * T) →
      u !₂[T, x] = v !₂[T, x] := by
    have hi := (((hut hpos).integrableOn_isCompact
      (isCompact_Icc (a := -(N : ℝ) + c * T) (b := N - c * T))).sub
        ((hvt hpos).integrableOn_isCompact isCompact_Icc)).norm
    have hzero : (∫ x : ℝ in Icc (-(N : ℝ) + c * T) (N - c * T),
        |u !₂[T, x] - v !₂[T, x]|) = 0 := by
      apply le_antisymm
      · simpa using hT N hpos
      · exact integral_nonneg (fun _ ↦ abs_nonneg _)
    have hz := (integral_eq_zero_iff_of_nonneg (fun _ ↦ abs_nonneg _) hi).1 hzero
    apply (ae_restrict_iff' measurableSet_Icc).1
    filter_upwards [hz] with x hx using sub_eq_zero.mp (abs_eq_zero.mp hx)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| + |c * T|)
  apply hx N
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self (c * T), neg_abs_le (c * T)]

/-- Uniformly essentially bounded scalar entropy solutions with the same strong local `L¹`
initial trace are equal almost everywhere on positive spacetime. -/
theorem IsEntropySolutionWithInitialTrace.unique_ae {flux : ℝ → ℝ} {u v : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux u₀ v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) :
    u =ᵐ[volume.restrict forwardHalfSpace] v :=
  ae_eq_of_ae_slice hu.interior.weak.u_locallyIntegrable.aestronglyMeasurable
    hv.interior.weak.u_locallyIntegrable.aestronglyMeasurable (hu.unique_slice_ae hv hf hbu hbv)

end PDE.Hyperbolic.ConservationLaw.Scalar
