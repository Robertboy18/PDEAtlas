/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.DistributionTheory.TestFunction.TensorProduct

/-!
# Initial traces of continuous conservation-law fields

Continuity on the closed forward half-space gives the strong local `L¹` initial
trace used by the time-cutoff theorem. Compact spacetime rectangles provide the dominators.

The initial term in the full weak formulation determines the initial datum
almost everywhere. Extending arbitrary smooth spatial tests across time zero
allows Mathlib's vector-valued fundamental lemma to identify that datum.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw

variable {E : Type*} [NormedAddCommGroup E] {u : ℝ^2 → E}

/-- Continuity up to time zero gives the strong local `L¹` trace equal to the
time-zero slice. Compact spatial intervals suffice, without a global bound. -/
theorem Scalar.hasInitialTraceLocallyL1_of_continuousOn (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    Scalar.HasInitialTraceLocallyL1 u (fun x ↦ u !₂[0, x]) := by
  have hslice (t : ℝ) (ht : 0 ≤ t) : Continuous (fun x : ℝ ↦ u !₂[t, x]) :=
    hu.comp_continuous (by fun_prop) (fun x ↦ by simpa using ht)
  apply Scalar.hasInitialTraceLocallyL1_of_dominated (hslice 0 le_rfl).locallyIntegrable
  · intro a b
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hslice t ht.le).sub (hslice 0 le_rfl)).aestronglyMeasurable
  · intro a b
    have hc : ContinuousOn (fun p : ℝ × ℝ ↦ u !₂[p.1, p.2] - u !₂[0, p.2])
        (Icc (0 : ℝ) 1 ×ˢ Icc a b) :=
      (hu.comp (by fun_prop) (fun p hp ↦ by simpa using hp.1.1)).sub
        (((hslice 0 le_rfl).comp continuous_snd).continuousOn)
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
    refine ⟨fun _ ↦ C, integrableOn_const isCompact_Icc.measure_ne_top, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC (t, x) ⟨⟨ht.le, ht1.le⟩, hx⟩
  · filter_upwards [] with x
    have hc : ContinuousOn (fun t : ℝ ↦ u !₂[t, x]) (Ici 0) :=
      hu.comp (by fun_prop) (fun t ht ↦ by simpa using ht)
    exact (hc 0 le_rfl).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- Changing the initial datum almost everywhere preserves a strong local
`L¹` trace, including the eventual integrability of its error. -/
theorem Scalar.HasInitialTraceLocallyL1.congr_initial_ae {g h : ℝ → E}
    (htrace : Scalar.HasInitialTraceLocallyL1 u g) (hgh : g =ᵐ[volume] h) :
    Scalar.HasInitialTraceLocallyL1 u h := by
  refine ⟨htrace.initial_locallyIntegrable.congr hgh, fun a b ↦ ?_⟩
  have heq (t : ℝ) : (fun x ↦ u !₂[t, x] - g x) =ᵐ[volume.restrict (Icc a b)]
        fun x ↦ u !₂[t, x] - h x := by
    filter_upwards [ae_restrict_of_ae hgh] with x hx
    rw [hx]
  refine ⟨(htrace.eventually_integrableOn_sub a b).mono (fun t ht ↦ ht.congr (heq t)), ?_⟩
  have hintegral : (fun t ↦ ∫ x in Icc a b, ‖u !₂[t, x] - g x‖) =
        fun t ↦ ∫ x in Icc a b, ‖u !₂[t, x] - h x‖ :=
    funext fun t ↦ integral_congr_ae ((heq t).fun_comp norm)
  rw [← hintegral]
  exact htrace.tendsto_setIntegral_norm_sub a b

/-- Continuity on the closed half-space gives local integrability for the
positive-time restricted measure, also in neighborhoods of the initial face. -/
theorem locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn
    (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    LocallyIntegrable u (volume.restrict forwardHalfSpace) := by
  have hclosed : IsClosed {p : ℝ^2 | 0 ≤ p 0} :=
    isClosed_le continuous_const (EuclideanSpace.proj 0).continuous
  exact ((locallyIntegrableOn_iff_locallyIntegrable_restrict hclosed).mp
    (hu.locallyIntegrableOn hclosed.measurableSet)).mono_measure
      (volume.restrict_mono_set (fun p hp ↦ show 0 ≤ p 0 from le_of_lt hp))

/-- Every smooth compact spatial test is the initial slice of an admissible
spacetime test, obtained by tensoring with a time bump equal to one at zero. -/
theorem InitialValueTestFunction.exists_initialSlice_eq {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∃ φ : InitialValueTestFunction, ∀ x : ℝ, φ !₂[0, x] = ψ x := by
  let b : ContDiffBump (0 : ℝ) := default
  let β : 𝓓((⊤ : Opens ℝ), ℝ) := .mk b b.contDiff b.hasCompactSupport (subset_univ _)
  let χ : 𝓓((⊤ : Opens ℝ), ℝ) := .mk ψ hψ hc (subset_univ _)
  let e : ℝ^2 ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let Φ := TestFunction.precompProper e e.contDiff e.toHomeomorph.isProperMap
    (TestFunction.tensorProduct β χ)
  refine ⟨.mk Φ (Φ.contDiff.of_le (by simp)) Φ.hasCompactSupport (subset_univ _), fun x ↦ ?_⟩
  change b 0 * ψ x = ψ x
  simp [b.eventuallyEq_one.self_of_nhds]

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- For a fixed spacetime field, the full weak identity determines the
prescribed initial datum almost everywhere. The proof uses the fundamental
lemma on arbitrary smooth compact spatial tests. -/
theorem IsWeakInitialValueSolution.initial_ae_eq {flux : E → E} {g h : ℝ → E}
    (hg : IsWeakInitialValueSolution flux g u) (hh : IsWeakInitialValueSolution flux h u) :
    g =ᵐ[volume] h := by
  apply ae_eq_of_integral_contDiff_smul_eq hg.initial_locallyIntegrable hh.initial_locallyIntegrable
  intro ψ hψ hc
  obtain ⟨φ, hφ⟩ := InitialValueTestFunction.exists_initialSlice_eq hψ hc
  have heq := add_left_cancel ((hg.weak_initial_eq φ).trans (hh.weak_initial_eq φ).symm)
  simpa only [hφ] using heq

/-- For a field continuous up to time zero and a continuous flux, the initial
datum in the weak formulation equals the time-zero slice almost
everywhere. The time-cutoff theorem constructs the comparison identity. -/
theorem IsWeakInitialValueSolution.initial_ae_eq_slice {flux : E → E} {g : ℝ → E}
    (hweak : IsWeakInitialValueSolution flux g u) (hflux : Continuous flux)
    (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    g =ᵐ[volume] fun x ↦ u !₂[0, x] := by
  apply hweak.initial_ae_eq
  exact isWeakInitialValueSolution_of_interior_of_initialTrace
    (locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn hu)
    (locallyIntegrable_restrict_forwardHalfSpace_of_continuousOn (hflux.comp_continuousOn hu))
    (Scalar.hasInitialTraceLocallyL1_of_continuousOn hu) hweak.interior_identity

/-- A continuous weak Cauchy solution attains its prescribed initial datum
strongly in local `L¹`. The initial trace follows from the full weak identity
and boundary continuity; it is not an additional assumption. -/
theorem IsWeakInitialValueSolution.hasInitialTraceLocallyL1_of_continuousOn {flux : E → E}
    {g : ℝ → E} (hweak : IsWeakInitialValueSolution flux g u) (hflux : Continuous flux)
    (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    Scalar.HasInitialTraceLocallyL1 u g :=
  (Scalar.hasInitialTraceLocallyL1_of_continuousOn hu).congr_initial_ae
    (hweak.initial_ae_eq_slice hflux hu).symm

end PDE.Hyperbolic.ConservationLaw
