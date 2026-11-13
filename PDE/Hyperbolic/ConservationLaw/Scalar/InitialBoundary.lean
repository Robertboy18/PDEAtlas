/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialValue
import PDE.Analysis.Integration.CompactSupportLimit

/-!
# Boundary pairings for conservation-law initial traces

A strong local `L¹` trace controls pairings with compact spacetime tests as time
approaches zero from above. The test may depend on time: its compact support gives
a common spatial interval, and continuity identifies the initial slice.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw

namespace Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strong local `L¹` convergence controls the trace error paired with a time-dependent
compact spacetime test. -/
theorem HasInitialTraceLocallyL1.tendsto_integral_test_smul_sub {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) (φ : InitialValueTestFunction) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • (u !₂[t, x] - u₀ x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR⟩ := φ.exists_spatial_support_interval
  obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  exact tendsto_integral_smul_zero_of_tendsto_integral_norm
    (hu.eventually_integrableOn_sub (-R) R) hR (Eventually.of_forall fun t x ↦ hC !₂[t, x])
    (hu.tendsto_setIntegral_norm_sub (-R) R)

/-- Pairing an initial state with the time slices of a compact spacetime test is continuous
at the initial time. -/
theorem tendsto_integral_initialState_test_smul {u₀ : ℝ → E} (hu₀ : LocallyIntegrable u₀ volume)
    (φ : InitialValueTestFunction) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • u₀ x) (𝓝 0) (𝓝 (∫ x : ℝ, φ !₂[0, x] • u₀ x)) := by
  obtain ⟨R, hR⟩ := φ.exists_spatial_support_interval
  obtain ⟨C, hC⟩ := φ.contDiff.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hI := hu₀.integrableOn_isCompact (k := Icc (-R) R) isCompact_Icc
  have heq (t : ℝ) : (∫ x : ℝ, φ !₂[t, x] • u₀ x) =
        ∫ x : ℝ in Icc (-R) R, φ !₂[t, x] • u₀ x := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    simp [hR t x hx]
  simp_rw [heq]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖u₀ x‖)
  · filter_upwards with t
    exact ((φ.contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable).smul
      hI.aestronglyMeasurable
  · filter_upwards with t
    filter_upwards with x
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · exact hI.norm.const_mul C
  · filter_upwards with x
    exact ((φ.contDiff.continuous.comp (by fun_prop)).tendsto 0).smul_const (u₀ x)

/-- A strong local `L¹` initial trace gives the boundary pairing for every compact
spacetime test, including tests whose time derivative is nonzero at the boundary. -/
theorem HasInitialTraceLocallyL1.tendsto_integral_test_smul {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) (φ : InitialValueTestFunction) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • u !₂[t, x])
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, φ !₂[0, x] • u₀ x)) := by
  have hlim := (hu.tendsto_integral_test_smul_sub φ).add
    ((tendsto_integral_initialState_test_smul hu.initial_locallyIntegrable φ).mono_left
      nhdsWithin_le_nhds)
  simp only [zero_add] at hlim
  apply hlim.congr' ?_
  obtain ⟨R, hR⟩ := φ.exists_spatial_support_interval
  have hI₀ := hu.initial_locallyIntegrable.integrableOn_isCompact (k := Icc (-R) R) isCompact_Icc
  filter_upwards [hu.eventually_integrableOn_sub (-R) R] with t ht
  have heq (v : ℝ → E) : (∫ x : ℝ, φ !₂[t, x] • v x) =
        ∫ x : ℝ in Icc (-R) R, φ !₂[t, x] • v x := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    simp [hR t x hx]
  rw [heq, heq, heq]
  have hφ : Continuous (fun x : ℝ ↦ φ !₂[t, x]) :=
    φ.contDiff.continuous.comp (by fun_prop)
  rw [← integral_add (ht.continuousOn_smul hφ.continuousOn isCompact_Icc)
    (hI₀.continuousOn_smul hφ.continuousOn isCompact_Icc)]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ ↦ ?_
  simp only [← smul_add, sub_add_cancel]

end Scalar
end PDE.Hyperbolic.ConservationLaw
