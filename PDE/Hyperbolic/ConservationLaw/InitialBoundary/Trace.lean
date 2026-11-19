/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff
public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundary
public import PDE.Analysis.Integration.LocallyBounded
import PDE.Analysis.Integration.CompactPairing
import PDE.DistributionTheory.TestFunction

/-!
# From strong initial traces to the initial weak equation

The positive-time cutoff isolates the initial face. Its derivative converges
to the strong local `L¹` trace in compact test pairings, for any Banach-valued
conserved density. Integrability for the restricted measure controls the
initial face as well as the open positive-time region.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology InnerProductSpace

namespace PDE.Hyperbolic.ConservationLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An interior equation with a strong local `L¹` trace satisfies the direct
initial-boundary identity for independent Banach-valued density and flux fields. -/
theorem initialWeak_eq_zero_of_interior_of_initialTrace {u q : ℝ^2 → E} {g : ℝ → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (htrace : Scalar.HasInitialTraceLocallyL1 u g)
    (hweak : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ), ∫ p : ℝ^2, InteriorWeakForm.integrand u q φ p = 0)
    (φ : InitialValueTestFunction) :
    (∫ p in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) +
      ∫ x : ℝ, φ !₂[0, x] • g x = 0 := by
  have hI := integrableOn_initialWeakIntegrand hu hq φ
  have hlim := (tendsto_integral_initialTimeCutoff_smul hI).add
    (tendsto_integral_derivCutoff_test_smul hu φ (htrace.tendsto_integral_test_smul φ))
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hi : (∫ p : ℝ^2 in forwardHalfSpace,
        InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) p) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hweak _
    · intro p hp
      simp only [InteriorWeakForm.integrand,
        (interiorCutoffTest φ hε).partialDeriv_eq_zero_of_notMem hp, zero_smul, add_zero]
  have hform : InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) =
      fun p ↦ initialTimeCutoff ε (p 0) • InteriorWeakForm.integrand u q φ p +
        deriv (initialTimeCutoff ε) (p 0) • (φ p • u p) :=
    funext (integrand_interiorCutoffTest u q φ hε)
  rw [hform, integral_add (integrableOn_initialTimeCutoff_smul hI ε)
    (integrableOn_derivCutoff_test_smul hu φ ε)] at hi
  exact hi.symm

/-- The interior equation and strong initial trace construct the weak
initial-value predicate. -/
theorem isWeakInitialValueSolution_of_interior_of_initialTrace
    {flux : E → E} {u : ℝ^2 → E} {g : ℝ → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hf : LocallyIntegrable (fun p ↦ flux (u p)) (volume.restrict forwardHalfSpace))
    (htrace : Scalar.HasInitialTraceLocallyL1 u g)
    (hweak : ∀ φ : 𝓓^{1}(forwardHalfSpace, ℝ),
      ∫ p : ℝ^2, InteriorWeakForm.integrand u (fun p ↦ flux (u p)) φ p = 0) :
    IsWeakInitialValueSolution flux g u where
  u_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hu
  flux_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hf
  initial_locallyIntegrable := htrace.initial_locallyIntegrable
  spacetime_integrable := integrableOn_initialWeakIntegrand hu hf
  weak_initial_eq := initialWeak_eq_zero_of_interior_of_initialTrace hu hf htrace hweak

/-- Compact vector tests pair integrably with locally integrable state and flux
fields, including near the initial face. -/
theorem integrableOn_initialVectorWeakIntegrand
    {m : ℕ} {u q : ℝ^2 → ℝ^m}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^m)) :
    IntegrableOn (fun p ↦
      ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪q p, (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ)
      forwardHalfSpace volume := by
  have hc (i : Fin 2) : Continuous (fun p ↦ (∂[i] (ψ : ℝ^2 → ℝ^m)) p) :=
    (ψ.contDiff.continuous_fderiv_apply (hn := by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hs (i : Fin 2) : HasCompactSupport (fun p ↦ (∂[i] (ψ : ℝ^2 → ℝ^m)) p) :=
    ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  exact (hu.integrable_inner_right_of_hasCompactSupport (hc 0) (hs 0)).add
    (hq.integrable_inner_right_of_hasCompactSupport (hc 1) (hs 1))

/-- A compact vector test has an integrable pairing with the initial datum.
The spatial slice is a closed isometric embedding of the line. -/
theorem integrable_initialVectorBoundary {m : ℕ} {g : ℝ → ℝ^m} (hg : LocallyIntegrable g volume)
    (ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^m)) :
    Integrable (fun x : ℝ ↦ ⟪g x, ψ !₂[0, x]⟫_ℝ) volume := by
  have hi : Isometry (fun x : ℝ ↦ (!₂[0, x] : ℝ^2)) := by
    have heq (x : ℝ) : (!₂[0, x] : ℝ^2) = EuclideanSpace.single 1 x := by
      ext i
      fin_cases i <;> simp
    intro x y
    simp only [heq, PiLp.edist_single_same]
  exact hg.integrable_inner_right_of_hasCompactSupport (ψ.contDiff.continuous.comp hi.continuous)
    (ψ.hasCompactSupport.comp_isClosedEmbedding hi.isClosedEmbedding)

end PDE.Hyperbolic.ConservationLaw
