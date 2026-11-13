/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.PartialDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# Interior weak forms for one-dimensional conservation laws

We study the interior weak form

`∫ (φ_t • u + φ_x • q) = 0`

for state and flux fields `u, q : ℝ^2 → E`, parameterized by a real
normed state space. We prove integrability against compactly supported test
functions and invariance of the identity under domain restriction and
almost-everywhere changes of the fields. The constant-field integral theorem
assumes completeness, as required for the Bochner integral.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.InteriorWeakForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interior weak integrand associated with state and flux fields. -/
def integrand
    (state flux : ℝ^2 → E) {U : Opens ℝ^2}
    (φ : 𝓓^{1}(U, ℝ)) (p : ℝ^2) : E :=
  (∂[0] (φ : ℝ^2 → ℝ)) p • state p +
    (∂[1] (φ : ℝ^2 → ℝ)) p • flux p

/-- Locally integrable state and flux fields give a globally integrable weak integrand. -/
theorem integrable_integrand {state flux : ℝ^2 → E} {U : Opens ℝ^2}
    (hstate : MeasureTheory.LocallyIntegrableOn state U MeasureTheory.volume)
    (hflux : MeasureTheory.LocallyIntegrableOn flux U MeasureTheory.volume) (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (integrand state flux φ) MeasureTheory.volume :=
  (φ.integrable_partialDeriv_smul hstate 0).add (φ.integrable_partialDeriv_smul hflux 1)

/-- Coordinate integration by parts for independent density and flux fields on
an open spacetime domain. The regularity is local to that domain. -/
theorem integral_smul_divergence_eq_neg_integrand {u q : ℝ^2 → E} {U : Opens ℝ^2}
    (hu : ContDiffOn ℝ 1 u U) (hq : ContDiffOn ℝ 1 q U) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p, φ p • ((∂[0] u) p + (∂[1] q) p)) = -∫ p, integrand u q φ p := by
  have hc {f : ℝ^2 → E} (hf : ContDiffOn ℝ 1 f U) (p : ℝ^2)
      (hp : p ∈ tsupport (φ : ℝ^2 → ℝ)) : ContDiffAt ℝ 1 f p :=
    hf.contDiffAt (U.isOpen.mem_nhds (φ.tsupport_subset hp))
  have hint {f : ℝ^2 → E} (hf : ContDiffOn ℝ 1 f U) (i : Fin 2) :
      MeasureTheory.Integrable (fun p ↦ φ p • (∂[i] f) p) := by
    apply MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := tsupport (φ : ℝ^2 → ℝ))
    · apply ContinuousOn.integrableOn_compact φ.hasCompactSupport
      refine φ.contDiff.continuous.continuousOn.smul ?_
      exact fun p hp ↦ (((hc hf p hp).continuousAt_fderiv one_ne_zero).clm_apply
        continuousAt_const).continuousWithinAt
    · intro p hp
      simp [image_eq_zero_of_notMem_tsupport hp]
  have htime := PDE.Analysis.integral_smul_partialDeriv_eq_neg_of_contDiffAt
    (0 : Fin 2) φ.contDiff (hc hu) φ.hasCompactSupport
  have hspace := PDE.Analysis.integral_smul_partialDeriv_eq_neg_of_contDiffAt
    (1 : Fin 2) φ.contDiff (hc hq) φ.hasCompactSupport
  have hui : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume :=
    hu.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hqi : MeasureTheory.LocallyIntegrableOn q U MeasureTheory.volume :=
    hq.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  simp only [smul_add, MeasureTheory.integral_add (hint hu 0) (hint hq 1), htime, hspace, integrand,
    MeasureTheory.integral_add (φ.integrable_partialDeriv_smul hui 0)
      (φ.integrable_partialDeriv_smul hqi 1), neg_add]

/-- The interior weak integrand of two constant fields has zero integral. -/
theorem integral_integrand_const_eq_zero [CompleteSpace E] (state flux : E) {U : Opens ℝ^2}
    (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, integrand (fun _ ↦ state) (fun _ ↦ flux) φ p ∂MeasureTheory.volume) = 0 := by
  have htimeIntegrable : MeasureTheory.Integrable (fun p : ℝ^2 ↦
          (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p • state)
        MeasureTheory.volume := (φ.integrable_partialDeriv (0 : Fin 2)).smul_const state
  have hspaceIntegrable : MeasureTheory.Integrable (fun p : ℝ^2 ↦
          (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p • flux)
        MeasureTheory.volume := (φ.integrable_partialDeriv (1 : Fin 2)).smul_const flux
  rw [show integrand (fun _ ↦ state) (fun _ ↦ flux) φ = fun p : ℝ^2 ↦
        (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p • state +
          (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p • flux by
    rfl]
  rw [MeasureTheory.integral_add htimeIntegrable hspaceIntegrable,
    integral_smul_const, integral_smul_const, φ.integral_partialDeriv_eq_zero (0 : Fin 2),
    φ.integral_partialDeriv_eq_zero (1 : Fin 2)]
  simp

/-- A zero-integral interior weak identity restricts to every smaller open domain. -/
theorem integral_eq_zero_mono_domain {state flux : ℝ^2 → E} {U V : Opens ℝ^2}
    (hidentity : ∀ φ : 𝓓^{1}(V, ℝ), ∫ p : ℝ^2, integrand state flux φ p ∂MeasureTheory.volume = 0)
    (hUV : U ≤ V) :
    ∀ φ : 𝓓^{1}(U, ℝ), ∫ p : ℝ^2, integrand state flux φ p ∂MeasureTheory.volume = 0 := by
  intro φ
  simpa [integrand, hUV] using hidentity (TestFunction.monoCLM ℝ φ : 𝓓^{1}(V, ℝ))

/-- Restricted almost-everywhere equality of both fields gives global almost-everywhere equality
of their weak integrands, because test-function derivatives vanish off the domain. -/
theorem integrand_congr_ae_restrict {state state' flux flux' : ℝ^2 → E} {U : Opens ℝ^2}
    (hstate : state =ᵐ[MeasureTheory.volume.restrict U] state')
    (hflux : flux =ᵐ[MeasureTheory.volume.restrict U] flux') (φ : 𝓓^{1}(U, ℝ)) :
    integrand state flux φ =ᵐ[MeasureTheory.volume] integrand state' flux' φ := by
  have hIntegrandOn : integrand state flux φ =ᵐ[MeasureTheory.volume.restrict U]
        integrand state' flux' φ :=
    (hstate.and hflux).mono fun p hp ↦ by
      simp [integrand, hp.1, hp.2]
  have hIntegrandOff : integrand state flux φ =ᵐ[ MeasureTheory.volume.restrict (U : Set ℝ^2)ᶜ]
        integrand state' flux' φ := by
    refine MeasureTheory.ae_restrict_of_forall_mem U.isOpen.measurableSet.compl fun p hp ↦ ?_
    have hpU : p ∉ U := hp
    have h0 := φ.partialDeriv_eq_zero_of_notMem hpU (0 : Fin 2)
    have h1 := φ.partialDeriv_eq_zero_of_notMem hpU (1 : Fin 2)
    simp [integrand, h0, h1]
  exact MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl (U : Set ℝ^2)
      hIntegrandOn hIntegrandOff

/-- A zero-integral interior weak identity is invariant under restricted almost-everywhere
changes of both fields. -/
theorem integral_eq_zero_congr_ae_restrict {state state' flux flux' : ℝ^2 → E} {U : Opens ℝ^2}
    (hidentity : ∀ φ : 𝓓^{1}(U, ℝ), ∫ p : ℝ^2, integrand state flux φ p ∂MeasureTheory.volume = 0)
    (hstate : state =ᵐ[MeasureTheory.volume.restrict U] state')
    (hflux : flux =ᵐ[MeasureTheory.volume.restrict U] flux') :
    ∀ φ : 𝓓^{1}(U, ℝ), ∫ p : ℝ^2, integrand state' flux' φ p ∂MeasureTheory.volume = 0 := by
  intro φ
  calc
    (∫ p : ℝ^2, integrand state' flux' φ p ∂MeasureTheory.volume) =
        ∫ p : ℝ^2, integrand state flux φ p ∂MeasureTheory.volume :=
      (MeasureTheory.integral_congr_ae (integrand_congr_ae_restrict hstate hflux φ)).symm
    _ = 0 := hidentity φ

end PDE.Hyperbolic.ConservationLaw.InteriorWeakForm
