/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Weak
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm

/-!
# Entropy weak solutions of one-dimensional conservation-law systems

For a convex entropy pair `(η, q)`, the distributional inequality

`∂t η(u) + ∂x q(u) ≤ 0`

is tested against nonnegative compactly supported functions and written as

`0 ≤ ∫ (η(u) φ_t + q(u) φ_x)`.

This is the inequality (28) of Evans, §11.4.2, in the weak form (29), on an open spacetime set.
The predicates are conjunctions, not structures. They include the local integrability
needed to make the totalized Bochner integral meaningful, are stable under domain
restriction and almost-everywhere changes of representative, and extend the vector weak
formulation from `System.Weak`.

## Main results

* `SatisfiesEntropyInequalityFor`, `SatisfiesEntropyInequality`, `IsEntropyWeakSolution`: the
  one-pair inequality, the inequality for every convex entropy pair, and its conjunction with
  the weak equation.
* `integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand`: integration by parts between the
  classical entropy residual `∂t η(u) + ∂x q(u)` and the weak entropy integrand, for `C¹`
  states.
* `isEntropyWeakSolution_of_pointwise_of_contDiff`,
  `IsClassicalSolutionOn.isEntropyWeakSolution`: a classical solution on `U` is an entropy
  weak solution when both the state and flux are globally `C¹`. Its entropy residual on `U`
  vanishes by the chain rule and the compatibility `Dq = Dη ∘ Df` built into `EntropyPair`.
* `isEntropyWeakSolution_const`: constant states are entropy weak solutions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, definitions of entropy/entropy-flux pair and
  entropy solution, equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
* P. D. Lax, *Hyperbolic Systems of Conservation Laws and the Mathematical Theory of Shock Waves*,
  Society for Industrial and Applied Mathematics, 1973.
  <https://doi.org/10.1137/1.9781611970562>
-/

@[expose] public section

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System


variable {m : ℕ}

/-! ## Entropy inequalities -/

/-- Integrand in the weak entropy inequality for one entropy pair. -/
def entropyWeakIntegrand
    {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (u : ℝ^2 → ℝ^m)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ))
    (p : ℝ^2) : ℝ :=
  E.entropy (u p) * (∂[0] (φ : ℝ^2 → ℝ)) p + E.entropyFlux (u p) * (∂[1] (φ : ℝ^2 → ℝ)) p

/-- Local integrability of the entropy density and entropy flux makes every weak entropy
integrand globally integrable. -/
theorem integrable_entropyWeakIntegrand {flux : ℝ^m → ℝ^m} {E : EntropyPair flux} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m}
    (hEntropy :
      MeasureTheory.LocallyIntegrableOn (fun p : ℝ^2 ↦ E.entropy (u p)) U MeasureTheory.volume)
    (hEntropyFlux : MeasureTheory.LocallyIntegrableOn (fun p : ℝ^2 ↦ E.entropyFlux (u p)) U
      MeasureTheory.volume)
    (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (entropyWeakIntegrand E u φ) MeasureTheory.volume :=
  (φ.integrable_mul_partialDeriv hEntropy 0).add (φ.integrable_mul_partialDeriv hEntropyFlux 1)

/-- The weak entropy inequality for one compatible entropy pair.

The first two conjuncts state local integrability of `η(u)` and `q(u)`; the third is the
distributional inequality against nonnegative test functions. -/
def SatisfiesEntropyInequalityFor
    {flux : ℝ^m → ℝ^m} (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ^m) (E : EntropyPair flux) : Prop :=
  MeasureTheory.LocallyIntegrableOn (fun p : ℝ^2 ↦ E.entropy (u p)) U MeasureTheory.volume ∧
    MeasureTheory.LocallyIntegrableOn (fun p : ℝ^2 ↦ E.entropyFlux (u p)) U MeasureTheory.volume ∧
    ∀ φ : 𝓓^{1}(U, ℝ), (∀ p : ℝ^2, 0 ≤ φ p) → 0 ≤ ∫ p : ℝ^2, entropyWeakIntegrand E u φ p
          ∂MeasureTheory.volume

/-- Every integrand occurring in a one-pair entropy inequality is integrable. -/
theorem SatisfiesEntropyInequalityFor.integrable_entropyWeakIntegrand {flux : ℝ^m → ℝ^m}
    {E : EntropyPair flux} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hE : SatisfiesEntropyInequalityFor U u E) (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (entropyWeakIntegrand E u φ) MeasureTheory.volume :=
  PDE.Hyperbolic.ConservationLaw.System.integrable_entropyWeakIntegrand hE.1 hE.2.1 φ

/-- The weak entropy integrand of a constant state has zero integral. -/
theorem integral_entropyWeakIntegrand_const_eq_zero {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    {U : Opens ℝ^2} (state : ℝ^m) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, entropyWeakIntegrand E (fun _ : ℝ^2 ↦ state) φ p ∂MeasureTheory.volume) = 0 := by
  have htimeIntegrable := φ.integrable_partialDeriv (0 : Fin 2)
  have hspaceIntegrable := φ.integrable_partialDeriv (1 : Fin 2)
  have htime := φ.integral_partialDeriv_eq_zero (0 : Fin 2)
  have hspace := φ.integral_partialDeriv_eq_zero (1 : Fin 2)
  change (∫ p : ℝ^2, E.entropy state * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p + E.entropyFlux state *
          (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p ∂MeasureTheory.volume) = 0
  rw [MeasureTheory.integral_add (htimeIntegrable.const_mul (E.entropy state))
    (hspaceIntegrable.const_mul (E.entropyFlux state))]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, htime, hspace]
  simp

/-- A constant state has zero entropy production for every entropy pair on
every open domain. -/
theorem satisfiesEntropyInequalityFor_const {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (U : Opens ℝ^2) (state : ℝ^m) :
    SatisfiesEntropyInequalityFor U (fun _ : ℝ^2 ↦ state) E := by
  refine ⟨MeasureTheory.locallyIntegrableOn_const _, MeasureTheory.locallyIntegrableOn_const _, ?_⟩
  intro φ _
  rw [integral_entropyWeakIntegrand_const_eq_zero E state φ]

/-- A one-pair entropy inequality restricts to every smaller open domain. -/
theorem SatisfiesEntropyInequalityFor.mono_domain {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {U V : Opens ℝ^2} {u : ℝ^2 → ℝ^m} (hE : SatisfiesEntropyInequalityFor V u E) (hUV : U ≤ V) :
    SatisfiesEntropyInequalityFor U u E := by
  refine ⟨hE.1.mono_set hUV, hE.2.1.mono_set hUV, fun φ hφ ↦ ?_⟩
  let φV : 𝓓^{1}(V, ℝ) := TestFunction.monoCLM ℝ φ
  have hφV : ∀ p : ℝ^2, 0 ≤ φV p := by
    intro p
    simpa [φV, hUV] using hφ p
  simpa [entropyWeakIntegrand, φV, hUV] using hE.2.2 φV hφV

/-- A one-pair entropy inequality is invariant under representatives that agree almost
everywhere on its domain. -/
theorem SatisfiesEntropyInequalityFor.congr_ae_restrict {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m} (hE : SatisfiesEntropyInequalityFor U u E)
    (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    SatisfiesEntropyInequalityFor U v E := by
  have hEntropy : (fun p : ℝ^2 ↦ E.entropy (u p)) =ᵐ[MeasureTheory.volume.restrict U]
        fun p : ℝ^2 ↦ E.entropy (v p) := huv.fun_comp E.entropy
  have hEntropyFlux : (fun p : ℝ^2 ↦ E.entropyFlux (u p)) =ᵐ[MeasureTheory.volume.restrict U]
        fun p : ℝ^2 ↦ E.entropyFlux (v p) := huv.fun_comp E.entropyFlux
  refine ⟨hE.1.congr hEntropy, hE.2.1.congr hEntropyFlux, fun φ hφ ↦ ?_⟩
  have hIntegrandOn : entropyWeakIntegrand E u φ =ᵐ[MeasureTheory.volume.restrict U]
        entropyWeakIntegrand E v φ :=
    huv.mono fun p hp ↦ by simp [entropyWeakIntegrand, hp]
  have hIntegrandOff : entropyWeakIntegrand E u φ =ᵐ[MeasureTheory.volume.restrict (U : Set ℝ^2)ᶜ]
        entropyWeakIntegrand E v φ := by
    refine MeasureTheory.ae_restrict_of_forall_mem U.isOpen.measurableSet.compl fun p hp ↦ ?_
    have hpU : p ∉ U := hp
    have h0 := φ.partialDeriv_eq_zero_of_notMem hpU (0 : Fin 2)
    have h1 := φ.partialDeriv_eq_zero_of_notMem hpU (1 : Fin 2)
    simp [entropyWeakIntegrand, h0, h1]
  have hIntegrand : entropyWeakIntegrand E u φ =ᵐ[MeasureTheory.volume]
        entropyWeakIntegrand E v φ :=
    MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl (U : Set ℝ^2) hIntegrandOn hIntegrandOff
  have hInequality := hE.2.2 φ hφ
  rwa [MeasureTheory.integral_congr_ae hIntegrand] at hInequality

/-- A one-pair entropy inequality is invariant under global almost-everywhere changes. -/
theorem SatisfiesEntropyInequalityFor.congr_ae {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m} (hE : SatisfiesEntropyInequalityFor U u E)
    (huv : u =ᵐ[MeasureTheory.volume] v) :
    SatisfiesEntropyInequalityFor U v E :=
  hE.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-- The entropy inequality for every globally `C¹` compatible entropy pair whose entropy
is convex on the whole state space. -/
def SatisfiesEntropyInequality
    (flux : ℝ^m → ℝ^m) (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ^m) : Prop :=
  ∀ E : ConvexEntropyPair flux, SatisfiesEntropyInequalityFor U u E.toEntropyPair

/-- Entropy inequalities restrict to smaller open domains. -/
theorem SatisfiesEntropyInequality.mono_domain {flux : ℝ^m → ℝ^m} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : SatisfiesEntropyInequality flux V u) (hUV : U ≤ V) :
    SatisfiesEntropyInequality flux U u :=
  fun E ↦ (hu E).mono_domain hUV

/-- Entropy inequalities are invariant under almost-everywhere changes on the domain. -/
theorem SatisfiesEntropyInequality.congr_ae_restrict {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ^m} (hu : SatisfiesEntropyInequality flux U u)
    (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    SatisfiesEntropyInequality flux U v :=
  fun E ↦ (hu E).congr_ae_restrict huv

/-- Entropy inequalities are invariant under global almost-everywhere changes. -/
theorem SatisfiesEntropyInequality.congr_ae {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    (hu : SatisfiesEntropyInequality flux U u) (huv : u =ᵐ[MeasureTheory.volume] v) :
    SatisfiesEntropyInequality flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-- A weak solution satisfying every convex entropy inequality. -/
def IsEntropyWeakSolution
    (flux : ℝ^m → ℝ^m) (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ^m) : Prop :=
  IsWeakSolution flux U u ∧ SatisfiesEntropyInequality flux U u

namespace IsEntropyWeakSolution

/-- An entropy weak solution is a weak solution. -/
theorem weak {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsEntropyWeakSolution flux U u) :
    IsWeakSolution flux U u :=
  hu.1

/-- An entropy weak solution satisfies every convex entropy inequality. -/
theorem entropy {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsEntropyWeakSolution flux U u) :
    SatisfiesEntropyInequality flux U u :=
  hu.2

/-- Entropy weak solutions restrict to smaller open domains. -/
theorem mono_domain {flux : ℝ^m → ℝ^m} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsEntropyWeakSolution flux V u) (hUV : U ≤ V) :
    IsEntropyWeakSolution flux U u :=
  ⟨hu.1.mono_domain hUV, hu.2.mono_domain hUV⟩

/-- Entropy weak solutions are invariant under almost-everywhere changes on the domain. -/
theorem congr_ae_restrict {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    (hu : IsEntropyWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    IsEntropyWeakSolution flux U v :=
  ⟨hu.1.congr_ae_restrict huv, hu.2.congr_ae_restrict huv⟩

/-- Entropy weak solutions are invariant under global almost-everywhere changes. -/
theorem congr_ae {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    (hu : IsEntropyWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume] v) :
    IsEntropyWeakSolution flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

end IsEntropyWeakSolution

/-! ## Classical solutions are entropy weak -/

/-- Integration by parts identifies the tested entropy residual on an open set.
Only the state near the support of the test needs to be continuously differentiable. -/
theorem integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand_on
    {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (E : EntropyPair flux) (hu : ContDiffOn ℝ 1 u U) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, φ p * entropyResidual E u p ∂MeasureTheory.volume) =
      -∫ p : ℝ^2, entropyWeakIntegrand E u φ p ∂MeasureTheory.volume := by
  simpa only [entropyResidual, entropyWeakIntegrand, InteriorWeakForm.integrand,
    smul_eq_mul, Function.comp_apply, mul_comm] using
    InteriorWeakForm.integral_smul_divergence_eq_neg_integrand
      (E.entropy_contDiff.comp_contDiffOn hu) (E.entropyFlux_contDiff.comp_contDiffOn hu) φ

/-- Integration by parts identifies the tested classical entropy residual with the negative
weak entropy integral. -/
theorem integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} (E : EntropyPair flux) (hu : ContDiff ℝ 1 u) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, φ p * entropyResidual E u p ∂MeasureTheory.volume) = -∫ p : ℝ^2,
      entropyWeakIntegrand E u φ p ∂MeasureTheory.volume :=
  integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand_on E hu.contDiffOn φ

/-- Every global `C¹` pointwise solution satisfies all convex entropy inequalities. -/
theorem satisfiesEntropyInequality_of_pointwise_of_contDiff {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} (hu : ContDiff ℝ 1 u) (hpde : ∀ p ∈ U, fluxResidual flux u p = 0) :
    SatisfiesEntropyInequality flux U u := by
  intro E
  refine ⟨(E.entropy_contDiff.comp hu).continuous.locallyIntegrable
        |>.locallyIntegrableOn U, (E.entropyFlux_contDiff.comp hu).continuous.locallyIntegrable
        |>.locallyIntegrableOn U, ?_⟩
  intro φ _
  have hResidualPointwise : ∀ p : ℝ^2, φ p * entropyResidual E.toEntropyPair u p = 0 := by
    intro p
    by_cases hp : p ∈ U
    · rw [E.toEntropyPair.entropyResidual_eq_zero_of_flux
        hu.differentiable_one.differentiableAt (hpde p hp)]
      simp
    · rw [φ.zero_on_compl hp]
      simp
  have hResidualIntegral : (∫ p : ℝ^2, φ p * entropyResidual E.toEntropyPair u p
        ∂MeasureTheory.volume) = 0 := by
    have hzero : (fun p : ℝ^2 ↦ φ p * entropyResidual E.toEntropyPair u p) = 0 := by
      funext p
      exact hResidualPointwise p
    simp [hzero]
  have hbridge := integral_mul_entropyResidual_eq_neg_entropyWeakIntegrand E.toEntropyPair hu φ
  rw [hResidualIntegral] at hbridge
  have hWeakIntegral : (∫ p : ℝ^2, entropyWeakIntegrand E.toEntropyPair u φ p
        ∂MeasureTheory.volume) = 0 := neg_eq_zero.mp hbridge.symm
  simp [hWeakIntegral]

/-- Every global `C¹` pointwise solution is an entropy weak solution. -/
theorem isEntropyWeakSolution_of_pointwise_of_contDiff {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u)
    (hpde : ∀ p ∈ U, fluxResidual flux u p = 0) :
    IsEntropyWeakSolution flux U u :=
  ⟨isWeakSolution_of_pointwise_of_contDiff hflux hu hpde,
    satisfiesEntropyInequality_of_pointwise_of_contDiff hu hpde⟩

/-- A classical solution on `U` is an entropy weak solution when both the state and flux
are globally `C¹`. -/
theorem IsClassicalSolutionOn.isEntropyWeakSolution {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} (hclassical : IsClassicalSolutionOn flux U u) (hflux : ContDiff ℝ 1 flux)
    (hu : ContDiff ℝ 1 u) :
    IsEntropyWeakSolution flux U u :=
  isEntropyWeakSolution_of_pointwise_of_contDiff hflux hu hclassical.residual_eq_zero

/-- Constant states are entropy weak solutions on every open domain for every flux. -/
theorem isEntropyWeakSolution_const {flux : ℝ^m → ℝ^m} (U : Opens ℝ^2) (state : ℝ^m) :
    IsEntropyWeakSolution flux U (fun _ : ℝ^2 ↦ state) := by
  refine ⟨isWeakSolution_const U state, fun E ↦ ?_⟩
  exact satisfiesEntropyInequalityFor_const E.toEntropyPair U state

end PDE.Hyperbolic.ConservationLaw.System
