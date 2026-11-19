/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm

/-!
# Weak solutions of one-dimensional conservation-law systems

We define the vector-valued distributional formulation of

`u_t + (f(u))_x = 0`.

The test functions remain scalar, while the identity is a Bochner integral
in the state space:

`∫ (φ_t • u + φ_x • f(u)) = 0`.

This is a local interior formulation on an open spacetime set.

The scalar tests are Mathlib's test functions. Restriction and almost-everywhere
congruence preserve weak solutions, and Mathlib's vector-valued integration-by-parts
theorem proves that every global `C¹` pointwise solution is weak.

The identity is the interior part of (13) in Evans, §11.1.1, with the same signs. Evans
pairs the system with smooth `ℝᵐ`-valued tests (12); we use scalar `C¹` tests and a
vector-valued integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (12)-(13).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace

open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System


variable {m : ℕ}

/-! ## Weak formulation -/

/-- Integrand in the vector weak formulation. -/
def weakIntegrand
    (flux : ℝ^m → ℝ^m) (u : ℝ^2 → ℝ^m)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ))
    (p : ℝ^2) : ℝ^m :=
  (∂[0] (φ : ℝ^2 → ℝ)) p • u p + (∂[1] (φ : ℝ^2 → ℝ)) p • flux (u p)

/-- The system integrand is the shared interior integrand applied to the state and its flux. -/
private theorem weakIntegrand_eq_interiorIntegrand (flux : ℝ^m → ℝ^m) (u : ℝ^2 → ℝ^m)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ)) :
    weakIntegrand flux u φ =
      PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrand u (fun p ↦ flux (u p)) φ :=
  rfl

/-- Local integrability of the state and flux makes every vector weak integrand globally
Bochner integrable. -/
theorem integrable_weakIntegrand {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hflux : MeasureTheory.LocallyIntegrableOn (fun p : ℝ^2 ↦ flux (u p)) U MeasureTheory.volume)
    (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (weakIntegrand flux u φ) MeasureTheory.volume := by
  rw [weakIntegrand_eq_interiorIntegrand]
  exact PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrable_integrand hu hflux φ

/-- The vector weak integrand of a constant state has zero integral. -/
theorem integral_weakIntegrand_const_eq_zero (flux : ℝ^m → ℝ^m) {U : Opens ℝ^2} (state : ℝ^m)
    (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, weakIntegrand flux (fun _ ↦ state) φ p ∂MeasureTheory.volume) = 0 := by
  rw [weakIntegrand_eq_interiorIntegrand]
  simpa using PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_integrand_const_eq_zero
      state (flux state) φ

/-- A weak solution of a one-dimensional system of conservation laws. -/
structure IsWeakSolution
    (flux : ℝ^m → ℝ^m) (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ^m) : Prop where
  /-- The conserved state is locally Bochner integrable. -/
  u_locallyIntegrable :
    MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume
  /-- The flux is locally Bochner integrable. -/
  flux_locallyIntegrable :
    MeasureTheory.LocallyIntegrableOn
      (fun p : ℝ^2 ↦ flux (u p)) U MeasureTheory.volume
  /-- Distributional conservation identity. -/
  weak_eq :
    ∀ φ : 𝓓^{1}(U, ℝ),
      ∫ p : ℝ^2, weakIntegrand flux u φ p
        ∂MeasureTheory.volume = 0

/-- Every integrand in the vector weak formulation is Bochner integrable. -/
theorem IsWeakSolution.integrable_weakIntegrand {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsWeakSolution flux U u) (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (weakIntegrand flux u φ) MeasureTheory.volume :=
  PDE.Hyperbolic.ConservationLaw.System.integrable_weakIntegrand
    hu.u_locallyIntegrable hu.flux_locallyIntegrable φ

/-- A weak solution restricts to every smaller open domain. -/
theorem IsWeakSolution.mono_domain {flux : ℝ^m → ℝ^m} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsWeakSolution flux V u) (hUV : U ≤ V) :
    IsWeakSolution flux U u := by
  exact
    { u_locallyIntegrable := hu.u_locallyIntegrable.mono_set hUV
      flux_locallyIntegrable := hu.flux_locallyIntegrable.mono_set hUV
      weak_eq := by
        intro φ
        rw [weakIntegrand_eq_interiorIntegrand]
        exact PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_eq_zero_mono_domain
            (fun ψ ↦ by
              rw [← weakIntegrand_eq_interiorIntegrand]
              exact hu.weak_eq ψ) hUV φ }

/-- Weak solutions are invariant under representatives that agree almost everywhere on the
domain. -/
theorem IsWeakSolution.congr_ae_restrict {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    (hu : IsWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    IsWeakSolution flux U v := by
  have hfluxU : (fun p : ℝ^2 ↦ flux (u p)) =ᵐ[MeasureTheory.volume.restrict U]
        fun p : ℝ^2 ↦ flux (v p) := huv.fun_comp flux
  refine
    { u_locallyIntegrable := hu.u_locallyIntegrable.congr huv
      flux_locallyIntegrable := hu.flux_locallyIntegrable.congr hfluxU
      weak_eq := ?_ }
  intro φ
  rw [weakIntegrand_eq_interiorIntegrand]
  exact PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_eq_zero_congr_ae_restrict
      (fun ψ ↦ by
        rw [← weakIntegrand_eq_interiorIntegrand]
        exact hu.weak_eq ψ) huv hfluxU φ

/-- Weak solutions are invariant under global almost-everywhere changes of representative. -/
theorem IsWeakSolution.congr_ae {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ^m}
    (hu : IsWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume] v) :
    IsWeakSolution flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-! ## Integration by parts -/

/-- Integration by parts identifies the tested classical residual with the
negative vector weak integral. -/
theorem integral_smul_fluxResidual_eq_neg_weakIntegrand {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ^m} (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ p : ℝ^2, φ p • fluxResidual flux u p ∂MeasureTheory.volume) = -∫ p : ℝ^2,
      weakIntegrand flux u φ p ∂MeasureTheory.volume :=
  InteriorWeakForm.integral_smul_divergence_eq_neg_integrand
    hu.contDiffOn (hflux.comp hu).contDiffOn φ

/-! ## Classical solutions are weak -/

/-- Every global `C¹` pointwise solution is a vector weak solution on the
given open domain. -/
theorem isWeakSolution_of_pointwise_of_contDiff {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u) (hpde : ∀ p ∈ U, fluxResidual flux u p = 0) :
    IsWeakSolution flux U u := by
  refine
    { u_locallyIntegrable := hu.continuous.locallyIntegrable.locallyIntegrableOn U
      flux_locallyIntegrable := (hflux.comp hu).continuous.locallyIntegrable
          |>.locallyIntegrableOn U
      weak_eq := ?_ }
  intro φ
  have hpoint : ∀ p : ℝ^2, φ p • fluxResidual flux u p = 0 := by
    intro p
    by_cases hp : p ∈ U
    · simp [hpde p hp]
    · simp [φ.zero_on_compl hp]
  have hResidualIntegral : (∫ p : ℝ^2, φ p • fluxResidual flux u p ∂MeasureTheory.volume) = 0 := by
    have hzero : (fun p : ℝ^2 ↦ φ p • fluxResidual flux u p) = 0 := by
      funext p
      exact hpoint p
    simp [hzero]
  have hbridge := integral_smul_fluxResidual_eq_neg_weakIntegrand hflux hu φ
  rw [hResidualIntegral] at hbridge
  exact neg_eq_zero.mp hbridge.symm

/-- A bundled classical solution with global `C¹` regularity is weak. -/
theorem IsClassicalSolutionOn.isWeakSolution {flux : ℝ^m → ℝ^m} {U : Opens ℝ^2} {u : ℝ^2 → ℝ^m}
    (hclassical : IsClassicalSolutionOn flux U u) (hflux : ContDiff ℝ 1 flux)
    (hu : ContDiff ℝ 1 u) :
    IsWeakSolution flux U u :=
  isWeakSolution_of_pointwise_of_contDiff hflux hu hclassical.residual_eq_zero

/-- A constant state has zero conservative residual for every flux. -/
theorem fluxResidual_const (flux : ℝ^m → ℝ^m) (state : ℝ^m) (p : ℝ^2) :
    fluxResidual flux (fun _ : ℝ^2 ↦ state) p = 0 := by
  simp [fluxResidual, Function.comp_def, partialDeriv_const]

/-- Constant states are weak solutions on every open domain for every flux. -/
theorem isWeakSolution_const {flux : ℝ^m → ℝ^m} (U : Opens ℝ^2) (state : ℝ^m) :
    IsWeakSolution flux U (fun _ : ℝ^2 ↦ state) := by
  refine
    { u_locallyIntegrable := MeasureTheory.locallyIntegrableOn_const state
      flux_locallyIntegrable := MeasureTheory.locallyIntegrableOn_const (flux state)
      weak_eq := ?_ }
  exact integral_weakIntegrand_const_eq_zero flux state

end PDE.Hyperbolic.ConservationLaw.System
