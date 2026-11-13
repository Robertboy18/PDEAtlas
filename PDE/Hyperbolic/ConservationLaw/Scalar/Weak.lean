/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Equation
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import PDE.DistributionTheory.TestFunction
import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm
import PDE.Analysis.Integration.CompactByParts

/-!
# Weak solutions for one-dimensional scalar conservation laws

We define weak solutions of the flux-form conservation law

`u_t + (f(u))_x = 0`

on spacetime `ℝ^2`.

The weak formulation puts derivatives on compactly supported test functions. For smooth
candidates we also give a residual-test identity and prove its equivalence to the weak
identity by integration by parts. The residual-test predicate is not called a
distributional solution because totalized classical derivatives do not encode jump
measures.

The sign convention is that of Evans, §3.4.1(a), equations (3)-(4), p. 136. Entropy
inequalities are in
`PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(a), equations (2)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open PDE.Common TopologicalSpace

open scoped Distributions Topology

/-! ## Classical residual-test identities -/

/-- Flux-form PDE residual `u_t + (f(u))_x`. -/
noncomputable def fluxResidual
    (flux : ℝ → ℝ) (u : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ (∂[(0 : Fin 2)] u) x +
    (∂[(1 : Fin 2)] (fun y ↦ flux (u y))) x

/-- The classical flux residual vanishes when tested against compactly supported `C¹` functions.

This predicate is useful only for smooth solutions. It is not a definition of a
distributional solution for nonsmooth `u`, because `partialDeriv` is a totalized classical
derivative and therefore does not record singular jump terms. -/
structure SatisfiesResidualTestIdentity
    (flux : ℝ → ℝ) (U : Opens ℝ^2) (u : ℝ^2 → ℝ) : Prop where
  /-- Every tested residual is integrable. -/
  integrable : ∀ φ : 𝓓^{1}(U, ℝ),
    MeasureTheory.Integrable (fun x : ℝ^2 ↦ fluxResidual flux u x * φ x)
      MeasureTheory.volume
  /-- Every tested residual has integral zero. -/
  identity : ∀ φ : 𝓓^{1}(U, ℝ),
    ∫ x : ℝ^2, fluxResidual flux u x * φ x ∂MeasureTheory.volume = 0

/-! ## Standard weak formulation (derivatives on the test function)

This is the conventional definition:

`∀ φ ∈ C_c^1(U), ∫ (u φ_t + f(u) φ_x) = 0`.

The `C¹` theorems below connect this formulation to the classical residual-test predicate
by integration by parts.
-/

/-- Integrand in the scalar weak formulation. -/
def weakIntegrand
    (flux : ℝ → ℝ) (u : ℝ^2 → ℝ)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ))
    (x : ℝ^2) : ℝ :=
  u x * (∂[0] (φ : ℝ^2 → ℝ)) x +
    flux (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x

/-- The scalar coefficient-first convention agrees with the shared interior weak integrand. -/
private theorem weakIntegrand_eq_interiorIntegrand
    (flux : ℝ → ℝ) (u : ℝ^2 → ℝ)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ)) :
    weakIntegrand flux u φ =
      PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrand
        u (fun x ↦ flux (u x)) φ := by
  funext x
  simp [weakIntegrand, PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrand,
    mul_comm]

/-- Local integrability of the conserved quantity and its flux makes every weak integrand
globally integrable. -/
theorem integrable_weakIntegrand
    {flux : ℝ → ℝ} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ} (φ : 𝓓^{1}(U, ℝ))
    (hu : MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume)
    (hflux : MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ^2 ↦ flux (u x)) U MeasureTheory.volume) :
    MeasureTheory.Integrable (weakIntegrand flux u φ)
      MeasureTheory.volume := by
  rw [weakIntegrand_eq_interiorIntegrand]
  exact
    PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrable_integrand
      hu hflux φ

/-- The scalar weak integrand of a constant state has zero integral. -/
theorem integral_weakIntegrand_const_eq_zero
    (flux : ℝ → ℝ) {U : Opens ℝ^2}
    (c : ℝ) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ x : ℝ^2,
      weakIntegrand flux (fun _ ↦ c) φ x
        ∂MeasureTheory.volume) = 0 := by
  rw [weakIntegrand_eq_interiorIntegrand]
  simpa using
    PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_integrand_const_eq_zero
      c (flux c) φ

/-- Weak solution in the standard test-function formulation.

The domain is open, both `u` and `flux ∘ u` are locally integrable there, and the distributional
identity

`∫ (u φ_t + flux(u) φ_x) = 0`

holds for every compactly supported `C¹` test function. The displayed integrand is integrable
because both coefficients are locally integrable and the derivatives of the test function are
continuous and compactly supported in the domain.

This is the interior distributional equation on `U`. It is not the weak
half-space initial-value formulation: no initial datum or boundary term at
`t = 0` is part of this structure. -/
structure IsWeakSolution
    (flux : ℝ → ℝ) (U : Opens ℝ^2) (u : ℝ^2 → ℝ) :
  Prop where
  /-- Local integrability of the conserved quantity. -/
  u_locallyIntegrable :
    MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume
  /-- Local integrability of the flux. -/
  flux_locallyIntegrable :
    MeasureTheory.LocallyIntegrableOn (fun x : ℝ^2 ↦ flux (u x)) U MeasureTheory.volume
  /-- Conservation-law identity against compactly supported test functions. -/
  weak_eq :
    ∀ φ : 𝓓^{1}(U, ℝ),
      ∫ x : ℝ^2, weakIntegrand flux u φ x
        ∂MeasureTheory.volume = 0

/-- Every integrand in the weak formulation is Bochner integrable. -/
theorem IsWeakSolution.integrable_weakIntegrand
    {flux : ℝ → ℝ} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ} (hu : IsWeakSolution flux U u)
    (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (weakIntegrand flux u φ)
      MeasureTheory.volume :=
  PDE.Hyperbolic.ConservationLaw.Scalar.integrable_weakIntegrand φ hu.u_locallyIntegrable
    hu.flux_locallyIntegrable

/-- A weak solution on `V` restricts to every smaller domain `U ⊆ V`. -/
theorem IsWeakSolution.mono_domain
    {flux : ℝ → ℝ} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hu : IsWeakSolution flux V u) (hUV : U ≤ V) :
    IsWeakSolution flux U u where
  u_locallyIntegrable := hu.u_locallyIntegrable.mono_set hUV
  flux_locallyIntegrable := hu.flux_locallyIntegrable.mono_set hUV
  weak_eq φ := by
    rw [weakIntegrand_eq_interiorIntegrand]
    exact PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_eq_zero_mono_domain
      (fun ψ ↦ by rw [← weakIntegrand_eq_interiorIntegrand]; exact hu.weak_eq ψ) hUV φ

/-- Weak solutions are invariant under representatives that agree almost everywhere on the
domain. -/
theorem IsWeakSolution.congr_ae_restrict
    {flux : ℝ → ℝ} {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ}
    (hu : IsWeakSolution flux U u)
    (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    IsWeakSolution flux U v :=
  have hfluxU : (fun x : ℝ^2 ↦ flux (u x)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x ↦ flux (v x) := huv.fun_comp flux
  { u_locallyIntegrable := hu.u_locallyIntegrable.congr huv
    flux_locallyIntegrable := hu.flux_locallyIntegrable.congr hfluxU
    weak_eq φ := by
      rw [weakIntegrand_eq_interiorIntegrand]
      exact PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integral_eq_zero_congr_ae_restrict
        (fun ψ ↦ by rw [← weakIntegrand_eq_interiorIntegrand]; exact hu.weak_eq ψ) huv hfluxU φ }

/-- Weak solutions are invariant under global almost-everywhere changes of representative. -/
theorem IsWeakSolution.congr_ae
    {flux : ℝ → ℝ} {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ}
    (hu : IsWeakSolution flux U u)
    (huv : u =ᵐ[MeasureTheory.volume] v) :
    IsWeakSolution flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-- The standard weak formulation is exactly the vanishing of the test-function-derivative
integral for every compactly supported `C¹` test function in the domain. -/
theorem isWeakSolution_iff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ} :
    IsWeakSolution flux U u ↔
      MeasureTheory.LocallyIntegrableOn u U MeasureTheory.volume ∧
        MeasureTheory.LocallyIntegrableOn (fun x : ℝ^2 ↦ flux (u x)) U
          MeasureTheory.volume ∧
        ∀ φ : 𝓓^{1}(U, ℝ),
          ∫ x : ℝ^2, weakIntegrand flux u φ x
            ∂MeasureTheory.volume = 0 :=
  ⟨fun h ↦ ⟨h.u_locallyIntegrable, h.flux_locallyIntegrable, h.weak_eq⟩,
    fun ⟨hu, hflux, hweak⟩ ↦ ⟨hu, hflux, hweak⟩⟩

/-! ## Integration by parts

Integration by parts against a test function relates:

* the residual formulation `∫ (u_t + (f(u))_x) φ = 0`, and
* the standard weak formulation `∫ (u φ_t + f(u) φ_x) = 0`.

To keep proofs elementary, we assume the functions are `C^1` (`ContDiff ℝ 1`),
which makes all relevant products integrable when multiplied by a compactly supported test
function.
-/

/-- Integration by parts against a `C¹` test: `(∂ᵢ g) φ` is integrable and
`∫ (∂ᵢ g) φ = -∫ g ∂ᵢ φ`. -/
theorem integrable_and_integral_partialDeriv_mul {U : Opens ℝ^2} {g : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (φ : 𝓓^{1}(U, ℝ)) (i : Fin 2) :
    MeasureTheory.Integrable (fun x ↦ (∂[i] g) x * φ x) MeasureTheory.volume ∧
      ∫ x, (∂[i] g) x * φ x ∂MeasureTheory.volume =
        -∫ x, g x * (∂[i] (φ : ℝ^2 → ℝ)) x ∂MeasureTheory.volume := by
  have h := PDE.Analysis.integral_mul_partialDeriv_eq_neg (i := i) (f := φ) (g := g)
    (hf := φ.contDiff) (hg := hg) φ.hasCompactSupport
  exact ⟨Continuous.integrable_of_hasCompactSupport ((contDiff_partialDeriv_of_succ (m := 0)
    (i := i) hg).continuous.fun_mul φ.contDiff.continuous) φ.hasCompactSupport.mul_left,
    by simpa [mul_comm] using h⟩

/-- A `C¹` flux residual is integrable against every compactly supported
`C¹` test function. -/
theorem integrable_fluxResidual_mul
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u) (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable
      (fun x : ℝ^2 ↦ fluxResidual flux u x * φ x)
      MeasureTheory.volume :=
  ((integrable_and_integral_partialDeriv_mul hu φ 0).1.add
    (integrable_and_integral_partialDeriv_mul (g := fun y ↦ flux (u y)) (hflux.comp hu) φ 1).1
    ).congr (.of_forall fun x ↦ by simp [fluxResidual, add_mul])

private theorem integral_fluxResidual_mul_eq_neg_integral_weakIntegrand
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u) (φ : 𝓓^{1}(U, ℝ)) :
    (∫ x : ℝ^2, fluxResidual flux u x * φ x ∂MeasureTheory.volume) =
      -∫ x : ℝ^2, weakIntegrand flux u φ x
        ∂MeasureTheory.volume := by
  obtain ⟨hI0, h0⟩ := integrable_and_integral_partialDeriv_mul hu φ 0
  obtain ⟨hI1, h1⟩ := integrable_and_integral_partialDeriv_mul (g := fun y ↦ flux (u y))
    (hflux.comp hu) φ 1
  simp only [fluxResidual, weakIntegrand, add_mul]
  rw [MeasureTheory.integral_add hI0 hI1, h0, h1, MeasureTheory.integral_add
    (φ.integrable_mul_partialDeriv (hu.continuous.locallyIntegrable.locallyIntegrableOn U) 0)
    (φ.integrable_mul_partialDeriv (g := fun y ↦ flux (u y))
      ((hflux.comp hu).continuous.locallyIntegrable.locallyIntegrableOn U) 1)]
  ring

/-- For a `C¹` flux and a `C¹` candidate, the residual-test identity implies the standard weak
formulation. Integration by parts moves the derivatives off `u` and `flux ∘ u` onto the compactly
supported test function with no boundary term; local integrability of `u` and `flux ∘ u` follows
from continuity. -/
theorem isWeakSolution_of_satisfiesResidualTestIdentity_of_contDiff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u)
    (hDist : SatisfiesResidualTestIdentity flux U u) :
    IsWeakSolution flux U u := by
  refine
    { u_locallyIntegrable := hu.continuous.locallyIntegrable.locallyIntegrableOn U
      flux_locallyIntegrable :=
        (hflux.comp hu).continuous.locallyIntegrable.locallyIntegrableOn U
      weak_eq := ?_ }
  intro φ
  have hid := integral_fluxResidual_mul_eq_neg_integral_weakIntegrand hflux hu φ
  rw [hDist.identity φ] at hid
  exact neg_eq_zero.mp hid.symm

/-- For a `C¹` flux and a `C¹` candidate, the standard weak formulation implies the
residual-test identity: the same integration by parts read in reverse, together with
integrability of the tested residual. -/
theorem satisfiesResidualTestIdentity_of_isWeakSolution_of_contDiff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u)
    (hWeak : IsWeakSolution flux U u) :
    SatisfiesResidualTestIdentity flux U u := by
  refine ⟨integrable_fluxResidual_mul hflux hu, ?_⟩
  intro φ
  rw [integral_fluxResidual_mul_eq_neg_integral_weakIntegrand hflux hu φ,
    hWeak.weak_eq φ, neg_zero]

/-- Under `C¹` regularity, the classical residual-test identity and the standard weak
formulation are equivalent. Integration by parts gives the passage from classical flux-form
identities to weak conservation laws. -/
theorem satisfiesResidualTestIdentity_iff_isWeakSolution_of_contDiff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u) :
    SatisfiesResidualTestIdentity flux U u ↔ IsWeakSolution flux U u := by
  constructor
  · exact isWeakSolution_of_satisfiesResidualTestIdentity_of_contDiff
      (flux := flux) (U := U) (u := u) hflux hu
  · exact satisfiesResidualTestIdentity_of_isWeakSolution_of_contDiff
      (flux := flux) (U := U) (u := u) hflux hu

/-! ## Pointwise residual to residual-test identity -/

/-- A pointwise zero flux residual has zero integral against every compactly supported test
function in `U`. Regularity is required separately to infer the distributional equation. -/
theorem satisfiesResidualTestIdentity_of_pointwise
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hpde : ∀ x ∈ U, fluxResidual flux u x = 0) :
    SatisfiesResidualTestIdentity flux U u := by
  have hzero (φ : 𝓓^{1}(U, ℝ)) :
      (fun x : ℝ^2 ↦ fluxResidual flux u x * φ x) = 0 := by
    funext x
    by_cases hx : x ∈ U
    · rw [hpde x hx]
      simp
    · rw [φ.zero_on_compl hx]
      simp
  refine ⟨?_, ?_⟩
  · intro φ
    simp [hzero φ]
  · intro φ
    simp [hzero φ]

/-- A `C¹` classical flux-form solution is a weak solution. This combines the pointwise
residual theorem with integration by parts without boundary terms, as in the
standard Evans passage from classical to weak solutions. -/
theorem isWeakSolution_of_pointwise_of_contDiff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u)
    (hpde : ∀ x ∈ U, fluxResidual flux u x = 0) :
    IsWeakSolution flux U u :=
  isWeakSolution_of_satisfiesResidualTestIdentity_of_contDiff (flux := flux) (U := U) (u := u)
    hflux hu (satisfiesResidualTestIdentity_of_pointwise (flux := flux) (U := U) (u := u)
      hpde)

/-- A classical solution of the bundled one-dimensional conservation law is a weak solution.
The scalar flux is the sole component of the spatial flux vector. -/
theorem isWeakSolution_of_satisfiesPDEProblem_of_contDiff
    {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hu : ContDiff ℝ 1 u)
    (hsol : SatisfiesPDEProblem
      (conservationLawEquation (fun z ↦ EuclideanSpace.single (0 : Fin 1) (flux z)) U)
      u) :
    IsWeakSolution flux U u := by
  apply isWeakSolution_of_pointwise_of_contDiff hflux hu
  intro x hx
  simpa [fluxResidual, Fin.sum_univ_one] using
    (conservationLawEquation_iff.mp hsol x hx)

end

end PDE.Hyperbolic.ConservationLaw.Scalar
