/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
public import PDE.Hyperbolic.ConservationLaw.Scalar.Weak
import PDE.Hyperbolic.ConservationLaw.InteriorWeakForm
import PDE.DistributionTheory.TestFunction
import PDE.FDeriv.Calculus

/-!
# Weak entropy solutions for one-dimensional scalar conservation laws

For

`u_t + (f(u))_x = 0`

we define the weak entropy inequality for convex entropy pairs, prove its
stability under domain restriction and almost-everywhere equality, and
connect smooth entropy-residual identities to entropy weak solutions by
integration by parts. The underlying entropy pairs and algebraic shock
admissibility conditions are defined in
`PDE.Hyperbolic.ConservationLaw.Scalar.Entropy`; the ordinary weak formulation
is defined in `PDE.Hyperbolic.ConservationLaw.Scalar.Weak`.

The inequality against nonnegative tests is (38) of Evans, §11.4.3, written on an open set of
spacetime, with Evans's convex entropy pairs (36)-(37).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, equation (27); §11.4.3, equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open PDE.Common TopologicalSpace

open scoped Distributions Topology

/-! ## Classical entropy-residual identities -/

/-- Entropy residual `∂t η(u) + ∂x q(u)` for a flux entropy pair. -/
noncomputable def entropyResidual
    (flux : ℝ → ℝ) (E : EntropyPair (fun r ↦ deriv flux r))
    (u : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ E.η (u y))) x +
    (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ E.q (u y))) x

/-- Every `C¹` entropy pair has an integrable residual with zero integral against each compactly
supported `C¹` test.

This is the classical identity. Entropy admissibility for nonsmooth solutions is the one-sided
weak inequality below and is restricted to convex entropies. Quantifying a one-sided inequality
over all entropy pairs would also quantify over their negatives and collapse it to equality.

The quantification here is over the bundled `C¹` `EntropyPair` structure, not the
nonsmooth Kružkov entropy family. -/
def SatisfiesEntropyResidualIdentity
    (flux : ℝ → ℝ) (U : Opens ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  ∀ E : EntropyPair (fun r ↦ deriv flux r),
    ∀ φ : 𝓓^{1}(U, ℝ),
      MeasureTheory.Integrable
          (fun x : ℝ^2 ↦ entropyResidual flux E u x * φ x)
          MeasureTheory.volume ∧
        ∫ x : ℝ^2, entropyResidual flux E u x * φ x
          ∂MeasureTheory.volume = 0

/-! ### Standard weak entropy inequality (test-function derivatives)

For `φ ≥ 0`, the distributional inequality

`∫ (∂t η(u) + ∂x q(u)) φ ≤ 0`

is equivalent (by integration by parts, no boundary term) to

`0 ≤ ∫ (η(u) φ_t + q(u) φ_x)`.
-/

/-- Integrand in the weak entropy inequality for one entropy pair. -/
def entropyWeakIntegrand
    (u : ℝ^2 → ℝ) {a : ℝ → ℝ} (E : EntropyPair a)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ))
    (x : ℝ^2) : ℝ :=
  E.η (u x) * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x +
    E.q (u x) * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x

/-- Local integrability of an entropy density and flux makes the weak entropy integrand
globally integrable. -/
theorem integrable_entropyWeakIntegrand {U : Opens ℝ^2} {u : ℝ^2 → ℝ} {a : ℝ → ℝ}
    {E : EntropyPair a} (φ : 𝓓^{1}(U, ℝ))
    (hη : MeasureTheory.LocallyIntegrableOn (fun x : ℝ^2 ↦ E.η (u x)) U MeasureTheory.volume)
    (hq : MeasureTheory.LocallyIntegrableOn (fun x : ℝ^2 ↦ E.q (u x)) U MeasureTheory.volume) :
    MeasureTheory.Integrable (entropyWeakIntegrand u E φ) MeasureTheory.volume :=
  (φ.integrable_mul_partialDeriv hη 0).add (φ.integrable_mul_partialDeriv hq 1)

/-- The weak entropy inequality for one `C¹` entropy pair.

The first two conjuncts state local integrability of `η(u)` and `q(u)`;
the third is the distributional inequality against nonnegative tests. -/
def SatisfiesEntropyInequalityFor
    (U : Opens ℝ^2) (u : ℝ^2 → ℝ)
    {a : ℝ → ℝ} (E : EntropyPair a) : Prop :=
  MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ^2 ↦ E.η (u x)) U MeasureTheory.volume ∧
    MeasureTheory.LocallyIntegrableOn
      (fun x : ℝ^2 ↦ E.q (u x)) U MeasureTheory.volume ∧
    ∀ φ : 𝓓^{1}(U, ℝ),
      (∀ x : ℝ^2, 0 ≤ φ x) →
        0 ≤ ∫ x : ℝ^2, entropyWeakIntegrand u E φ x
          ∂MeasureTheory.volume

/-- Every integrand occurring in a one-pair weak entropy inequality is integrable. -/
theorem SatisfiesEntropyInequalityFor.integrable_entropyWeakIntegrand {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    {a : ℝ → ℝ} {E : EntropyPair a} (hE : SatisfiesEntropyInequalityFor U u E) (φ : 𝓓^{1}(U, ℝ)) :
    MeasureTheory.Integrable (entropyWeakIntegrand u E φ) MeasureTheory.volume :=
  PDE.Hyperbolic.ConservationLaw.Scalar.integrable_entropyWeakIntegrand φ hE.1 hE.2.1

/-- Restrict a one-pair weak entropy condition to a smaller domain. -/
theorem SatisfiesEntropyInequalityFor.mono_domain {U V : Opens ℝ^2} {u : ℝ^2 → ℝ} {a : ℝ → ℝ}
    {E : EntropyPair a} (hE : SatisfiesEntropyInequalityFor V u E) (hUV : U ≤ V) :
    SatisfiesEntropyInequalityFor U u E := by
  refine ⟨hE.1.mono_set hUV, hE.2.1.mono_set hUV, fun φ hφ_nonneg ↦ ?_⟩
  simpa [entropyWeakIntegrand, hUV] using hE.2.2 (TestFunction.monoCLM ℝ φ)
    fun x ↦ by simpa [hUV] using hφ_nonneg x

/-- The weak entropy inequality depends only on the representative inside
its domain. Test derivatives vanish outside that domain. -/
theorem SatisfiesEntropyInequalityFor.congr_ae_restrict {U : Opens ℝ^2} {u v : ℝ^2 → ℝ} {a : ℝ → ℝ}
    {E : EntropyPair a} (hE : SatisfiesEntropyInequalityFor U u E)
    (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    SatisfiesEntropyInequalityFor U v E := by
  have hηU : (fun x : ℝ^2 ↦ E.η (u x)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x ↦ E.η (v x) := huv.fun_comp E.η
  have hqU : (fun x : ℝ^2 ↦ E.q (u x)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x ↦ E.q (v x) := huv.fun_comp E.q
  refine ⟨hE.1.congr hηU, hE.2.1.congr hqU, fun φ hφ_nonneg ↦ ?_⟩
  rw [← MeasureTheory.integral_congr_ae (g := entropyWeakIntegrand v E φ) (by
    filter_upwards [InteriorWeakForm.integrand_congr_ae_restrict hηU hqU φ] with p hp
    simpa only [entropyWeakIntegrand, InteriorWeakForm.integrand, smul_eq_mul, mul_comm] using hp)]
  exact hE.2.2 φ hφ_nonneg

/-- The weak entropy inequality for one entropy pair is invariant under
global almost-everywhere changes of representative. -/
theorem SatisfiesEntropyInequalityFor.congr_ae {U : Opens ℝ^2} {u v : ℝ^2 → ℝ} {a : ℝ → ℝ}
    {E : EntropyPair a} (hE : SatisfiesEntropyInequalityFor U u E)
    (huv : u =ᵐ[MeasureTheory.volume] v) :
    SatisfiesEntropyInequalityFor U v E :=
  hE.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-- The weak entropy inequality for every `C¹` convex entropy pair.

The quantification is over `C¹` entropy pairs whose entropy `η` is convex. Convexity is
essential: requiring the same one-sided inequality for every entropy pair would also require it
for the negated pair and would therefore collapse the inequality to equality, excluding every
shock that dissipates entropy.

The predicate is stated for any `flux` and uses `deriv flux` in the compatibility relation. It
is the standard notion when `flux` is `C¹`, which every theorem that uses it assumes. Because
`η` ranges over all convex `C¹` functions, the local integrability clauses force `u` to be
locally essentially bounded on `U`. -/
def SatisfiesEntropyInequality
    (flux : ℝ → ℝ) (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ) : Prop :=
  ∀ E : EntropyPair (fun r ↦ deriv flux r),
    ConvexOn ℝ Set.univ E.η → SatisfiesEntropyInequalityFor U u E

/-- The weak entropy inequality on `V` restricts to every smaller domain `U ⊆ V`. -/
theorem SatisfiesEntropyInequality.mono_domain {flux : ℝ → ℝ} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hu : SatisfiesEntropyInequality flux V u) (hUV : U ≤ V) :
    SatisfiesEntropyInequality flux U u :=
  fun E hE_convex ↦ (hu E hE_convex).mono_domain hUV

/-- The weak entropy condition is invariant under almost-everywhere changes of representative. -/
theorem SatisfiesEntropyInequality.congr_ae_restrict {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : SatisfiesEntropyInequality flux U u) (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    SatisfiesEntropyInequality flux U v :=
  fun E hE_convex ↦ (hu E hE_convex).congr_ae_restrict huv

/-- The weak entropy condition is invariant under global almost-everywhere
changes of representative. -/
theorem SatisfiesEntropyInequality.congr_ae {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : SatisfiesEntropyInequality flux U u) (huv : u =ᵐ[MeasureTheory.volume] v) :
    SatisfiesEntropyInequality flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

/-- Weak entropy solution using the standard convex-entropy inequality. -/
def IsEntropyWeakSolution
    (flux : ℝ → ℝ) (U : Opens ℝ^2) (u : ℝ^2 → ℝ)
  : Prop :=
  IsWeakSolution flux U u ∧ SatisfiesEntropyInequality flux U u

namespace IsEntropyWeakSolution

/-- An entropy weak solution is, in particular, a weak solution. -/
theorem weak {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ} (hu : IsEntropyWeakSolution flux U u) :
    IsWeakSolution flux U u :=
  hu.1

/-- An entropy weak solution satisfies the weak entropy inequality. -/
theorem entropy {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ} (hu : IsEntropyWeakSolution flux U u) :
    SatisfiesEntropyInequality flux U u :=
  hu.2

/-- An entropy weak solution on `V` restricts to every smaller domain `U ⊆ V`. -/
theorem mono_domain {flux : ℝ → ℝ} {U V : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux V u) (hUV : U ≤ V) :
    IsEntropyWeakSolution flux U u :=
  ⟨hu.1.mono_domain hUV, hu.2.mono_domain hUV⟩

/-- Entropy weak solutions depend only on the representative inside the domain. -/
theorem congr_ae_restrict {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume.restrict U] v) :
    IsEntropyWeakSolution flux U v :=
  ⟨hu.1.congr_ae_restrict huv, hu.2.congr_ae_restrict huv⟩

/-- Entropy weak solutions are invariant under global almost-everywhere
changes of representative. -/
theorem congr_ae {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux U u) (huv : u =ᵐ[MeasureTheory.volume] v) :
    IsEntropyWeakSolution flux U v :=
  hu.congr_ae_restrict (MeasureTheory.ae_restrict_of_ae huv)

end IsEntropyWeakSolution

private theorem integral_entropyResidual_mul_eq_neg_integral_entropyWeakIntegrand {flux : ℝ → ℝ}
    {U : Opens ℝ^2} {u : ℝ^2 → ℝ} (hu : ContDiff ℝ 1 u) (E : EntropyPair (fun r ↦ deriv flux r))
    (φ : 𝓓^{1}(U, ℝ)) :
    (∫ x : ℝ^2, entropyResidual flux E u x * φ x ∂MeasureTheory.volume) = -∫ x : ℝ^2,
      entropyWeakIntegrand u E φ x ∂MeasureTheory.volume := by
  obtain ⟨hI0, h0⟩ := integrable_and_integral_partialDeriv_mul (g := fun y ↦ E.η (u y))
    (E.eta_contDiff.comp hu) φ 0
  obtain ⟨hI1, h1⟩ := integrable_and_integral_partialDeriv_mul (g := fun y ↦ E.q (u y))
    (E.entropyFlux_contDiff.comp hu) φ 1
  simp only [entropyResidual, entropyWeakIntegrand, add_mul]
  rw [MeasureTheory.integral_add hI0 hI1, h0, h1, MeasureTheory.integral_add
    (φ.integrable_mul_partialDeriv (g := fun y ↦ E.η (u y))
      ((E.eta_contDiff.comp hu).continuous.locallyIntegrable.locallyIntegrableOn U) 0)
    (φ.integrable_mul_partialDeriv (g := fun y ↦ E.q (u y))
      ((E.entropyFlux_contDiff.comp hu).continuous.locallyIntegrable.locallyIntegrableOn U) 1)]
  ring

/-- A `C¹` solution satisfying every classical entropy-residual identity obeys the weak
inequality for every convex member of the bundled `C¹` entropy-pair family. -/
theorem satisfiesEntropyInequality_of_entropyResidualIdentity_of_contDiff {flux : ℝ → ℝ}
    {U : Opens ℝ^2} {u : ℝ^2 → ℝ} (hu : ContDiff ℝ 1 u)
    (hEnt : SatisfiesEntropyResidualIdentity flux U u) :
    SatisfiesEntropyInequality flux U u := by
  intro E _hE_convex
  refine ⟨(E.eta_contDiff.comp hu).continuous.locallyIntegrable.locallyIntegrableOn U,
      (E.entropyFlux_contDiff.comp hu).continuous.locallyIntegrable
        |>.locallyIntegrableOn U, ?_⟩
  intro φ _hφnonneg
  linarith [integral_entropyResidual_mul_eq_neg_integral_entropyWeakIntegrand hu E φ, (hEnt E φ).2]

/-! ## Classical solutions and entropy residuals

This uses the pointwise entropy identity from
`PDE.Hyperbolic.ConservationLaw.Scalar.Entropy`.
-/

/-- At a differentiability point, a solution of the flux equation satisfies the entropy
balance with equality for every entropy pair. -/
theorem entropyResidual_eq_zero_of_flux_pde {flux : ℝ → ℝ} (hflux : Differentiable ℝ flux)
    {E : EntropyPair (fun r ↦ deriv flux r)} {u : ℝ^2 → ℝ} {x : ℝ^2} (hu : DifferentiableAt ℝ u x)
    (hpde : fluxResidual flux u x = 0) :
    entropyResidual flux E u x = 0 := by
  have hpde' : (∂[(0 : Fin 2)] u) x + deriv flux (u x) * (∂[(1 : Fin 2)] u) x = 0 := by
    simpa [fluxResidual, partialDeriv_comp_real (i := (1 : Fin 2)) hflux.differentiableAt hu,
      mul_comm] using hpde
  simpa [entropyResidual] using entropy_identity_of_pde (a := fun r ↦ deriv flux r) (E := E) hu
    hpde'

/-- A pointwise differentiable flux-form solution has an integrable, vanishing tested entropy
residual for every bundled `C¹` entropy pair. -/
theorem satisfiesEntropyResidualIdentity_of_pointwise {flux : ℝ → ℝ} (hflux : ContDiff ℝ 1 flux)
    {U : Opens ℝ^2} {u : ℝ^2 → ℝ} (hu : ∀ x ∈ U, DifferentiableAt ℝ u x)
    (hpde : ∀ x ∈ U, fluxResidual flux u x = 0) :
    SatisfiesEntropyResidualIdentity flux U u := by
  intro E φ
  have : (fun x : ℝ^2 ↦ entropyResidual flux E u x * φ x) = 0 := by
    funext x
    by_cases hx : x ∈ U
    · simp [entropyResidual_eq_zero_of_flux_pde hflux.differentiable_one (E := E) (hu x hx)
        (hpde x hx)]
    · simp [φ.zero_on_compl hx]
  simp [this]

/-- A `C¹` classical flux-form solution is an entropy weak solution. This is the computation (27)
of Evans, §11.4.2, tested against nonnegative test functions. -/
theorem isEntropyWeakSolution_of_pointwise_of_contDiff {flux : ℝ → ℝ}
    {U : Opens ℝ^2} (hflux : ContDiff ℝ 1 flux) {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 1 u) (hpde : ∀ x ∈ U, fluxResidual flux u x = 0) :
    IsEntropyWeakSolution flux U u :=
  ⟨isWeakSolution_of_pointwise_of_contDiff hflux hu hpde,
    satisfiesEntropyInequality_of_entropyResidualIdentity_of_contDiff hu
      (satisfiesEntropyResidualIdentity_of_pointwise hflux
        (fun _ _ ↦ hu.differentiable_one.differentiableAt) hpde)⟩

/-! ## Constant solutions -/

/-- Constant states have zero flux-form residual for every flux. -/
theorem fluxResidual_const (flux : ℝ → ℝ) (c : ℝ) (x : ℝ^2) :
    fluxResidual flux (fun _ : ℝ^2 ↦ c) x = 0 := by
  simp [fluxResidual, partialDeriv_const]

/-- Constant states satisfy the classical residual-test identity on every open domain. -/
theorem satisfiesResidualTestIdentity_const (flux : ℝ → ℝ) (U : Opens ℝ^2) (c : ℝ) :
    SatisfiesResidualTestIdentity flux U (fun _ : ℝ^2 ↦ c) :=
  satisfiesResidualTestIdentity_of_pointwise (u := fun _ : ℝ^2 ↦ c)
    fun x _ ↦ fluxResidual_const flux c x

/-- Constant states satisfy every classical entropy residual identity. -/
theorem satisfiesEntropyResidualIdentity_const {flux : ℝ → ℝ} (hflux : ContDiff ℝ 1 flux)
    (U : Opens ℝ^2) (c : ℝ) :
    SatisfiesEntropyResidualIdentity flux U (fun _ : ℝ^2 ↦ c) :=
  satisfiesEntropyResidualIdentity_of_pointwise hflux (u := fun _ : ℝ^2 ↦ c)
    (fun _ _ ↦ by fun_prop) fun x _ ↦ fluxResidual_const flux c x

/-- Constant states are weak solutions on every open domain for every flux. -/
theorem isWeakSolution_const {flux : ℝ → ℝ}
    (U : Opens ℝ^2) (c : ℝ) :
    IsWeakSolution flux U (fun _ : ℝ^2 ↦ c) where
  u_locallyIntegrable := MeasureTheory.locallyIntegrableOn_const c
  flux_locallyIntegrable := MeasureTheory.locallyIntegrableOn_const (flux c)
  weak_eq := integral_weakIntegrand_const_eq_zero flux c

/-- Constant states are entropy weak solutions on every open domain for every flux. -/
theorem isEntropyWeakSolution_const {flux : ℝ → ℝ}
    (U : Opens ℝ^2) (c : ℝ) :
    IsEntropyWeakSolution flux U (fun _ : ℝ^2 ↦ c) :=
  ⟨isWeakSolution_const U c, fun E _ ↦ ⟨MeasureTheory.locallyIntegrableOn_const (E.η c),
    MeasureTheory.locallyIntegrableOn_const (E.q c), fun φ _ ↦ le_of_eq (by
      simpa [weakIntegrand, entropyWeakIntegrand] using
        (integral_weakIntegrand_const_eq_zero (fun _ ↦ E.q c) (E.η c) φ).symm)⟩⟩

end

end PDE.Hyperbolic.ConservationLaw.Scalar
