/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.BoundedComposition
public import PDE.DistributionTheory.TestFunction.NonnegativeTesting
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Approximation
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.WeakEquation

/-!
# From smooth entropy inequalities to C¹ entropy inequalities

The entropy inequalities (38) of Evans, §11.4.3, test smooth convex entropy pairs, in the sense
of (36)-(37), against nonnegative tests in `C_c^∞(ℝ × (0, ∞))`. For a bounded measurable state
and smooth flux, this is equivalent to the C¹ entropy inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, definition of entropy/entropy-flux pair,
  equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology ContDiff

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The interior entropy inequality with Evans's smooth entropy and test classes.
Integrability follows from a measurable essentially bounded state. -/
def SatisfiesSmoothEntropyInequality (flux : ℝ → ℝ) (U : Opens ℝ^2)
    (u : ℝ^2 → ℝ) : Prop :=
  ∀ E : EntropyPair (deriv flux),
    ContDiff ℝ ∞ E.η → ContDiff ℝ ∞ E.q → ConvexOn ℝ univ E.η →
    ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, E.η (u x) * (∂[0] (φ : ℝ^2 → ℝ)) x + E.q (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x

variable {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}

/-- For one smooth pair, smooth nonnegative tests imply the compact C¹ test inequality. -/
theorem SatisfiesSmoothEntropyInequality.satisfiesEntropyInequalityFor
    (h : SatisfiesSmoothEntropyInequality flux U u)
    (hu : AEStronglyMeasurable u (volume.restrict U)) {M : ℝ}
    (hM : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) (E : EntropyPair (deriv flux)) (hη : ContDiff ℝ ∞ E.η)
    (hq : ContDiff ℝ ∞ E.q) (hconvex : ConvexOn ℝ univ E.η) :
    SatisfiesEntropyInequalityFor U u E := by
  have hηint := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hu hM hη.continuous)
  have hqint := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hu hM hq.continuous)
  exact ⟨hηint, hqint, fun φ hφ ↦
    TestFunction.nonneg_integral_mul_partialDeriv_of_smooth hηint hqint 0 1
      (h E hη hq hconvex) φ hφ⟩

private theorem tendsto_integral_comp_partialDeriv (hu : AEStronglyMeasurable u (volume.restrict U))
    {M : ℝ} (hM : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) {f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hf : Continuous f) (hF : ∀ j, Continuous (F j)) (hconv : TendstoLocallyUniformly F f atTop)
    (φ : 𝓓^{1}(U, ℝ)) (i : Fin 2) :
    Tendsto (fun j ↦ ∫ x, F j (u x) * (∂[i] (φ : ℝ^2 → ℝ)) x) atTop
      (𝓝 (∫ x, f (u x) * (∂[i] (φ : ℝ^2 → ℝ)) x)) := by
  have hlim := tendsto_integral_comp_mul_of_ae_bound hu hM hf hF hconv
    (φ.integrable_partialDeriv i).restrict
  have heq (g : ℝ → ℝ) : (∫ x in U, g (u x) * (∂[i] (φ : ℝ^2 → ℝ)) x) =
        ∫ x, g (u x) * (∂[i] (φ : ℝ^2 → ℝ)) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [φ.partialDeriv_eq_zero_of_notMem hx i, mul_zero]
  simpa only [heq] using hlim

/-- Smooth entropy pairs and smooth tests imply the full C¹ entropy inequality.
The scalar flux is smooth; it need not be convex. -/
theorem SatisfiesSmoothEntropyInequality.satisfiesEntropyInequality
    (h : SatisfiesSmoothEntropyInequality flux U u) (hf : ContDiff ℝ ∞ flux)
    (hu : AEStronglyMeasurable u (volume.restrict U)) {M : ℝ}
    (hM : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) :
    SatisfiesEntropyInequality flux U u := by
  intro E hconvex
  obtain ⟨A, hA, hηlim, hqlim⟩ :=
    E.exists_smooth_convex_approximation (contDiff_infty_iff_deriv.mp hf).2 hconvex
  have hAE (j : ℕ) : SatisfiesEntropyInequalityFor U u (A j) :=
    h.satisfiesEntropyInequalityFor hu hM (A j) (hA j).1 (hA j).2.1 (hA j).2.2
  have hηint := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hu hM E.eta_contDiff.continuous)
  have hqint := locallyIntegrableOn_of_locallyIntegrable_restrict
    (locallyIntegrable_comp_of_ae_bound hu hM E.entropyFlux_contDiff.continuous)
  refine ⟨hηint, hqint, fun φ hφ ↦ ?_⟩
  have hlim := (tendsto_integral_comp_partialDeriv hu hM E.eta_contDiff.continuous
      (fun j ↦ (hA j).1.continuous) hηlim φ 0).add
    (tendsto_integral_comp_partialDeriv hu hM E.entropyFlux_contDiff.continuous
      (fun j ↦ (hA j).2.1.continuous) hqlim φ 1)
  have heq (j : ℕ) : (∫ x, entropyWeakIntegrand u (A j) φ x) =
        (∫ x, (A j).η (u x) * (∂[0] (φ : ℝ^2 → ℝ)) x) +
          ∫ x, (A j).q (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x :=
    integral_add (φ.integrable_mul_partialDeriv (hAE j).1 0)
      (φ.integrable_mul_partialDeriv (hAE j).2.1 1)
  rw [← integral_add (φ.integrable_mul_partialDeriv hηint 0)
    (φ.integrable_mul_partialDeriv hqint 1)] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun j ↦ by
    rw [← heq]
    exact (hAE j).2.2 φ hφ)

/-- The C¹ entropy inequality includes Evans's smooth testing class. -/
theorem SatisfiesEntropyInequality.satisfiesSmoothEntropyInequality
    (h : SatisfiesEntropyInequality flux U u) :
    SatisfiesSmoothEntropyInequality flux U u := by
  intro E _ _ hconvex φ hφ
  let ψ : 𝓓^{1}(U, ℝ) :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  exact (h E hconvex).2.2 ψ hφ

/-- Evans's smooth entropy and test classes imply the entropy weak solution
predicate, including the ordinary weak equation obtained from affine entropies. -/
theorem SatisfiesSmoothEntropyInequality.isEntropyWeakSolution
    (h : SatisfiesSmoothEntropyInequality flux U u) (hf : ContDiff ℝ ∞ flux)
    (hu : AEStronglyMeasurable u (volume.restrict U)) {M : ℝ}
    (hM : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) :
    IsEntropyWeakSolution flux U u := by
  have hE := h.satisfiesEntropyInequality hf hu hM
  exact ⟨hE.isWeakSolution (hf.of_le (by simp)), hE⟩

end PDE.Hyperbolic.ConservationLaw.Scalar
