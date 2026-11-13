/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Approximation
import PDE.DistributionTheory.TestFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# From smooth convex entropies to the Kružkov inequalities

A locally essentially bounded scalar entropy weak solution for a `C¹` flux
satisfies the nonsmooth absolute-value entropy inequality. The approximating
entropy pairs, their convexity, and both coefficient limits are constructed in
`Kruzhkov.Approximation`. On the compact support of a test, local boundedness
gives a common coefficient bound. The integrable norms of the test derivatives
then permit dominated convergence in the weak inequality. The inequality is the
interior distributional one, on any open spacetime domain.

The inequality is (41) of Evans, §11.4.3, which step 1 of the proof of Theorem 3 derives in
the same way from the approximation (40) of `|z - α|`; `kruzhkovFlux` is its flux
`sgn(z - α)(F(z) - F(α))`. Evans assumes a smooth flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 1, equations (39)-(41).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The nonsmooth scalar entropy flux associated with `|r - k|`. -/
def kruzhkovFlux (flux : ℝ → ℝ) (k r : ℝ) : ℝ :=
  Real.sign (r - k) * (flux r - flux k)

/-- The absolute-value entropy tested with derivatives of a compactly supported test. -/
def kruzhkovWeakIntegrand (flux : ℝ → ℝ) (u : ℝ^2 → ℝ) (k : ℝ)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ)) (x : ℝ^2) : ℝ :=
  |u x - k| * (∂[0] (φ : ℝ^2 → ℝ)) x + kruzhkovFlux flux k (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x

/-- The full family of interior scalar Kružkov inequalities, with local integrability
of the entropy density and flux included. -/
def SatisfiesKruzhkovInequality (flux : ℝ → ℝ) (U : Opens ℝ^2) (u : ℝ^2 → ℝ) : Prop :=
  ∀ k : ℝ,
    LocallyIntegrableOn (fun x ↦ |u x - k|) U volume ∧
    LocallyIntegrableOn (fun x ↦ kruzhkovFlux flux k (u x)) U volume ∧
    ∀ φ : 𝓓^{1}(U, ℝ), (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, kruzhkovWeakIntegrand flux u k φ x

/-- The Kružkov flux is bounded in norm by the physical flux difference. -/
theorem norm_kruzhkovFlux_le (flux : ℝ → ℝ) (k r : ℝ) :
    ‖kruzhkovFlux flux k r‖ ≤ ‖flux r - flux k‖ := by
  have hs : ‖Real.sign (r - k)‖ ≤ 1 := le_of_tendsto (Kruzhkov.tendsto_smoothSign k r).norm
      (Eventually.of_forall fun n ↦ Kruzhkov.norm_smoothSign_le n k r)
  unfold kruzhkovFlux
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans_eq (one_mul _)

/-- Every tested Kružkov integrand is integrable. -/
theorem SatisfiesKruzhkovInequality.integrable {flux : ℝ → ℝ} {U : Opens ℝ^2} {u : ℝ^2 → ℝ}
    (hu : SatisfiesKruzhkovInequality flux U u) (k : ℝ) (φ : 𝓓^{1}(U, ℝ)) :
    Integrable (kruzhkovWeakIntegrand flux u k φ) volume :=
  (φ.integrable_mul_partialDeriv (hu k).1 0).add (φ.integrable_mul_partialDeriv (hu k).2.1 1)

/-- Smooth convex entropy inequalities imply every Kružkov inequality for a locally
essentially bounded scalar weak solution with `C¹` flux.

The local bound is required only on compact subsets of the open domain and may hold almost
everywhere. Neither an absolute-value entropy inequality nor convergence of entropy fluxes
is a hypothesis. -/
theorem IsEntropyWeakSolution.satisfiesKruzhkovInequality {flux : ℝ → ℝ} {U : Opens ℝ^2}
    {u : ℝ^2 → ℝ} (hu : IsEntropyWeakSolution flux U u) (hf : ContDiff ℝ 1 flux)
    (hbound : ∀ K : Set ℝ^2, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖u x‖ ≤ M) :
    SatisfiesKruzhkovInequality flux U u := by
  intro k
  have hE (n : ℕ) : SatisfiesEntropyInequalityFor U u (Kruzhkov.smoothEntropyPair hf n k) :=
    hu.entropy _ (Kruzhkov.convexOn_smoothEntropy n k)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hu.weak.u_locallyIntegrable.sub (locallyIntegrableOn_const k)).norm
  · refine (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).2 fun K hKU hK ↦ ?_
    have hmeas : AEStronglyMeasurable (fun x ↦ kruzhkovFlux flux k (u x)) (volume.restrict K) :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n ↦ ((hE n).2.1.integrableOn_compact_subset hKU hK).aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ Kruzhkov.tendsto_smoothEntropyFlux hf k (u x))
    apply ((hu.weak.flux_locallyIntegrable.integrableOn_compact_subset hKU hK).sub
      (integrableOn_const hK.measure_ne_top (C := flux k))).norm.mono' hmeas
    exact Eventually.of_forall fun x ↦ norm_kruzhkovFlux_le flux k (u x)
  · intro φ hφ
    obtain ⟨M, hM⟩ := hbound (tsupport (φ : ℝ^2 → ℝ)) φ.tsupport_subset φ.hasCompactSupport
    obtain ⟨B, _hB, hcoeff⟩ := Kruzhkov.exists_bound_smoothEntropyPair hf k M
    let bound : ℝ^2 → ℝ := fun x ↦ B * ‖(∂[0] (φ : ℝ^2 → ℝ)) x‖ + B * ‖(∂[1] (φ : ℝ^2 → ℝ)) x‖
    have hboundInt : Integrable bound volume := ((φ.integrable_partialDeriv 0).norm.const_mul B).add
        ((φ.integrable_partialDeriv 1).norm.const_mul B)
    have hdom (n : ℕ) :
        ∀ᵐ x, ‖entropyWeakIntegrand u (Kruzhkov.smoothEntropyPair hf n k) φ x‖ ≤ bound x := by
      have hM' := (ae_restrict_iff' (isClosed_tsupport _).measurableSet).1 hM
      filter_upwards [hM'] with x hx
      by_cases hxs : x ∈ tsupport (φ : ℝ^2 → ℝ)
      · obtain ⟨hη, hq⟩ := hcoeff n (u x) (hx hxs)
        change ‖Kruzhkov.smoothEntropy n k (u x) * (∂[0] (φ : ℝ^2 → ℝ)) x +
          Kruzhkov.smoothEntropyFlux flux n k (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x‖ ≤ _
        apply (norm_add_le _ _).trans
        simp only [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hη (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
      · simp [entropyWeakIntegrand, bound, φ.partialDeriv_eq_zero_of_notMem_tsupport hxs]
    have hlim : Tendsto
          (fun n ↦ ∫ x, entropyWeakIntegrand u (Kruzhkov.smoothEntropyPair hf n k) φ x)
          atTop (𝓝 (∫ x, kruzhkovWeakIntegrand flux u k φ x)) := by
      apply tendsto_integral_of_dominated_convergence bound
        (fun n ↦ ((hE n).integrable_entropyWeakIntegrand φ).aestronglyMeasurable) hboundInt hdom
      exact Eventually.of_forall fun x ↦
        ((Kruzhkov.tendsto_smoothEntropy k (u x)).mul_const ((∂[0] (φ : ℝ^2 → ℝ)) x)).add
          ((Kruzhkov.tendsto_smoothEntropyFlux hf k (u x)).mul_const ((∂[1] (φ : ℝ^2 → ℝ)) x))
    exact ge_of_tendsto hlim (Eventually.of_forall fun n ↦ (hE n).2.2 φ hφ)

end PDE.Hyperbolic.ConservationLaw.Scalar
