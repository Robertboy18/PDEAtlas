/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.InitialComparison
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.SpatialLocalization

/-!
# Local contraction for scalar entropy solutions

Uniformly essentially bounded entropy solutions with strong local `L¹` initial
traces satisfy the finite-speed local contraction estimate at almost every positive
time. The proof uses the derived doubled inequality, its spacetime diagonal limit,
and the time and cone cutoffs. No positive-time representative is prescribed.

Step 4 of the proof of Evans, §11.4.3, Theorem 3, tests (49) with `α(x)β(t)` and lets `r → ∞`
and `δ → 0`, which gives the global contraction (50) between two positive times for solutions
in `C([0, ∞), L¹(ℝ))`; step 5 combines (50) with the initial convergence in `L¹`. We test with
a cutoff on intervals that shrink at the speed `c` and compare with the initial data directly,
so only bounded solutions with local initial traces are needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, steps 4-5, equations (49)-(50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

namespace Kruzhkov

/-- An essentially bounded measurable state is locally integrable up to time zero. -/
theorem locallyIntegrable_of_ae_bound {u : ℝ^2 → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict forwardHalfSpace))
    {M : ℝ} (hM : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M) :
    LocallyIntegrable u (volume.restrict forwardHalfSpace) := by
  have hconst : LocallyIntegrable (fun _ : ℝ^2 ↦ M)
      (volume.restrict forwardHalfSpace) := locallyIntegrable_const M
  apply hconst.mono hu
  filter_upwards [hM] with p hp using hp.trans (le_abs_self M)

/-- The entropy distance is locally integrable up to the initial boundary. -/
theorem locallyIntegrable_entropyDistance {u v : ℝ^2 → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hv : LocallyIntegrable v (volume.restrict forwardHalfSpace)) :
    LocallyIntegrable (fun p ↦ |u p - v p|) (volume.restrict forwardHalfSpace) := by
  refine locallyIntegrable_iff.mpr fun K hK ↦ ?_
  exact ((hu.integrableOn_isCompact hK).sub (hv.integrableOn_isCompact hK)).norm

/-- A bound on the characteristic speed controls the entropy flux almost everywhere. -/
theorem ae_entropyFlux_bound {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {u v : ℝ^2 → ℝ} {M c : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M)
    (hc : ∀ r ∈ Icc (-M) M, ‖deriv flux r‖ ≤ c) :
    ∀ᵐ p ∂volume.restrict forwardHalfSpace, |kruzhkovFlux flux (v p) (u p)| ≤ c * |u p - v p| := by
  filter_upwards [hbu, hbv] with p hup hvp
  have hu : u p ∈ Icc (-M) M := by
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hup
  have hv : v p ∈ Icc (-M) M := by
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hvp
  exact norm_kruzhkovFlux_le_mul hf hc hv hu

/-- The entropy flux is locally integrable up to time zero under the speed bound. -/
theorem locallyIntegrable_entropyFlux {flux : ℝ → ℝ} (hf : Measurable flux) {u v : ℝ^2 → ℝ}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hv : LocallyIntegrable v (volume.restrict forwardHalfSpace)) {c : ℝ}
    (hc : ∀ᵐ p ∂volume.restrict forwardHalfSpace, |kruzhkovFlux flux (v p) (u p)| ≤
      c * |u p - v p|) :
    LocallyIntegrable (fun p ↦ kruzhkovFlux flux (v p) (u p))
      (volume.restrict forwardHalfSpace) := by
  have hm := ((measurable_kruzhkovFlux hf).comp_aemeasurable
    (hv.aestronglyMeasurable.prodMk hu.aestronglyMeasurable).aemeasurable).aestronglyMeasurable
  apply ((locallyIntegrable_entropyDistance hu hv).smul c).mono hm
  filter_upwards [hc] with p hp using hp.trans (le_abs_self _)

/-- The derived Kato inequality in the density-flux form used by the cone comparison. -/
theorem comparison_inequality {flux : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux forwardHalfSpace u)
    (hv : IsEntropyWeakSolution flux forwardHalfSpace v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (hφ : ∀ p, 0 ≤ φ p) :
    0 ≤ ∫ p, InteriorWeakForm.integrand (fun p ↦ |u p - v p|)
      (fun p ↦ kruzhkovFlux flux (v p) (u p)) φ p := by
  have h := hu.kato_inequality hv hf (fun _ hK _ ↦ ⟨M, ae_restrict_of_ae_restrict_of_subset hK hbu⟩)
    (fun _ hK _ ↦ ⟨M, ae_restrict_of_ae_restrict_of_subset hK hbv⟩) φ hφ
  simpa only [katoWeakIntegrand, InteriorWeakForm.integrand, smul_eq_mul, mul_comm] using h

end Kruzhkov

open Kruzhkov

/-- Finite-speed local `L¹` contraction from the initial data at almost every positive time.
The characteristic speed is bounded on the common essential range of the two solutions. -/
theorem IsEntropySolutionWithInitialTrace.local_l1_contraction_ae {flux : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    {u₀ v₀ : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux v₀ v) (hf : ContDiff ℝ 1 flux) {M c : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M)
    (hc : ∀ r ∈ Icc (-M) M, ‖deriv flux r‖ ≤ c) (a b : ℝ) :
    ∀ᵐ T : ℝ, 0 < T → (∫ x : ℝ in Icc (a + c * T) (b - c * T), |u !₂[T, x] - v !₂[T, x]|) ≤ ∫ x :
      ℝ in Icc a b, |u₀ x - v₀ x| := by
  have hui := locallyIntegrable_of_ae_bound
    hu.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbu
  have hvi := locallyIntegrable_of_ae_bound
    hv.interior.weak.u_locallyIntegrable.aestronglyMeasurable hbv
  have hflux := ae_entropyFlux_bound hf hbu hbv hc
  exact ae_local_comparison (locallyIntegrable_entropyDistance hui hvi)
    (locallyIntegrable_entropyFlux hf.continuous.measurable hui hvi hflux)
    (entropyDistance_initialTrace hu.initialTrace hv.initialTrace)
    (comparison_inequality hu.interior hv.interior hf hbu hbv) hflux a b

/-- A continuously differentiable flux supplies a finite nonnegative contraction speed
for two uniformly essentially bounded entropy solutions. -/
theorem IsEntropySolutionWithInitialTrace.exists_local_l1_contraction_ae {flux : ℝ → ℝ}
    {u v : ℝ^2 → ℝ} {u₀ v₀ : ℝ → ℝ} (hu : IsEntropySolutionWithInitialTrace flux u₀ u)
    (hv : IsEntropySolutionWithInitialTrace flux v₀ v) (hf : ContDiff ℝ 1 flux) {M : ℝ}
    (hbu : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u p‖ ≤ M)
    (hbv : ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ a b : ℝ, ∀ᵐ T : ℝ, 0 < T → (∫ x : ℝ in Icc (a + c * T) (b - c * T), |u !₂[T, x] - v !₂[T,
        x]|) ≤ ∫ x : ℝ in Icc a b, |u₀ x - v₀ x| := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv flux) (s := Icc (-M) M) hf.continuous_deriv_one.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  exact hu.local_l1_contraction_ae hv hf hbu hbv (fun r hr ↦ (hC r hr).trans (le_max_left _ _))

end PDE.Hyperbolic.ConservationLaw.Scalar
