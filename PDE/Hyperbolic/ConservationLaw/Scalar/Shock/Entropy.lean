/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Weak
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.ConvexShock

/-!
# Convex entropy admissibility for a curved shock

For varying classical fields joined across `x = s(t)`, the entropy chain rule
annihilates the bulk entropy residuals. The derived moving-interface formula
then expresses the weak entropy integral as

`∫ (s'(t) [η(u)] - [q(u)]) φ(t,s(t)) dt`.

Rankine–Hugoniot and a downward trace jump make this coefficient nonnegative
for a convex flux and convex entropy. Hence the joined field satisfies the distributional
entropy inequality, and its entropy and entropy flux are locally integrable.

Only convexity between the two traces at each time is needed. The entropy
predicates quantify over the `C¹` entropy pairs `EntropyPair`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (8)-(12) and (19); §11.4.3,
  equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common TopologicalSpace
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Shock

/-- The weak entropy jump formula across a C¹ moving graph. The bulk entropy
equations follow from the classical conservation law and the entropy chain rule. -/
theorem integral_entropyWeakIntegrand_profile {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hF : ContDiff ℝ 1 F)
    (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0) (E : EntropyPair (fun r ↦ deriv F r))
    (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p, entropyWeakIntegrand (profile s uL uR) E φ p) = ∫ t,
      (deriv s t * (E.η (uR (interface s t)) - E.η (uL (interface s t))) -
      (E.q (uR (interface s t)) - E.q (uL (interface s t)))) * φ (interface s t) := by
  have hη (p : ℝ^2) := congrFun (comp_profile E.η s uL uR) p
  have hq (p : ℝ^2) := congrFun (comp_profile E.q s uL uR) p
  simp_rw [entropyWeakIntegrand, hη, hq]
  apply integral_profile_divergence_of_bulk_eq_zero hs
    (E.eta_contDiff.comp hL) (E.eta_contDiff.comp hR)
    (E.entropyFlux_contDiff.comp hL) (E.entropyFlux_contDiff.comp hR)
  · exact fun p hp ↦ entropyResidual_eq_zero_of_flux_pde hF.differentiable_one
      (hL.differentiable_one p) (hPL p hp)
  · exact fun p hp ↦ entropyResidual_eq_zero_of_flux_pde hF.differentiable_one
      (hR.differentiable_one p) (hPR p hp)

/-- The entropy-production density paired with a compact test trace is integrable. -/
theorem integrable_entropy_jump_mul_trace {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ} (hs : ContDiff ℝ 1 s)
    (hL : Continuous uL) (hR : Continuous uR) (E : EntropyPair (fun r ↦ deriv F r))
    (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    Integrable (fun t ↦ (deriv s t * (E.η (uR (interface s t)) - E.η (uL (interface s t))) -
      (E.q (uR (interface s t)) - E.q (uL (interface s t)))) * φ (interface s t)) := by
  have hc := continuous_interface hs.continuous
  apply integrable_mul_interface_comp hs.continuous
    _ φ.continuous φ.hasCompactSupport
  exact (hs.continuous_deriv_one.mul ((E.eta_contDiff.continuous.comp (hR.comp hc)).sub
      (E.eta_contDiff.continuous.comp (hL.comp hc)))).sub
    ((E.entropyFlux_contDiff.continuous.comp (hR.comp hc)).sub
      (E.entropyFlux_contDiff.continuous.comp (hL.comp hc)))

/-- A downward curved Rankine–Hugoniot shock satisfies the distributional
inequality for an entropy convex between its traces at each time. -/
theorem satisfiesEntropyInequalityFor_profile_of_convex {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0)
    (hRH : ∀ t, RankineHugoniot F (uL (interface s t)) (uR (interface s t)) (deriv s t))
    (hdown : ∀ t, uR (interface s t) ≤ uL (interface s t))
    (hconv : ∀ t, ConvexOn ℝ (Icc (uR (interface s t)) (uL (interface s t))) F)
    (E : EntropyPair (fun r ↦ deriv F r))
    (hη : ∀ t, ConvexOn ℝ (Icc (uR (interface s t)) (uL (interface s t))) E.η) :
    SatisfiesEntropyInequalityFor (⊤ : Opens ℝ^2) (profile s uL uR) E := by
  refine ⟨ (locallyIntegrable_flux_profile E.eta_contDiff.continuous hs.continuous
      hL.continuous hR.continuous).locallyIntegrableOn univ,
    (locallyIntegrable_flux_profile E.entropyFlux_contDiff.continuous hs.continuous
      hL.continuous hR.continuous).locallyIntegrableOn univ, ?_⟩
  intro φ hφ
  rw [integral_entropyWeakIntegrand_profile hF hs hL hR hPL hPR E φ]
  refine integral_nonneg fun t ↦ ?_
  apply mul_nonneg _ (hφ _)
  exact sub_nonneg.mpr ((hRH t).entropy_jump_le_of_convex (hdown t) (hconv t)
      (fun r _ ↦ hF.differentiable_one r) E (hη t))

/-- A downward Rankine–Hugoniot shock with varying classical fields is an
entropy weak solution for every bundled smooth convex entropy. -/
theorem isEntropyWeakSolution_profile_of_convex {F s : ℝ → ℝ} {uL uR : ℝ^2 → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : ContDiff ℝ 1 s) (hL : ContDiff ℝ 1 uL) (hR : ContDiff ℝ 1 uR)
    (hPL : ∀ p, p 1 < s (p 0) → fluxResidual F uL p = 0)
    (hPR : ∀ p, s (p 0) < p 1 → fluxResidual F uR p = 0)
    (hRH : ∀ t, RankineHugoniot F (uL (interface s t)) (uR (interface s t)) (deriv s t))
    (hdown : ∀ t, uR (interface s t) ≤ uL (interface s t))
    (hconv : ∀ t, ConvexOn ℝ (Icc (uR (interface s t)) (uL (interface s t))) F) :
    IsEntropyWeakSolution F (⊤ : Opens ℝ^2) (profile s uL uR) := by
  refine ⟨isWeakSolution_profile_of_rankineHugoniot hF hs hL hR hPL hPR hRH, fun E hη ↦ ?_⟩
  exact satisfiesEntropyInequalityFor_profile_of_convex hF hs hL hR hPL hPR hRH
    hdown hconv E (fun t ↦ hη.subset (subset_univ _) (convex_Icc _ _))

end PDE.Hyperbolic.ConservationLaw.Scalar.Shock
