/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
public import PDE.Hyperbolic.ConservationLaw.Scalar.Weak
public import PDE.Representations.Similarity.Pointwise

/-!
# Burgers rarefaction as a self-similar solution

The smooth interior `u(t, x) = x / t` of the Burgers rarefaction fan (Evans, §3.4.1(b),
Example 2, and §3.4.4, Theorem 4(ii)) is `BurgersEquation.Riemann.ratio`. Its quasilinear and
conservative Burgers residuals vanish away from `t = 0` by `pde_ratio` and `conservation_ratio` in
`PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles`. We read that profile
through the scaling ansatz (28) of Evans, §4.2.2: on positive time it is the forward
self-similar field with amplitude exponent `0` and spatial exponent `1`, and the residual
identities restrict to positive time.

The full piecewise entropy solution across the fan boundaries is constructed in
`PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Rarefaction`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1(b), Example 2; §3.4.4, Theorem 4(ii), equation (56);
  §4.2.2, equation (28).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace BurgersEquation.Similarity

open BurgersEquation.Riemann
open PDE.Representations.Similarity

noncomputable section

/-- The scalar similarity profile `F(ξ) = ξ`. -/
def identityProfile (ξ : ℝ^1) : ℝ :=
  ξ 0

/-- On positive time, the smooth rarefaction interior `x / t` is the forward self-similar
field with amplitude exponent `0` and spatial exponent `1`. -/
theorem rarefaction_interior_eq_forward_self_similar_on_positive_time :
    Set.EqOn ratio (fun p : ℝ^2 ↦ forwardSelfSimilarAnsatz identityProfile 0 1 0
      (PDE.Common.spatialPart p) (p 0)) PDE.Common.positiveTimeDomain := by
  intro p hp
  -- In one spatial dimension the similarity coordinate is exactly `t⁻¹ x`.
  have hsimilarityCoordinate : centeredDilation (p 0)⁻¹ 0 (PDE.Common.spatialPart p) (0 : Fin 1) =
        (p 0)⁻¹ * p 1 := by
    simp [centeredDilation, PDE.Common.spatialPart_apply]
  simp [forwardSelfSimilarAnsatz, scaledProfileAnsatz, identityProfile, ratio,
    hsimilarityCoordinate, mul_comm]

/-- In Euclidean derivative notation, `u_t + u u_x = 0` for the rarefaction interior on
positive time. -/
theorem rarefaction_interior_partial_deriv_residual_eq_zero_on_positive_time
    (p : ℝ^2) (hp : p ∈ PDE.Common.positiveTimeDomain) :
    (∂[(0 : Fin 2)] ratio) p + ratio p * (∂[(1 : Fin 2)] ratio) p = 0 :=
  pde_ratio p (ne_of_gt hp)

/-- The Burgers flux residual integrates to zero on every subdomain of positive spacetime. -/
theorem rarefaction_interior_flux_residual_integral_eq_zero
    (Ω : Set (ℝ^2)) (hΩ : Ω ⊆ PDE.Common.positiveTimeDomain) :
    (∫ p in Ω, PDE.Hyperbolic.ConservationLaw.Scalar.fluxResidual (fun r : ℝ ↦ r ^ 2 / 2) ratio p) =
      0 := by
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards with p hp
  have h := conservation_ratio p (ne_of_gt (hΩ hp))
  simpa [PDE.Hyperbolic.ConservationLaw.Scalar.fluxResidual, flux] using h

end

end BurgersEquation.Similarity
