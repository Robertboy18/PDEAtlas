/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Inverse.Monotone
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Representation

/-!
# Lax–Oleinik existence for uniformly convex C² fluxes

We prove the integral-solution existence statement of Evans, §3.4.2,
Theorem 2, for C² fluxes with a positive lower bound on the second derivative.

The lower bound on the second derivative gives a global inverse of the flux
derivative, by the monotone-inverse theorem. The Legendre conjugate is then
finite and differentiable. Its attained Hopf–Lax footpoint yields a weak
initial solution for arbitrary `L∞`
data, with the initial term and the sharp essential bound.

Linear and constant flux terms are allowed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 2, equations (28)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

private theorem convexOn_of_deriv2_lower_bound {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) : ConvexOn ℝ univ F :=
  convexOn_univ_of_deriv2_nonneg (hF.differentiable (by norm_num))
    hF.differentiable_deriv_two fun r ↦ hθ.le.trans (hlower r)

/-- The conjugate is finite under the uniformly convex C²
assumptions. Surjectivity of the flux derivative is derived. -/
theorem legendreFinite_of_deriv2_lower_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) :
    HopfLax1D.LegendreFinite F :=
  HopfLax1D.legendreFinite_of_surjective_deriv
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
    (surjective_of_deriv_lower_bound hF.differentiable_deriv_two hθ hlower)

/-- The conjugate is strictly convex because its derivative is the
strictly increasing inverse of the flux derivative. -/
theorem strictConvexOn_legendreTransform_of_deriv2_lower_bound {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) :
    StrictConvexOn ℝ univ (HopfLax1D.legendreTransform F) := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  have hd (v : ℝ) : deriv (HopfLax1D.legendreTransform F) v = e.symm v :=
    (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
      e.apply_symm_apply (e.symm.continuous.continuousAt (x := v))).deriv
  apply StrictMono.strictConvexOn_univ_of_deriv
    (HopfLax1D.continuous_legendreTransform (legendreFinite_of_deriv2_lower_bound hF hθ hlower))
  intro u v huv
  rw [hd u, hd v]
  exact e.symm.strictMono huv

/-- The attained-footpoint Lax–Oleinik construction solves the full
weak initial problem and belongs to `L∞`. Only the C² uniform
convexity and `L∞` initial-data hypotheses are required. -/
theorem solution_spec_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution F g (solution F g) ∧ MemLp (solution F g) ∞ volume := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  exact solution_spec_of_continuous_rightInverse
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
    e.apply_symm_apply e.symm.continuous hg

/-- Every essential bound for the datum, including zero, is preserved under
the flux hypotheses. -/
theorem ae_norm_solution_le_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) {K : ℝ≥0}
    (hK : ∀ᵐ x : ℝ, ‖g x‖ ≤ K) :
    ∀ᵐ p : ℝ^2, ‖solution F g p‖ ≤ K := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  exact ae_norm_solution_le_of_continuous_rightInverse
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
    e.apply_symm_apply e.symm.continuous hg hK

/-- The solution has the sharp bound by the datum's essential
supremum. -/
theorem ae_norm_solution_le_eLpNorm_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    ∀ᵐ p : ℝ^2, ‖solution F g p‖ ≤ (eLpNorm g ∞ volume).toReal := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  exact ae_norm_costSolution_le_eLpNorm (superlinear_scalar_legendre hFin)
    (HopfLax1D.convexOn_legendreTransform hFin)
    (fun v ↦ (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
      e.apply_symm_apply (e.symm.continuous.continuousAt (x := v))).differentiableAt) hg

/-- At every positive point the solution is the derived inverse of `F'`
evaluated at the minimizing-footpoint slope. -/
theorem solution_eq_inverse_footpoint_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) {p : ℝ^2} (ht : 0 < p 0) :
    solution F g p = (orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower).symm
      ((p 1 - minimizingFootpoint (HopfLax1D.legendreTransform F) (fun x ↦ ∫ s in (0 : ℝ)..x, g s)
      (p 0) (p 1)) / p 0) := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  exact solution_eq_inverse_footpoint
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
    e.apply_symm_apply e.symm.continuous ht

/-- At each fixed positive time the footpoint solution is the
spatial derivative of the variational value almost everywhere. -/
theorem solution_ae_eq_deriv_value_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) {t : ℝ}
    (ht : 0 < t) :
    ∀ᵐ x : ℝ, solution F g !₂[t, x] =
      deriv (value (HopfLax1D.legendreTransform F) (fun y ↦ ∫ s in (0 : ℝ)..y, g s) t) x := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  exact costSolution_ae_eq_deriv_value (superlinear_scalar_legendre hFin)
    (fun v ↦ (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
      e.apply_symm_apply (e.symm.continuous.continuousAt (x := v))).differentiableAt) hg ht

/-- The footpoint solution is the spatial partial derivative
jointly almost everywhere at positive time. -/
theorem solution_ae_eq_partialDeriv_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    solution F g =ᵐ[volume.restrict forwardHalfSpace] (∂[1] (initialPotential F g)) := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  exact solution_ae_eq_partialDeriv_of_continuous_rightInverse
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num))
    e.apply_symm_apply e.symm.continuous hg

/-- The potential satisfies its Hamilton–Jacobi equation in
partial derivatives almost everywhere under the flux/data hypotheses. -/
theorem ae_initialPotential_hamiltonJacobi_of_deriv2_lower_bound {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume) :
    ∀ᵐ p ∂volume.restrict (forwardHalfSpace : Set ℝ^2),
      (∂[0] (initialPotential F g)) p + F ((∂[1] (initialPotential F g)) p) = 0 :=
  ae_initialPotential_hamiltonJacobi (legendreFinite_of_deriv2_lower_bound hF hθ hlower)
    (convexOn_of_deriv2_lower_bound hF hθ hlower) (hF.differentiable (by norm_num)) hg

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
