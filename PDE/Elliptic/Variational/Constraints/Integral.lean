/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegralPotential.QuadraticGrowth
public import PDE.Elliptic.Variational.PrincipalForms

/-!
# Nonlinear integral constraints on the zero-boundary Sobolev space

The constraint `u ↦ ∫ G(u)` uses the `L²` base coordinate. A continuous
derivative `g` of linear growth gives its strict Fréchet derivative, namely the
weak load with density `g(u)`. The representative and integral identities
are proved here so subsequent minimization and multiplier arguments use the
nonlinear functional.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "dΩ" => domainMeasure n Ω

/-- The integral constraint evaluated on the Sobolev representative. -/
def integralConstraint (G : ℝ → ℝ) (u : H¹₀(Ω)) : ℝ :=
  ∫ x, G (baseCoordCLM (n := n) (Ω := Ω) u x) ∂dΩ

/-- Evaluation of the constraint at zero, allowing `G(0) ≠ 0`. -/
theorem integralConstraint_zero (G : ℝ → ℝ) :
    integralConstraint (n := n) (Ω := Ω) G 0 = (domainMeasure n Ω).real univ * G 0 := by
  unfold integralConstraint
  rw [map_zero]
  calc
    _ = ∫ _ : ℝ^n, G 0 ∂dΩ := integral_congr_ae
      ((Lp.coeFn_zero ℝ 2 dΩ).mono fun x hx ↦ congrArg G hx)
    _ = _ := by simp

variable [IsFiniteMeasure (domainMeasure n Ω)] {G g : ℝ → ℝ} {C : ℝ}

/-- The constraint density is integrable under linear growth of its derivative. -/
theorem integralConstraint_integrable
    (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u : H¹₀(Ω)) :
    Integrable (fun x ↦ G (baseCoordCLM (n := n) (Ω := Ω) u x)) dΩ :=
  integrable_potential_L2_of_deriv_growth (by simpa using (abs_nonneg (g 0)).trans (hg 0)) hd hg _

/-- The nonlinear weak-equation density `g(u)v` is integrable for every
zero-boundary test function. -/
theorem integrable_integralConstraint_pairing
    (hc : Continuous g) (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u v : H¹₀(Ω)) :
    Integrable (fun x ↦ g (baseCoordCLM u x) * baseCoordCLM v x) dΩ :=
  (memLp_comp_of_linear_growth hc hg (baseCoordCLM u)).integrable_mul
    (Lp.memLp (baseCoordCLM v))

/-- The nonlinear integral constraint is continuous on `H¹₀`. -/
theorem continuous_integralConstraint
    (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) :
    Continuous (integralConstraint (n := n) (Ω := Ω) G) :=
  (continuous_integral_L2_of_deriv_growth (μ := domainMeasure n Ω)
    (by simpa using (abs_nonneg (g 0)).trans (hg 0)) hd hg).comp
    (baseCoordCLM (n := n) (Ω := Ω)).continuous

/-- Strict differentiation of the constraint gives the load
with superposition density `g(u)`. -/
theorem integralConstraint_hasStrictFDerivAt
    (hd : ∀ s, HasDerivAt G (g s) s) (hc : Continuous g)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u : H¹₀(Ω)) :
    HasStrictFDerivAt (integralConstraint G)
      (loadFunctional (Lp.superposition (fun _ : ℝ^n ↦ g)
        (memLp_comp_of_linear_growth hc hg) (baseCoordCLM u))) u :=
  (hasStrictFDerivAt_integral_L2_of_deriv_growth
    (by simpa using (abs_nonneg (g 0)).trans (hg 0)) hd hc hg
    (baseCoordCLM u)).comp u baseCoordCLM.hasStrictFDerivAt

/-- Evaluation of the derivative is the integral of `g(u)v`, with both
factors the Sobolev base coordinates. -/
theorem integralConstraint_fderiv_apply
    (hd : ∀ s, HasDerivAt G (g s) s) (hc : Continuous g)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u v : H¹₀(Ω)) :
    fderiv ℝ (integralConstraint G) u v =
      ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂dΩ := by
  rw [(integralConstraint_hasStrictFDerivAt hd hc hg u).hasFDerivAt.fderiv,
    loadFunctional_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_superposition (fun _ : ℝ^n ↦ g)
    (memLp_comp_of_linear_growth (μ := domainMeasure n Ω) hc hg) (baseCoordCLM u)] with x hx
  rw [hx]

/-- On an open domain, a vanishing constraint derivative means that its
pointwise derivative density vanishes almost everywhere. -/
theorem integralConstraint_fderiv_eq_zero_iff
    (hΩ : IsOpen Ω) (hd : ∀ s, HasDerivAt G (g s) s)
    (hc : Continuous g) (hg : ∀ s, |g s| ≤ C * (1 + |s|)) (u : H¹₀(Ω)) :
    fderiv ℝ (integralConstraint G) u = 0 ↔
      (fun x ↦ g (baseCoordCLM u x)) =ᵐ[dΩ] 0 := by
  rw [(integralConstraint_hasStrictFDerivAt hd hc hg u).hasFDerivAt.fderiv,
    loadFunctional_eq_zero_iff hΩ, Lp.eq_zero_iff_ae_eq_zero]
  exact (Lp.coeFn_superposition (fun _ : ℝ^n ↦ g)
    (memLp_comp_of_linear_growth (μ := domainMeasure n Ω) hc hg) (baseCoordCLM u)).congr_left

end SobolevSpace.GraphSpace
