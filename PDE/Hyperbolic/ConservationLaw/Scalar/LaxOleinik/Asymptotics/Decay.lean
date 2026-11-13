/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Primitive.Integrable
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.UniformlyConvex
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Legendre.Taylor
import CAS.ExactTactic

/-!
# Pointwise decay of the Lax–Oleinik solution

An integrable datum bounds the oscillation of its primitive. Compare the
constructed minimizing footpoint with the zero-state characteristic, then use
quadratic support of the original uniformly convex flux. The estimate holds
at every positive-time point of the selected-footpoint representative,
including shocks.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(a), Theorem 5 and its proof, equations (57)-(62).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The squared pointwise decay estimate for the variational solution.
Only a lower bound on the second derivative of the original flux is needed. -/
theorem mul_sq_solution_le_integral_abs {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    t * θ / 2 * |solution F g !₂[t, x]| ^ 2 ≤ ∫ y, |g y| := by
  let L := HopfLax1D.legendreTransform F
  let h : ℝ → ℝ := fun y ↦ ∫ s in (0 : ℝ)..y, g s
  let y := minimizingFootpoint L h t x
  let σ := deriv F 0
  have hf := hF.differentiable (by norm_num)
  have hconv : ConvexOn ℝ univ F := convexOn_univ_of_deriv2_nonneg hf hF.differentiable_deriv_two
      (fun r ↦ hθ.le.trans (hlower r))
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hL := superlinear_scalar_legendre hFin
  have hh := lipschitzWith_intervalIntegral_of_memLp_top hg 0
  have hy : value L h t x = h y + t * L ((x - y) / t) :=
    minimizingFootpoint_spec (HopfLax1D.continuous_legendreTransform hFin) hL hh ht x
  have hσ : L σ = 0 := by
    dsimp only [L, σ]
    rw [HopfLax1D.legendreTransform_eq_of_convex_differentiable hFin hconv (hf 0)]
    simp only [zero_mul, hzero, sub_self]
  have hvel : (x - (x - t * σ)) / t = σ := by
    cas
  have hcompare := value_le_fixed_footpoint hL hh ht x (x - t * σ)
  change value L h t x ≤ h (x - t * σ) + t * L ((x - (x - t * σ)) / t) at hcompare
  rw [hy, hvel, hσ, mul_zero, add_zero] at hcompare
  have hosc := norm_intervalIntegral_sub_le_integral_norm hg1 0 (x - t * σ) y
  simp only [Real.norm_eq_abs] at hosc
  have hcost : t * L ((x - y) / t) ≤ ∫ s, |g s| := by
    have hdiff : h (x - t * σ) - h y ≤ ∫ s, |g s| := (le_abs_self _).trans hosc
    linarith
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  have hu : deriv F (solution F g !₂[t, x]) = (x - y) / t := by
    rw [solution_eq_inverse_footpoint_of_deriv2_lower_bound hF hθ hlower ht]
    exact e.apply_symm_apply ((x - y) / t)
  have hquad := HopfLax1D.quadratic_le_legendreTransform_deriv hF hθ hlower (solution F g !₂[t, x])
  rw [hzero, add_zero, hu] at hquad
  have hmul := mul_le_mul_of_nonneg_left hquad ht.le
  rw [sq_abs]
  nlinarith only [hmul, hcost]

/-- Every positive-time value decays at rate `t⁻¹ᐟ²`, with the explicit
constant determined by the uniform convexity modulus and the datum's `L¹`
norm. The drift `F'(0)` is unrestricted. This is the estimate (57) of Evans, §3.4.5, Theorem 5. -/
theorem abs_solution_le_sqrt_div_sqrt {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |solution F g !₂[t, x]| ≤ √(2 * (∫ y, |g y|) / θ) / √t := by
  have hsq := mul_sq_solution_le_integral_abs hF hθ hlower hzero hg hg1 ht x
  apply (le_div_iff₀ (Real.sqrt_pos.2 ht)).2
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt ht.le, sq_abs]
  apply (le_div_iff₀ hθ).2
  rw [sq_abs] at hsq
  nlinarith only [hsq]

/-- A prescribed `L¹` budget gives a single explicit decay constant for all
admissible fluxes and data with the given convexity modulus. -/
theorem abs_solution_le_of_integral_abs_le {θ M : ℝ} (hθ : 0 < θ) {F g : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0)
    (hg : MemLp g ∞ volume) (hg1 : Integrable g volume) (hM : (∫ y, |g y|) ≤ M) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    |solution F g !₂[t, x]| ≤ √(2 * M / θ) / √t := by
  apply (abs_solution_le_sqrt_div_sqrt hF hθ hlower hzero hg hg1 ht x).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg t)
  exact Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hθ.le)

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
