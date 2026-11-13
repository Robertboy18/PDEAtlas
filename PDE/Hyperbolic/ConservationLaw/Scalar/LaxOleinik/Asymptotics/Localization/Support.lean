/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Decay
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.NWave
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Footpoint.Order
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.FinitePropagation
import CAS.ExactTactic

/-!
# Localization of the scalar variational solution

The selected footpoint minimizes the cost with the primitive from
negative infinity. Comparing with the zero-state characteristic shows that
the solution vanishes whenever these two footpoints have the same primitive
value. Constant tails and the finite propagation estimate then give
bounded support at every positive time, including small times.

In the notation of Evans, §3.4.2, `deriv_solution_eq_footpoint_slope` is the formula (29),
`u = G((x - y(x, t))/t)` with `G = (F')^{-1}`. `solution_eq_zero_of_integral_Iio_footpoint_eq`
is the argument that ends step 3 of the proof of §3.4.5(b), Theorem 6: if the footpoint and the
drift point `x - σt` give the same value of the primitive, then `y(x, t) = x - σt` and
`u(x, t) = G(σ) = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 1, equation (29); §3.4.5(b), Theorem 6
  and step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The characteristic speed of the selected-footpoint solution is
exactly its minimizing slope. -/
theorem deriv_solution_eq_footpoint_slope {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv F (solution F g !₂[t, x]) = (x - minimizingFootpoint (HopfLax1D.legendreTransform F)
      (fun y ↦ ∫ s in (0 : ℝ)..y, g s) t x) / t := by
  let e := orderIsoOfDerivLowerBound hF.differentiable_deriv_two hθ hlower
  rw [solution_eq_inverse_footpoint_of_deriv2_lower_bound hF hθ hlower ht]
  exact e.apply_symm_apply _

/-- The selected footpoint minimizes the cost with the
half-line primitive. The change of primitive base point is proved by
integrability, rather than supplied as a minimization hypothesis. -/
theorem isMinOn_integral_Iio_add_cost_footpoint {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    IsMinOn (fun y ↦ (∫ s in Iio y, g s) + t * HopfLax1D.legendreTransform F ((x - y) / t)) univ
      (minimizingFootpoint (HopfLax1D.legendreTransform F)
        (fun y ↦ ∫ s in (0 : ℝ)..y, g s) t x) := by
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hL := superlinear_scalar_legendre hFin
  have hh := lipschitzWith_intervalIntegral_of_memLp_top hg 0
  have hy := minimizingFootpoint_spec (HopfLax1D.continuous_legendreTransform hFin) hL hh ht x
  intro z _
  change (_ : ℝ) + _ ≤ _ + _
  have hz := value_le_fixed_footpoint hL hh ht x z
  rw [hy] at hz
  conv_lhs => rw [integral_Iio_eq_intervalIntegral_add hg1 0]
  conv_rhs => rw [integral_Iio_eq_intervalIntegral_add hg1 0]
  linarith

/-- Equal primitive values at the selected footpoint and the zero-state
characteristic force the solution to vanish. This uses the coercivity
of the original flux and works at shocks as well as differentiability points. -/
theorem solution_eq_zero_of_integral_Iio_footpoint_eq {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {t x : ℝ} (ht : 0 < t)
    (heq : (∫ s in Iio (minimizingFootpoint (HopfLax1D.legendreTransform F)
      (fun y ↦ ∫ s in (0 : ℝ)..y, g s) t x), g s) = ∫ s in Iio (x - t * deriv F 0), g s) :
    solution F g !₂[t, x] = 0 := by
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hf := hF.differentiable (by norm_num)
  have hconv : ConvexOn ℝ univ F := convexOn_univ_of_deriv2_nonneg hf hF.differentiable_deriv_two
      (fun r ↦ hθ.le.trans (hlower r))
  have hσ : HopfLax1D.legendreTransform F (deriv F 0) = 0 := by
    rw [HopfLax1D.legendreTransform_eq_of_convex_differentiable hFin hconv (hf 0)]
    simp only [zero_mul, hzero, sub_self]
  have hmin := isMinOn_integral_Iio_add_cost_footpoint hF hθ hlower hg hg1 ht x
    (mem_univ (x - t * deriv F 0))
  have hvel : (x - (x - t * deriv F 0)) / t = deriv F 0 := by cas
  change (_ : ℝ) + _ ≤ _ + _ at hmin
  rw [heq, hvel, hσ, mul_zero, add_zero,
    ← deriv_solution_eq_footpoint_slope hF hθ hlower ht x] at hmin
  have hcost : HopfLax1D.legendreTransform F (deriv F (solution F g !₂[t, x])) ≤ 0 := by
    nlinarith only [hmin, ht]
  have hquad := HopfLax1D.quadratic_le_legendreTransform_deriv hF hθ hlower (solution F g !₂[t, x])
  rw [hzero, add_zero] at hquad
  have hsq : (solution F g !₂[t, x]) ^ 2 = 0 := by
    nlinarith only [hquad, hcost, hθ, sq_nonneg (solution F g !₂[t, x])]
  exact sq_eq_zero_iff.mp hsq

/-- Compact support of the datum gives a finite propagation cone for
the solution, at every positive time and every spatial point. -/
theorem exists_solution_eq_zero_of_abs_gt {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume)
    (hg1 : Integrable g volume) {R : ℝ} (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ, R + c * t < |x| → solution F g !₂[t, x] = 0 := by
  let L := HopfLax1D.legendreTransform F
  let h : ℝ → ℝ := fun y ↦ ∫ s in (0 : ℝ)..y, g s
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hL := superlinear_scalar_legendre hFin
  obtain ⟨K, hh⟩ := exists_lipschitzWith_intervalIntegral_of_memLp_top hg 0
  let c₀ := max (F (K + 1)) (F (-(K + 1))) + L 0
  refine ⟨|c₀| + |deriv F 0|, add_nonneg (abs_nonneg _) (abs_nonneg _), fun t ht x hx ↦ ?_⟩
  let y := minimizingFootpoint L h t x
  have hy : value L h t x = h y + t * L ((x - y) / t) :=
    minimizingFootpoint_spec (HopfLax1D.continuous_legendreTransform hFin) hL hh ht x
  have hmin : IsMinOn (HopfLax1D.hopfLaxIntegrand F h t x) univ y := by
    intro z _
    have hz := value_le_fixed_footpoint hL hh ht x z
    rwa [hy] at hz
  have hdist := HopfLax1D.dist_le_propagationRadius_of_isMinOn_hopfLaxIntegrand hFin hh ht hmin
  have hradius : HopfLax1D.propagationRadius F K t ≤ |c₀| * t := by
    change max 0 (t * c₀) ≤ |c₀| * t
    apply max_le (mul_nonneg (abs_nonneg _) ht.le)
    nlinarith [le_abs_self c₀]
  have hxy : |x - y| ≤ |c₀| * t := by
    simpa only [Real.dist_eq] using hdist.trans hradius
  apply solution_eq_zero_of_integral_Iio_footpoint_eq hF hθ hlower hzero hg hg1 ht
  change (∫ s in Iio y, g s) = ∫ s in Iio (x - t * deriv F 0), g s
  have hdiff := abs_le.mp hxy
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at hx
    have hyR : R ≤ y := by nlinarith [abs_nonneg (deriv F 0)]
    have hξR : R ≤ x - t * deriv F 0 := by
      nlinarith [le_abs_self (deriv F 0), abs_nonneg c₀]
    rw [integral_Iio_eq_integral_of_ae_support_Icc hg1 hsupport hyR,
      integral_Iio_eq_integral_of_ae_support_Icc hg1 hsupport hξR]
  · rw [abs_of_neg (lt_of_not_ge hx0)] at hx
    have hyR : y ≤ -R := by nlinarith [abs_nonneg (deriv F 0)]
    have hξR : x - t * deriv F 0 ≤ -R := by
      nlinarith [neg_abs_le (deriv F 0), abs_nonneg c₀]
    rw [integral_Iio_eq_zero_of_ae_support_Icc hsupport hyR,
      integral_Iio_eq_zero_of_ae_support_Icc hsupport hξR]

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
