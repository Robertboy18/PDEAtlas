/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Support
import CAS.ExactTactic

/-!
# Linear approximation between the inner fronts

Cost comparisons with one primitive minimizer localize the footpoints at the
inner endpoints. The shared monotone-footpoint theorem extends this localization
throughout the interval, giving the approximation by the linear N-wave profile.

This is step 5 of the proof of Evans, §3.4.5(b), Theorem 6, at time `t = s²`. The cost
comparisons with a minimizer `z` of the primitive give the footpoint bounds (76)-(77) at the
inner fronts, as in step 4, and since `x ↦ y(x, t)` is nondecreasing (§3.4.2, Theorem 1(ii)),
the footpoints between them lie in `[-R, R]`. The bound (69) then gives (78), the approximation
of `u` by the linear part `(1/d)(x/t - σ)` of the N-wave (63).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, Theorem 1(ii); §3.4.5(b), equation (63),
  Theorem 6 and steps 4-5 of its proof, equations (69) and (76)-(78).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- Strict cost comparisons at the inner fronts bound their selected footpoints
inside the datum's support interval. Monotonicity then localizes every interior footpoint,
and the state error gives the linear N-wave approximation there. -/
theorem abs_sub_linear_le_of_inner_cost_comparison
    {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0)
    (hg : MemLp g ∞ volume) (hg1 : Integrable g volume) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0)
    {s D A z : ℝ} (hs0 : 0 < s)
    (hzmin : (∫ y in Iio z, g y) = -negativeLobeMass g / 2)
    (hleftCost : s ^ 2 * HopfLax1D.legendreTransform F
      ((deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s + D - z) / s ^ 2)
        < negativeLobeMass g / 2)
    (hrightCost : s ^ 2 * HopfLax1D.legendreTransform F
      ((deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s - D - z) / s ^ 2)
        < positiveLobeMass g / 2)
    (hstate : ∀ x : ℝ,
      let y := minimizingFootpoint (HopfLax1D.legendreTransform F)
        (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2) x
      |solution F g !₂[s ^ 2, x] -
        (((x - y) / s ^ 2) - deriv F 0) / deriv (deriv F) 0| ≤ A / s ^ 2) :
    ∀ x : ℝ,
      deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s + D ≤ x →
      x ≤ deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s - D →
      |solution F g !₂[s ^ 2, x] -
        (x - deriv F 0 * s ^ 2) / (deriv (deriv F) 0 * s ^ 2)| ≤
          (A + R / deriv (deriv F) 0) / s ^ 2 := by
  let d := deriv (deriv F) 0
  let σ := deriv F 0
  let P := √(negativeLobeMass g * d)
  let Q := √(positiveLobeMass g * d)
  let L := HopfLax1D.legendreTransform F
  let H : ℝ → ℝ := fun x ↦ ∫ y in Iio x, g y
  let y : ℝ → ℝ := minimizingFootpoint L (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2)
  let xL := σ * s ^ 2 - P * s + D
  let xR := σ * s ^ 2 + Q * s - D
  change H z = -negativeLobeMass g / 2 at hzmin
  have hd : 0 < d := hθ.trans_le (hlower 0)
  have hmass := positiveLobeMass_sub_negativeLobeMass hg1 (by linarith) hsupport
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hLnonneg (v : ℝ) : 0 ≤ L v := HopfLax1D.legendreTransform_nonneg hFin hzero v
  have hmin (x w : ℝ) : H (y x) + s ^ 2 * L ((x - y x) / s ^ 2) ≤
      H w + s ^ 2 * L ((x - w) / s ^ 2) :=
    isMinOn_integral_Iio_add_cost_footpoint hF hθ hlower hg hg1
      (sq_pos_of_pos hs0) x (mem_univ w)
  have hyL : -R ≤ y xL := by
    by_contra hnot
    have hy : y xL ≤ -R := le_of_lt (lt_of_not_ge hnot)
    have hc := hmin xL z
    rw [show H (y xL) = 0 from integral_Iio_eq_zero_of_ae_support_Icc hsupport hy,
      hzmin] at hc
    have hn := mul_nonneg (sq_nonneg s) (hLnonneg ((xL - y xL) / s ^ 2))
    change s ^ 2 * L ((xL - z) / s ^ 2) < negativeLobeMass g / 2 at hleftCost
    linarith
  have hyR : y xR ≤ R := by
    by_contra hnot
    have hy : R ≤ y xR := le_of_lt (lt_of_not_ge hnot)
    have hc := hmin xR z
    rw [show H (y xR) = ∫ y, g y from
      integral_Iio_eq_integral_of_ae_support_Icc hg1 hsupport hy, hzmin] at hc
    have hn := mul_nonneg (sq_nonneg s) (hLnonneg ((xR - y xR) / s ^ 2))
    change s ^ 2 * L ((xR - z) / s ^ 2) < positiveLobeMass g / 2 at hrightCost
    linarith
  have hmono : Monotone y := monotone_minimizingFootpoint
    (HopfLax1D.continuous_legendreTransform hFin) (superlinear_scalar_legendre hFin)
    (strictConvexOn_legendreTransform_of_deriv2_lower_bound hF hθ hlower)
    (lipschitzWith_intervalIntegral_of_memLp_top hg 0) (sq_pos_of_pos hs0)
  intro x hxL hxR
  have hyabs : |y x| ≤ R := abs_le.mpr
    ⟨hyL.trans (hmono hxL), (hmono hxR).trans hyR⟩
  have heq : solution F g !₂[s ^ 2, x] - (x - σ * s ^ 2) / (d * s ^ 2) =
      (solution F g !₂[s ^ 2, x] - (((x - y x) / s ^ 2) - σ) / d) -
        y x / (d * s ^ 2) := by cas
  change |solution F g !₂[s ^ 2, x] - (x - σ * s ^ 2) / (d * s ^ 2)| ≤ _
  rw [heq]
  calc
    |(solution F g !₂[s ^ 2, x] - (((x - y x) / s ^ 2) - σ) / d) -
        y x / (d * s ^ 2)| ≤
        |solution F g !₂[s ^ 2, x] - (((x - y x) / s ^ 2) - σ) / d| +
          |y x / (d * s ^ 2)| := abs_sub _ _
    _ ≤ A / s ^ 2 + R / (d * s ^ 2) := by
      apply add_le_add (hstate x)
      rw [abs_div, abs_of_pos (by positivity : 0 < d * s ^ 2)]
      exact div_le_div_of_nonneg_right hyabs (by positivity)
    _ = (A + R / d) / s ^ 2 := by cas

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
