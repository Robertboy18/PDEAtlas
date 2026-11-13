/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.Localization.Support
import PDE.Analysis.Convex.Real.Quadratic
import CAS.ExactTactic

/-!
# Vanishing outside the displaced N-wave fronts

The primitive plateaus and its global minimum exclude minimizing footpoints
on the wrong side of the support interval. Equal plateau values then force a zero state.

This is step 3 of the proof of Evans, §3.4.5(b), Theorem 6, at time `t = s²`, given the cost
expansion (74) with error `E/s`. The primitive is constant outside `[-R, R]`, and its minimum is
given by (70). For `x` outside the fronts, comparison with the drift point `x - σt` shows that a
minimizing footpoint lies on the same plateau, which forces `y(x, t) = x - σt` and
`u(x, t) = G(σ) = 0`, as in (72)-(73). Evans's fronts are `x - σt = -R - (pd(1 + ε)t)^{1/2}` and
`x - σt = R + (qd(1 + ε)t)^{1/2}` with `ε = A/t^{1/2}` as in (71). Since
`((1 + ε)t)^{1/2} - t^{1/2} = O(1)`, as he notes in step 5, we use `x - σt = -(pdt)^{1/2} - D`
and `x - σt = (qdt)^{1/2} + D` for a constant `D ≥ R`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(b), Theorem 6 and steps 2, 3 and 5 of its
  proof, equations (70)-(75).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- A quantitative cost error excludes nonzero solution states outside the two
expanded N-wave fronts. Primitive plateaus and the attained minimum determine
the comparison costs. The cost estimate is discharged in `exists_nWave_front_localization`. -/
theorem solution_eq_zero_outside_nWave_strip_of_cost_error
    {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0)
    (hg : MemLp g ∞ volume) (hg1 : Integrable g volume) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0)
    (hp : 0 < negativeLobeMass g) (hq : 0 < positiveLobeMass g)
    {s D E : ℝ} (hs0 : 0 < s) (hDR : R ≤ D)
    (hgapP : E < √(negativeLobeMass g * deriv (deriv F) 0) * (D - R) / deriv (deriv F) 0)
    (hgapQ : E < √(positiveLobeMass g * deriv (deriv F) 0) * (D - R) / deriv (deriv F) 0)
    (hcost : ∀ x : ℝ,
      let y := minimizingFootpoint (HopfLax1D.legendreTransform F)
        (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2) x
      |s ^ 2 * HopfLax1D.legendreTransform F ((x - y) / s ^ 2) -
        (x - deriv F 0 * s ^ 2 - y) ^ 2 / (2 * deriv (deriv F) 0 * s ^ 2)| ≤ E / s) :
    ∀ x : ℝ,
      x ≤ deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s - D ∨
      deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s + D ≤ x →
      solution F g !₂[s ^ 2, x] = 0 := by
  let d := deriv (deriv F) 0
  let σ := deriv F 0
  let P := √(negativeLobeMass g * d)
  let Q := √(positiveLobeMass g * d)
  let L := HopfLax1D.legendreTransform F
  let H : ℝ → ℝ := fun x ↦ ∫ y in Iio x, g y
  have hd : 0 < d := hθ.trans_le (hlower 0)
  have hP : 0 < P := Real.sqrt_pos.mpr (mul_pos hp hd)
  have hQ : 0 < Q := Real.sqrt_pos.mpr (mul_pos hq hd)
  have hpdiv : P ^ 2 / (2 * d) = negativeLobeMass g / 2 := by
    rw [show P ^ 2 = negativeLobeMass g * d from Real.sq_sqrt (by positivity)]
    cas
  have hqdiv : Q ^ 2 / (2 * d) = positiveLobeMass g / 2 := by
    rw [show Q ^ 2 = positiveLobeMass g * d from Real.sq_sqrt (by positivity)]
    cas
  obtain ⟨z, hz, hzmin, _, hminH⟩ := exists_lobe_minimizer hg1 (by linarith) hsupport
  have hmass := positiveLobeMass_sub_negativeLobeMass hg1 (by linarith) hsupport
  have hleft (x : ℝ) (hx : x ≤ -R) : H x = 0 :=
    integral_Iio_eq_zero_of_ae_support_Icc hsupport hx
  have hright (x : ℝ) (hx : R ≤ x) : H x = ∫ y, g y :=
    integral_Iio_eq_integral_of_ae_support_Icc hg1 hsupport hx
  have hFin := legendreFinite_of_deriv2_lower_bound hF hθ hlower
  have hLσ : L σ = 0 := by
    have h := HopfLax1D.legendreTransform_eq_of_convex_differentiable hFin
      (convexOn_univ_of_deriv2_nonneg (hF.differentiable (by norm_num))
        hF.differentiable_deriv_two (fun r ↦ hθ.le.trans (hlower r)))
      (hF.differentiable (by norm_num) 0)
    simpa only [zero_mul, hzero, sub_self] using h
  let y : ℝ → ℝ := minimizingFootpoint L (fun w ↦ ∫ r in (0 : ℝ)..w, g r) (s ^ 2)
  let ξ : ℝ → ℝ := fun x ↦ x - σ * s ^ 2
  have hquad (x : ℝ) :
      |s ^ 2 * L ((x - y x) / s ^ 2) - (ξ x - y x) ^ 2 / (2 * d * s ^ 2)| ≤ E / s := hcost x
  have hzeroCmp (x : ℝ) : H (y x) + s ^ 2 * L ((x - y x) / s ^ 2) ≤ H (ξ x) := by
    have h := isMinOn_integral_Iio_add_cost_footpoint hF hθ hlower hg hg1
      (sq_pos_of_pos hs0) x (mem_univ (ξ x))
    change H (y x) + s ^ 2 * L ((x - y x) / s ^ 2) ≤ H (ξ x) + s ^ 2 * L ((x - ξ x) / s ^ 2) at h
    have heq : (x - ξ x) / s ^ 2 = σ := by dsimp [ξ]; cas
    simpa only [heq, hLσ, mul_zero, add_zero] using h
  intro x hx
  apply solution_eq_zero_of_integral_Iio_footpoint_eq hF hθ hlower hzero hg hg1
    (sq_pos_of_pos hs0)
  rw [mul_comm (s ^ 2) (deriv F 0)]
  change H (y x) = H (ξ x)
  rcases hx with hx | hx
  · have hξ : ξ x ≤ -R := by dsimp [ξ, σ] at *; nlinarith [mul_pos hP hs0]
    have hy : y x ≤ -R := by
      by_contra hnot
      have hw : P * s + (D - R) ≤ |ξ x - y x| := by
        have habs := neg_le_abs (ξ x - y x)
        dsimp [ξ, σ] at *
        linarith
      have hq := quadratic_outward_gap hd hs0 hP.le (by linarith : 0 ≤ D - R)
        (by linarith : E < P * (D - R) / d) hw
      rw [hpdiv] at hq
      have hb := (abs_le.mp (hquad x)).1
      have hH := hminH (y x)
      rw [hzmin] at hH
      have hc := hzeroCmp x
      rw [hleft _ hξ] at hc
      linarith
    rw [hleft _ hy, hleft _ hξ]
  · have hξ : R ≤ ξ x := by dsimp [ξ, σ] at *; nlinarith [mul_pos hQ hs0]
    have hy : R ≤ y x := by
      by_contra hnot
      have hw : Q * s + (D - R) ≤ |ξ x - y x| := by
        have habs := le_abs_self (ξ x - y x)
        dsimp [ξ, σ] at *
        linarith
      have hq' := quadratic_outward_gap hd hs0 hQ.le (by linarith : 0 ≤ D - R)
        (by linarith : E < Q * (D - R) / d) hw
      rw [hqdiv] at hq'
      have hb := (abs_le.mp (hquad x)).1
      have hH := hminH (y x)
      rw [hzmin] at hH
      have hc := hzeroCmp x
      rw [hright _ hξ] at hc
      linarith
    rw [hright _ hy, hright _ hξ]

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
