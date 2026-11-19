/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.NonlinearRecurrence
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Cutoffs
import PDE.Elliptic.Regularity.Coefficients.Restriction
import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGeometry

/-!
# The De Giorgi tail-energy estimate on interior balls

For a homogeneous weak solution `u` and levels `k < h`, `exists_superlevel_ball_energy_le` bounds
`∫_{B_r} (u - h)₊²` by `C (R - r)⁻² (h - k)^(-2(1 - 2/q))` times the power `2 - 2/q > 1` of
`∫_{B_R} (u - k)₊²`. The nonlinear energy estimate is applied to the restriction of the weak
solution. Smooth cutoffs are constructed between the two balls; their derivative bounds account for
the inverse square of the radius gap. The constant is uniform in the centre, radii, levels,
coefficients and solution.

This is the ball energy estimate of the De Giorgi iteration for scalar uniformly elliptic equations
in divergence form with measurable coefficients. Evans states the De Giorgi-Nash theorem in §8.3.2
without proof and refers to Gilbarg-Trudinger, Chapter 8.

## Implementation notes

Boundary atlases needed by the truncation API are constructed from the regular defining function of
a ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.3.2, the De Giorgi-Nash theorem for the linear equation
  (17), stated without proof, p. 487.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity).
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped NNReal Sobolev ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The superlinear tail-energy estimate on concentric interior balls for a
homogeneous weak solution. The coefficient matrix is merely measurable
and essentially bounded. The constant depends on a fixed bounded ambient set,
the dimension, the exponent, and the ellipticity bounds. -/
theorem exists_superlevel_ball_energy_le
    {W : Set ℝ^n} (hWb : Bornology.IsBounded W)
    {q : ℝ≥0∞}
    (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (z : ℝ^n) (r R k h : ℝ), 0 < r → r < R → ball z R ⊆ W → k < h →
        (∫ x in ball z r, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2) ≤
          C / (R - r) ^ 2 / (h - k) ^ (2 * (1 - 2 / q.toReal)) *
            (∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2) ^
              (2 - 2 / q.toReal) := by
  obtain ⟨C, hC, henergy⟩ := exists_uniform_superlevel_nonlinear_energy_le
    hWb hq2 hq hα hΛ
  obtain ⟨D, hD, hcut⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_ball_cutoffs_with_derivative_bound (n := n)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro a haΛ ha u hu z r R k h hr hrR hball hkh
  let := Classical.choice (Boundary.nonempty_c1ExtensionAtlas_ball z (hr.trans hrR))
  let V : H¹(ball z R) := restrictCLM isOpen_ball.measurableSet hball u
  let b (i j : Fin n) : DerivLp n ∞ (ball z R) := restrictDerivLp hball (a i j)
  have hbΛ (i j : Fin n) : ‖b i j‖ ≤ Λ :=
    (norm_restrictDerivLp_le hball (a i j)).trans (haΛ i j)
  have hV : IsInteriorWeakDivergenceSolution b 0 V := by
    have hz : restrictDerivLp (p := 2) hball 0 = 0 := by
      apply Lp.ext
      exact (restrictDerivLp_apply_ae hball 0).trans
        (((Lp.coeFn_zero ℝ 2 (domainMeasure n W)).filter_mono
          (ae_mono (domainMeasure_le hball))).trans
          (Lp.coeFn_zero ℝ 2 (domainMeasure n (ball z R))).symm)
    simpa only [hz] using hu.restrict isOpen_ball hball
  obtain ⟨η, hη, hone, _, hηD⟩ := hcut z r R hr hrR
  have ht := henergy (ball z R) hball b hbΛ (ha.restrict hball) V hV
    k h hkh η hη (D / (R - r)) (div_nonneg hD.le (sub_pos.mpr hrR).le)
    (norm_partialTestFunctionLpTop_le_of_fderiv_bound η (div_nonneg hD.le (sub_pos.mpr hrR).le) hηD)
    (ball z r) measurableSet_ball (fun x hx ↦ hone x (ball_subset_closedBall hx))
  have hrep : (wkpBaseCoordinateCLM V : ℝ^n → ℝ)
      =ᵐ[volume.restrict (ball z R)] wkpBaseCoordinateCLM u :=
    restrictCLM_apply_ae isOpen_ball.measurableSet hball u (baseIndex n 1)
  have hbig :
      (∫ x, max (wkpBaseCoordinateCLM V x - k) 0 ^ 2 ∂domainMeasure n (ball z R)) =
        ∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 :=
    integral_congr_ae (hrep.fun_comp (fun t : ℝ ↦ max (t - k) 0 ^ 2))
  have hsmall :
      (∫ x in ball z r, max (wkpBaseCoordinateCLM V x - h) 0 ^ 2
        ∂domainMeasure n (ball z R)) =
        ∫ x in ball z r, max (wkpBaseCoordinateCLM u x - h) 0 ^ 2 := by
    change (∫ x in ball z r, max (wkpBaseCoordinateCLM V x - h) 0 ^ 2
      ∂volume.restrict (ball z R)) = _
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball hrR.le)]
    exact integral_congr_ae ((hrep.filter_mono (ae_mono
      (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))).fun_comp
        (fun t : ℝ ↦ max (t - h) 0 ^ 2))
  rw [hbig, hsmall] at ht
  rw [div_pow] at ht
  convert ht using 1
  ring

end SobolevSpace.GraphSpace
