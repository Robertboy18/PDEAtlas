/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Definitions
public import PDE.FDeriv.Euclidean.Distance
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability

/-!
# First derivative of the half-space Poisson integral

On an interior neighborhood the height separates every point from the
boundary hyperplane. This gives integrable bounds for differentiating the
inverse-distance boundary potential once.
-/

@[expose] public section

namespace GreenFunction

open PDE.Analysis MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

namespace PoissonHalfSpace

theorem halfHeightBall_subset_upper
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ SobolevSpace.HalfSpace.upper n) :
    Metric.ball x₀ (x₀ PDE.Common.lastIndex / 2) ⊆
      SobolevSpace.HalfSpace.upper n := by
  intro x hxball
  have hx₀pos : 0 < x₀ PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx₀
  have hcoord : |x PDE.Common.lastIndex - x₀ PDE.Common.lastIndex| ≤ dist x x₀ := by
    simpa [Real.dist_eq] using PiLp.dist_apply_le x x₀ (PDE.Common.lastIndex (n := n))
  have hxlast : 0 < x PDE.Common.lastIndex := by
    linarith [(abs_le.mp hcoord).1, Metric.mem_ball.1 hxball]
  simpa [SobolevSpace.HalfSpace.upper] using hxlast

theorem inv_distance_pow_le_of_mem_halfHeightBall
    {x₀ x : ℝ^n} (hx₀ : x₀ ∈ SobolevSpace.HalfSpace.upper n)
    (hx : x ∈ Metric.ball x₀ (x₀ PDE.Common.lastIndex / 2))
    (y : ℝ^(n - 1)) (m : ℕ) :
    (dist x (halfSpaceEmb (n := n) y) ^ m)⁻¹ ≤
      (2 : ℝ) ^ m *
        (dist x₀ (halfSpaceEmb (n := n) y) ^ m)⁻¹ := by
  have hx₀pos : 0 < x₀ PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx₀
  have hx₀lower := lastCoord_le_distance_halfSpaceEmb (n := n) x₀ hx₀ y
  have hdist_ge : dist x₀ (halfSpaceEmb (n := n) y) / 2 ≤ dist x (halfSpaceEmb (n := n) y) := by
    linarith [dist_triangle_left x₀ (halfSpaceEmb (n := n) y) x, Metric.mem_ball.1 hx]
  have hposHalf : 0 < dist x₀ (halfSpaceEmb (n := n) y) / 2 := by linarith
  calc (dist x (halfSpaceEmb (n := n) y) ^ m)⁻¹
      ≤ ((dist x₀ (halfSpaceEmb (n := n) y) / 2) ^ m)⁻¹ := by
        gcongr
    _ = (2 : ℝ) ^ m * (dist x₀ (halfSpaceEmb (n := n) y) ^ m)⁻¹ := by
      rw [div_pow, inv_div]
      simp [div_eq_mul_inv]

/-- Inverse-distance decay gives a common integrable bound near an interior point
for a kernel weighted by bounded boundary data. The same bound controls every
point in the ball of half the interior height. -/
theorem exists_integrable_bound_boundary_smul_of_norm_le_inv_distance_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ^n → ℝ}
    (hg_bounded : ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ SobolevSpace.HalfSpace.upper n)
    (K : ℝ^n → ℝ^(n - 1) → E) {m : ℕ} (hm : n ≤ m)
    {C : ℝ} (hC : 0 ≤ C)
    (hK : ∀ x ∈ SobolevSpace.HalfSpace.upper n, ∀ y,
      ‖K x y‖ ≤ C * (dist x (halfSpaceEmb (n := n) y) ^ m)⁻¹) :
    ∃ bound : ℝ^(n - 1) → ℝ,
      Integrable bound (volume : Measure ℝ^(n - 1)) ∧
      ∀ y x, x ∈ Metric.ball x₀ (x₀ PDE.Common.lastIndex / 2) →
        ‖g (halfSpaceEmb (n := n) y) • K x y‖ ≤ bound y := by
  obtain ⟨M, hM⟩ := hg_bounded
  have hMnonneg : 0 ≤ M :=
    (abs_nonneg _).trans (hM _ (halfSpaceEmb_mem_boundary (n := n) (0 : ℝ^(n - 1))))
  refine ⟨fun y ↦ (M * C * (2 : ℝ) ^ m) * (dist x₀ (halfSpaceEmb (n := n) y) ^ m)⁻¹,
    (integrable_inv_distance_pow_of_le x₀ hx₀ hm).const_mul _, fun y x hx ↦ ?_⟩
  calc ‖g (halfSpaceEmb (n := n) y) • K x y‖
      ≤ M * (C * ((2 : ℝ) ^ m * (dist x₀ (halfSpaceEmb (n := n) y) ^ m)⁻¹)) := by
        rw [norm_smul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hM _ (halfSpaceEmb_mem_boundary y))
          ((hK x (halfHeightBall_subset_upper hx₀ hx) y).trans (mul_le_mul_of_nonneg_left
            (inv_distance_pow_le_of_mem_halfHeightBall hx₀ hx y m) hC)) (norm_nonneg _) hMnonneg
    _ = _ := by ring

theorem integrable_boundary_smul_invDistPowFDeriv
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ SobolevSpace.HalfSpace.upper n)
    (k : ℕ) (hk : n ≤ k + 1) :
    Integrable
      (fun y : ℝ^(n - 1) ↦
        (g (halfSpaceEmb (n := n) y)) •
          EuclideanDistance.invDistPowFDerivFormula k x
            (halfSpaceEmb (n := n) y))
      (volume : Measure ℝ^(n - 1)) := by
  obtain ⟨M, hM⟩ := hg_bounded
  have hMnonneg : 0 ≤ M := (abs_nonneg _).trans (hM _ (halfSpaceEmb_mem_boundary (n := n) 0))
  refine ((integrable_inv_distance_pow_of_le (n := n) x hx hk).const_mul (M * k)).mono'
    ((hg.comp (measurable_halfSpaceEmb (n := n))).aestronglyMeasurable.smul
      (EuclideanDistance.continuous_invDistPowFDerivFormula k continuous_const
        (continuous_halfSpaceEmb (n := n))
        (halfSpace_ne_halfSpaceEmb (n := n) hx)).aestronglyMeasurable) (.of_forall fun y ↦ ?_)
  rw [norm_smul, mul_assoc]
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using hM _ (halfSpaceEmb_mem_boundary (n := n) y))
    (EuclideanDistance.norm_invDistPowFDerivFormula_le k (halfSpace_ne_halfSpaceEmb (n := n) hx y))
    (norm_nonneg _) hMnonneg

end PoissonHalfSpace

open PoissonHalfSpace

/-- Differentiate the inverse-distance boundary integral under the integral sign. -/
theorem hasFDerivAt_halfSpaceIntegral_div_distance_pow {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded : ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ SobolevSpace.HalfSpace.upper n) :
    HasFDerivAt
      (fun x : ℝ^n ↦
        ∫ y : ℝ^(n - 1),
          g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n
            ∂(volume : Measure ℝ^(n - 1)))
      (∫ y : ℝ^(n - 1),
        (g (halfSpaceEmb (n := n) y)) •
          EuclideanDistance.invDistPowFDerivFormula n x₀ (halfSpaceEmb (n := n) y)
          ∂(volume : Measure ℝ^(n - 1)))
      x₀ := by
  obtain ⟨bound, bound_integrable, h_bound⟩ :=
    exists_integrable_bound_boundary_smul_of_norm_le_inv_distance_pow hg_bounded hx₀
      (fun x y ↦ EuclideanDistance.invDistPowFDerivFormula n x (halfSpaceEmb (n := n) y))
      (m := n + 1) (by omega) (C := (n : ℝ)) (by positivity)
      (fun x hx y ↦ EuclideanDistance.norm_invDistPowFDerivFormula_le n
        (halfSpace_ne_halfSpaceEmb hx y))
  have hx₀pos : 0 < x₀ PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y ↦ g (halfSpaceEmb (n := n) y) / dist x (halfSpaceEmb (n := n) y) ^ n)
    (Metric.ball_mem_nhds x₀ (half_pos hx₀pos))
    (.of_forall fun x ↦ ((hg.comp (measurable_halfSpaceEmb (n := n))).div
      ((continuous_const.dist (continuous_halfSpaceEmb (n := n))).measurable.pow_const
        n)).aestronglyMeasurable)
    (integrable_halfSpace_integrand_of_bounded hg hg_bounded x₀ hx₀)
    (integrable_boundary_smul_invDistPowFDeriv hg hg_bounded hx₀ n (by omega)).aestronglyMeasurable
    (ae_of_all _ h_bound) bound_integrable
    (ae_of_all _ fun y x hx ↦ EuclideanDistance.hasFDerivAt_const_div_dist_pow
      (halfSpace_ne_halfSpaceEmb (halfHeightBall_subset_upper hx₀ hx) y) _)

end GreenFunction
