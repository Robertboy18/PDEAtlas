/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.FirstDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian

/-!
# Second derivatives of the half-space Poisson integral

The Hessian of the inverse-distance potential admits a common integrable
majorant on each interior height ball. Differentiation under the boundary
integral gives its repeated coordinate derivatives and Laplacian.
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open PDE.Analysis MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

namespace PoissonHalfSpace

theorem integrable_boundary_invDistPowFDeriv_apply_fderiv
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ SobolevSpace.HalfSpace.upper n)
    (v : ℝ^n) :
    Integrable
      (fun y : ℝ^(n - 1) ↦
        (g (halfSpaceEmb (n := n) y)) •
          EuclideanDistance.invDistPowSecondFDerivFormula n x
            (halfSpaceEmb (n := n) y) v)
      (volume : Measure ℝ^(n - 1)) := by
  classical
  obtain ⟨M, hM⟩ := hg_bounded
  have hp := continuous_halfSpaceEmb (n := n)
  have hne := halfSpace_ne_halfSpaceEmb (n := n) hx
  have hS : Continuous fun y : ℝ^(n - 1) ↦
      (-(n : ℝ)) / dist x (halfSpaceEmb (n := n) y) ^ (n + 2) :=
    continuous_const.div₀ ((continuous_const.dist hp).pow (n + 2))
      fun y ↦ pow_ne_zero _ (dist_ne_zero.mpr (hne y))
  have hT : Continuous fun y : ℝ^(n - 1) ↦ (innerSL ℝ v) (x - halfSpaceEmb (n := n) y) :=
    continuous_const.inner (continuous_const.sub hp)
  have hK := EuclideanDistance.continuous_invDistPowFDerivFormula (n + 2) continuous_const hp hne
  have hcore : Continuous fun y : ℝ^(n - 1) ↦
      EuclideanDistance.invDistPowSecondFDerivFormula n x (halfSpaceEmb (n := n) y) v :=
    (hS.smul continuous_const).add (hT.smul (hK.const_smul (-(n : ℝ))))
  have hbound : Integrable (fun y : ℝ^(n - 1) ↦ M * (n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ *
      (dist x (halfSpaceEmb (n := n) y) ^ (n + 2))⁻¹) := by
    simpa using (integrable_inv_distance_pow_of_le (n := n) x hx (m := n + 2) (by omega)).const_mul
      (M * (n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖)
  refine hbound.mono' ((hg.comp hp.measurable).aestronglyMeasurable.smul
    hcore.aestronglyMeasurable) (ae_of_all _ fun y ↦ ?_)
  rw [norm_smul]
  calc _ ≤ M * ((n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖ *
        (dist x (halfSpaceEmb (n := n) y) ^ (n + 2))⁻¹) :=
      mul_le_mul (by simpa using hM _ (halfSpaceEmb_mem_boundary (n := n) y))
        (EuclideanDistance.norm_invDistPowFDerivFormula_apply_fderiv_le n (hne y)) (norm_nonneg _)
        ((abs_nonneg _).trans (hM _ (halfSpaceEmb_mem_boundary (n := n) 0)))
    _ = _ := by ring


end PoissonHalfSpace

open PoissonHalfSpace

/-- Differentiate the first inverse-distance derivative under the boundary
integral. This is the second-order dominated-differentiation step for the
half-space Poisson extension. -/
theorem hasFDerivAt_halfSpaceIntegral_invDistPowFDeriv_apply
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ SobolevSpace.HalfSpace.upper n)
    (v : ℝ^n) :
    HasFDerivAt
      (fun x : ℝ^n ↦
        ∫ y : ℝ^(n - 1),
          g (halfSpaceEmb (n := n) y) *
            EuclideanDistance.invDistPowFDerivFormula n x
              (halfSpaceEmb (n := n) y) v
          ∂(volume : Measure ℝ^(n - 1)))
      (∫ y : ℝ^(n - 1),
        (g (halfSpaceEmb (n := n) y)) •
          EuclideanDistance.invDistPowSecondFDerivFormula n x₀
            (halfSpaceEmb (n := n) y) v
        ∂(volume : Measure ℝ^(n - 1)))
      x₀ := by
  classical
  dsimp only [EuclideanDistance.invDistPowSecondFDerivFormula]
  let F : ℝ^n → ℝ^(n - 1) → ℝ := fun x y ↦
    g (halfSpaceEmb (n := n) y) *
      EuclideanDistance.invDistPowFDerivFormula n x (halfSpaceEmb (n := n) y) v
  let K : ℝ^n → ℝ^(n - 1) → ℝ^n →L[ℝ] ℝ := fun x y ↦
    let p : ℝ^n := halfSpaceEmb (n := n) y
    let S : ℝ := (-(n : ℝ)) / dist x p ^ (n + 2)
    let T : ℝ := (innerSL ℝ v) (x - p)
    S • innerSL ℝ v + T • ((-(n : ℝ)) •
      EuclideanDistance.invDistPowFDerivFormula (n + 2) x p)
  let F' : ℝ^n → ℝ^(n - 1) → ℝ^n →L[ℝ] ℝ :=
    fun x y ↦ g (halfSpaceEmb (n := n) y) • K x y
  obtain ⟨bound, bound_integrable, h_bound⟩ :=
    exists_integrable_bound_boundary_smul_of_norm_le_inv_distance_pow hg_bounded hx₀ K
      (m := n + 2) (by omega) (C := (n : ℝ) * ((n + 3 : ℕ) : ℝ) * ‖v‖) (by positivity)
      (fun x hx y ↦ EuclideanDistance.norm_invDistPowFDerivFormula_apply_fderiv_le n
        (halfSpace_ne_halfSpaceEmb hx y))
  have hx₀pos : 0 < x₀ PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx₀
  have hball : Metric.ball x₀ (x₀ PDE.Common.lastIndex / 2) ∈ nhds x₀ :=
    Metric.ball_mem_nhds x₀ (div_pos hx₀pos (by norm_num))
  have hF_int (x : ℝ^n) (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
      Integrable (F x) (volume : Measure ℝ^(n - 1)) := by
    simpa only [F, smul_apply, smul_eq_mul] using
      (integrable_boundary_smul_invDistPowFDeriv hg hg_bounded hx n
        (by omega)).apply_continuousLinearMap v
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (F x) (volume : Measure ℝ^(n - 1)) := by
    filter_upwards [hball] with x hx
    exact (hF_int x (halfHeightBall_subset_upper hx₀ hx)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume : Measure ℝ^(n - 1)) :=
    (integrable_boundary_invDistPowFDeriv_apply_fderiv hg hg_bounded hx₀ v).aestronglyMeasurable
  have h_diff : ∀ᵐ y : ℝ^(n - 1) ∂(volume : Measure ℝ^(n - 1)),
      ∀ x ∈ Metric.ball x₀ (x₀ PDE.Common.lastIndex / 2),
        HasFDerivAt (fun x ↦ F x y) (F' x y) x := by
    refine ae_of_all _ fun y x hx ↦ ?_
    exact (EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply (k := n) (v := v)
      (halfSpace_ne_halfSpaceEmb (halfHeightBall_subset_upper hx₀ hx) y)).const_mul
        (g (halfSpaceEmb (n := n) y))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hball hF_meas (hF_int x₀ hx₀) hF'_meas (ae_of_all _ h_bound) bound_integrable h_diff

namespace PoissonHalfSpace

/-!
### Coordinate derivatives of the boundary integral
-/

/-- Coordinate form of the first derivative of the inverse-distance boundary
integral. -/
theorem partialDeriv_halfSpaceIntegral_div_distance_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    (∂[i]
        (fun z : ℝ^n ↦
          ∫ y : ℝ^(n - 1),
            g (halfSpaceEmb (n := n) y) /
              dist z (halfSpaceEmb (n := n) y) ^ n
            ∂(volume : Measure ℝ^(n - 1)))) x =
      (∫ y : ℝ^(n - 1),
        (g (halfSpaceEmb (n := n) y)) •
          EuclideanDistance.invDistPowFDerivFormula n x
            (halfSpaceEmb (n := n) y)
        ∂(volume : Measure ℝ^(n - 1)))
        (EuclideanSpace.single i (1 : ℝ)) := by
  have h :=
    (hasFDerivAt_halfSpaceIntegral_div_distance_pow
      (n := n) hg hg_bounded hx).fderiv
  exact congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) h

/-- Scalar coordinate form of the first derivative of the inverse-distance
boundary integral. -/
theorem partialDeriv_halfSpaceIntegral_div_distance_pow_scalar
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    (∂[i]
        (fun z : ℝ^n ↦
          ∫ y : ℝ^(n - 1),
            g (halfSpaceEmb (n := n) y) /
              dist z (halfSpaceEmb (n := n) y) ^ n
            ∂(volume : Measure ℝ^(n - 1)))) x =
      ∫ y : ℝ^(n - 1),
        g (halfSpaceEmb (n := n) y) *
          EuclideanDistance.invDistPowFDerivFormula n x
            (halfSpaceEmb (n := n) y)
            (EuclideanSpace.single i (1 : ℝ))
        ∂(volume : Measure ℝ^(n - 1)) := by
  rw [partialDeriv_halfSpaceIntegral_div_distance_pow
    (n := n) hg hg_bounded i hx]
  have hInt :=
    integrable_boundary_smul_invDistPowFDeriv
      (n := n) hg hg_bounded hx n (by omega)
  rw [ContinuousLinearMap.integral_apply hInt]
  simp only [smul_apply, smul_eq_mul]

/-- The `(i, i)` entry of the boundary Hessian integrand, written out. -/
private theorem boundary_hessian_integrand_apply_basis {g : ℝ^n → ℝ} (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) (y : ℝ^(n - 1)) :
    ((g (halfSpaceEmb (n := n) y)) • EuclideanDistance.invDistPowSecondFDerivFormula n x
        (halfSpaceEmb (n := n) y) (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) =
      g (halfSpaceEmb (n := n) y) *
        (let p : ℝ^n := halfSpaceEmb (n := n) y
         (-(n : ℝ)) / dist x p ^ (n + 2) +
          (n : ℝ) * ((n + 2 : ℕ) : ℝ) * (x - p) i ^ 2 / dist x p ^ (n + 4)) := by
  have hxp := halfSpace_ne_halfSpaceEmb (n := n) hx y
  have hpoint := EuclideanLaplacian.fderiv_invDistPowFDeriv_apply_basis (k := n) i hxp
  rw [(EuclideanDistance.hasFDerivAt_invDistPowFDerivFormula_apply
    (v := EuclideanSpace.single i (1 : ℝ)) hxp).fderiv] at hpoint
  simpa only [smul_apply, smul_eq_mul, EuclideanDistance.invDistPowSecondFDerivFormula] using
    congrArg (g (halfSpaceEmb (n := n) y) * ·) hpoint

/-- A repeated coordinate derivative of the inverse-distance boundary
integral. -/
theorem secondPartial_halfSpaceIntegral_div_distance_pow_scalar
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    (∂[i]
        (fun z : ℝ^n ↦
          (∂[i]
            (fun w : ℝ^n ↦
              ∫ y : ℝ^(n - 1),
                g (halfSpaceEmb (n := n) y) /
                  dist w (halfSpaceEmb (n := n) y) ^ n
                ∂(volume : Measure ℝ^(n - 1)))) z)) x =
      ∫ y : ℝ^(n - 1),
        g (halfSpaceEmb (n := n) y) *
          (let p : ℝ^n := halfSpaceEmb (n := n) y
           (-(n : ℝ)) / dist x p ^ (n + 2) +
            (n : ℝ) * ((n + 2 : ℕ) : ℝ) * (x - p) i ^ 2 /
              dist x p ^ (n + 4))
        ∂(volume : Measure ℝ^(n - 1)) := by
  classical
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  have hxpos : 0 < x PDE.Common.lastIndex := by simpa [SobolevSpace.HalfSpace.upper] using hx
  have hEq : (fun z : ℝ^n ↦ (∂[i] fun w : ℝ^n ↦ ∫ y : ℝ^(n - 1), g (halfSpaceEmb (n := n) y) /
      dist w (halfSpaceEmb (n := n) y) ^ n) z) =ᶠ[nhds x] fun z ↦ ∫ y : ℝ^(n - 1),
        g (halfSpaceEmb (n := n) y) *
          EuclideanDistance.invDistPowFDerivFormula n z (halfSpaceEmb (n := n) y) e := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < x PDE.Common.lastIndex / 2)]
      with z hz
    exact partialDeriv_halfSpaceIntegral_div_distance_pow_scalar hg hg_bounded i
      (halfHeightBall_subset_upper hx hz)
  have hΦ : (∂[i] fun z ↦ ∫ y : ℝ^(n - 1), g (halfSpaceEmb (n := n) y) *
      EuclideanDistance.invDistPowFDerivFormula n z (halfSpaceEmb (n := n) y) e) x =
      (∫ y : ℝ^(n - 1), (g (halfSpaceEmb (n := n) y)) •
        EuclideanDistance.invDistPowSecondFDerivFormula n x (halfSpaceEmb (n := n) y) e) e :=
    congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L e)
      (hasFDerivAt_halfSpaceIntegral_invDistPowFDeriv_apply hg hg_bounded hx e).fderiv
  rw [PDE.partialDeriv_congr_nhds i hEq, hΦ, ContinuousLinearMap.integral_apply
    (integrable_boundary_invDistPowFDeriv_apply_fderiv hg hg_bounded hx e)]
  exact integral_congr_ae (ae_of_all _ (boundary_hessian_integrand_apply_basis i hx))


theorem integrable_boundary_secondPartial_inv_dist_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    Integrable
      (fun y : ℝ^(n - 1) ↦
        g (halfSpaceEmb (n := n) y) *
          (let p : ℝ^n := halfSpaceEmb (n := n) y
           (-(n : ℝ)) / dist x p ^ (n + 2) +
            (n : ℝ) * ((n + 2 : ℕ) : ℝ) * (x - p) i ^ 2 /
              dist x p ^ (n + 4)))
      (volume : Measure ℝ^(n - 1)) := by
  exact ((integrable_boundary_invDistPowFDeriv_apply_fderiv hg hg_bounded hx _)
    |>.apply_continuousLinearMap _).congr
      (ae_of_all _ (boundary_hessian_integrand_apply_basis i hx))


/-- The Euclidean Laplacian commutes with the inverse-distance boundary
integral. -/
theorem laplacian_halfSpaceIntegral_div_distance_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    laplacian (n := n)
        (fun z : ℝ^n ↦
          ∫ y : ℝ^(n - 1),
            g (halfSpaceEmb (n := n) y) /
              dist z (halfSpaceEmb (n := n) y) ^ n
            ∂(volume : Measure ℝ^(n - 1))) x =
      ∫ y : ℝ^(n - 1),
        g (halfSpaceEmb (n := n) y) *
          (2 * (n : ℝ) /
            dist x (halfSpaceEmb (n := n) y) ^ (n + 2))
        ∂(volume : Measure ℝ^(n - 1)) := by
  classical
  unfold laplacian
  rw [Finset.sum_congr rfl fun i _ ↦
      secondPartial_halfSpaceIntegral_div_distance_pow_scalar hg hg_bounded i hx,
    ← integral_finsetSum _ fun i _ ↦
      integrable_boundary_secondPartial_inv_dist_pow hg hg_bounded i hx]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have hxp := halfSpace_ne_halfSpaceEmb (n := n) hx y
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun i _ ↦
    (EuclideanLaplacian.secondPartial_inv_dist_pow (k := n) i hxp).symm]
  change laplacian (n := n) (fun w : ℝ^n ↦ (dist w (halfSpaceEmb (n := n) y) ^ n)⁻¹) x = _
  rw [EuclideanLaplacian.laplacian_inv_dist_pow (n := n) (k := n) hxp]
  push_cast
  ring


/-- Each first coordinate derivative of the inverse-distance boundary integral
is differentiable at interior points. -/
theorem differentiableAt_partialDeriv_halfSpaceIntegral_div_distance_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    (i : Fin n) {x : ℝ^n}
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    DifferentiableAt ℝ
      (fun z : ℝ^n ↦
        (∂[i]
          (fun w : ℝ^n ↦
            ∫ y : ℝ^(n - 1),
              g (halfSpaceEmb (n := n) y) /
                dist w (halfSpaceEmb (n := n) y) ^ n
              ∂(volume : Measure ℝ^(n - 1)))) z) x := by
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  let Φ : ℝ^n → ℝ := fun z ↦
    ∫ y : ℝ^(n - 1),
      g (halfSpaceEmb (n := n) y) *
        EuclideanDistance.invDistPowFDerivFormula n z
          (halfSpaceEmb (n := n) y) e
      ∂(volume : Measure ℝ^(n - 1))
  have hxpos : 0 < x PDE.Common.lastIndex := by
    simpa [SobolevSpace.HalfSpace.upper] using hx
  have hball :
      Metric.ball x (x PDE.Common.lastIndex / 2) ∈ nhds x :=
    Metric.ball_mem_nhds x (by positivity)
  have hEq :
      (fun z : ℝ^n ↦
        (∂[i]
          (fun w : ℝ^n ↦
            ∫ y : ℝ^(n - 1),
              g (halfSpaceEmb (n := n) y) /
                dist w (halfSpaceEmb (n := n) y) ^ n
              ∂(volume : Measure ℝ^(n - 1)))) z) =ᶠ[nhds x] Φ := by
    filter_upwards [hball] with z hz
    have hz_upper :=
      halfHeightBall_subset_upper (n := n) hx hz
    simpa only [Φ, e] using
      partialDeriv_halfSpaceIntegral_div_distance_pow_scalar
        (n := n) hg hg_bounded i hz_upper
  have hΦ : DifferentiableAt ℝ Φ x := by
    simpa only [Φ, e] using
      (hasFDerivAt_halfSpaceIntegral_invDistPowFDeriv_apply
        (n := n) hg hg_bounded hx e).differentiableAt
  exact hΦ.congr_of_eventuallyEq hEq

/-- The vertical derivative of the inverse-distance boundary integral. The
boundary pole has zero last coordinate, so only the interior height remains. -/
theorem partialDeriv_last_halfSpaceIntegral_div_distance_pow
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M)
    {x : ℝ^n} (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    (∂[PDE.Common.lastIndex]
        (fun z : ℝ^n ↦
          ∫ y : ℝ^(n - 1),
            g (halfSpaceEmb (n := n) y) /
              dist z (halfSpaceEmb (n := n) y) ^ n
            ∂(volume : Measure ℝ^(n - 1)))) x =
      ∫ y : ℝ^(n - 1),
        g (halfSpaceEmb (n := n) y) *
          ((-(n : ℝ)) /
            dist x (halfSpaceEmb (n := n) y) ^ (n + 2) *
            x PDE.Common.lastIndex)
        ∂(volume : Measure ℝ^(n - 1)) := by
  rw [partialDeriv_halfSpaceIntegral_div_distance_pow_scalar
    (n := n) hg hg_bounded PDE.Common.lastIndex hx]
  apply integral_congr_ae
  refine ae_of_all _ fun y ↦ ?_
  let last := PDE.Common.lastIndex (n := n)
  let p : ℝ^n := halfSpaceEmb (n := n) y
  have hxp : x ≠ p :=
    halfSpace_ne_halfSpaceEmb (n := n) hx y
  have hpzero : p last = 0 := by
    exact lastCoord_halfSpaceEmb (n := n) y
  have hcoord :
      (innerSL ℝ (EuclideanSpace.single last (1 : ℝ))) (x - p) =
        x last := by
    rw [innerSL_apply_apply]
    simpa [hpzero] using
      (EuclideanSpace.inner_single_left
        (i := last) (a := (1 : ℝ)) (v := x - p))
  change
    g (halfSpaceEmb (n := n) y) *
        EuclideanDistance.invDistPowFDerivFormula n x p
          (EuclideanSpace.single last (1 : ℝ)) =
      g (halfSpaceEmb (n := n) y) *
        ((-(n : ℝ)) / dist x p ^ (n + 2) * x last)
  rw [EuclideanDistance.invDistPowFDerivFormula_apply_eq_of_ne
    n hxp, hcoord]

end PoissonHalfSpace

end GreenFunction
