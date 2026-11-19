/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution

/-!
# Flux normalization of the Laplace fundamental solution

For `n ≥ 2`, the outward radial flux of the fundamental solution through every sphere centered at
its pole is `-1` (`integral_deriv_fundamentalSolution_smul`): along each ray, the radial
derivative at radius `r` is minus the reciprocal of the area of the sphere of radius `r`
(`deriv_fundamentalSolution_smul`). This is the normalization of the singular boundary term in
the distributional identity `-Δ Φ = δ₀`. Evans computes the same normal derivative, for the
inward normal, in step 3 of his proof of §2.2.1, Theorem 1, where the constants of his
definition (6) make the small-sphere term tend to `-f(x)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(a), the fundamental solution (6), p. 22; §2.2.1(b),
  step 3 of the proof of Theorem 1, p. 24.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PotentialTheory

open MeasureTheory
open PDE.Analysis

section

variable {n : ℕ} [Fact (0 < n)]

private theorem deriv_fundamentalSolution_smul_mul_unitSphereArea
    (hn : 2 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    deriv (fun ρ : ℝ ↦ fundamentalSolution n (ρ • (ω : ℝ^n))) r *
        (r ^ (n - 1) * PDE.Analysis.unitSphereArea n) = -1 := by
  classical
  have hωnorm : ‖(ω : ℝ^n)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ω.property
  have hωne : (ω : ℝ^n) ≠ 0 :=
    norm_ne_zero_iff.mp (by simp [hωnorm])
  by_cases h2 : n = 2
  · subst n
    have hlocal :
        (fun ρ : ℝ ↦ fundamentalSolution 2 (ρ • (ω : ℝ^2))) =ᶠ[nhds r]
          fun ρ ↦ -(1 / (2 * Real.pi)) * Real.log ρ := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with ρ hρ
      change 0 < ρ at hρ
      have hρsmul : ρ • (ω : ℝ^2) ≠ 0 := smul_ne_zero hρ.ne' hωne
      simp [fundamentalSolution, hρsmul, norm_smul, hωnorm, abs_of_pos hρ]
    rw [hlocal.deriv_eq, deriv_const_mul _ (Real.differentiableAt_log hr.ne'), Real.deriv_log,
      PDE.Analysis.unitSphereArea_eq, unitBallVolume_two]
    field_simp
    ring
  · have hn3 : 3 ≤ n := by omega
    let A : ℝ := ((n : ℝ) - 2) * (n : ℝ) * unitBallVolume n
    have hA : A ≠ 0 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      exact (mul_pos (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos n)).ne'
    have h1 : n ≠ 1 := by omega
    have hlocal :
        (fun ρ : ℝ ↦ fundamentalSolution n (ρ • (ω : ℝ^n))) =ᶠ[nhds r]
          fun ρ ↦ (A * ρ ^ (n - 2))⁻¹ := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with ρ hρ
      change 0 < ρ at hρ
      have hρsmul : ρ • (ω : ℝ^n) ≠ 0 := smul_ne_zero hρ.ne' hωne
      simp [fundamentalSolution, hρsmul, h1, h2, hn3, A, norm_smul, hωnorm,
        abs_of_pos hρ, one_div]
    rw [hlocal.deriv_eq]
    have hden : A * r ^ (n - 2) ≠ 0 := mul_ne_zero hA (pow_ne_zero _ hr.ne')
    have hderiv := (((hasDerivAt_const r A).mul ((hasDerivAt_id r).pow (n - 2))).inv hden).deriv
    change
      deriv (((fun _ : ℝ ↦ A) * (id : ℝ → ℝ) ^ (n - 2))⁻¹) r *
          (r ^ (n - 1) * PDE.Analysis.unitSphereArea n) = -1
    rw [hderiv, PDE.Analysis.unitSphereArea_eq]
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_mul, zero_add, mul_one]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn3
    have hnk : (n : ℝ) = k + 3 := by rw [hk]; push_cast; ring
    rw [show n - 2 - 1 = k by omega, show n - 2 = k + 1 by omega, show n - 1 = k + 2 by omega]
    have hV := (unitBallVolume_pos n).ne'
    dsimp only [A]
    rw [hnk, show (k : ℝ) + 3 - 2 = k + 1 by ring]
    push_cast
    field_simp
    ring

/-- Along every unit ray, the radial derivative of the fundamental solution at radius `r` is the
negative reciprocal of the surface area of the sphere of radius `r`. -/
theorem deriv_fundamentalSolution_smul
    (hn : 2 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    deriv (fun ρ : ℝ ↦ fundamentalSolution n (ρ • (ω : ℝ^n))) r =
      -1 / (r ^ (n - 1) * PDE.Analysis.unitSphereArea n) := by
  have hden : r ^ (n - 1) * PDE.Analysis.unitSphereArea n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hr.ne')
      (ne_of_gt (PDE.Analysis.unitSphereArea_pos (n := n)))
  exact (eq_div_iff hden).2
    (deriv_fundamentalSolution_smul_mul_unitSphereArea hn ω hr)

/-- The radial derivative of the fundamental solution times the surface area of the sphere of
radius `r` is `-1`. -/
theorem deriv_fundamentalSolution_smul_mul_surfaceArea
    (hn : 2 ≤ n) (ω : Metric.sphere (0 : ℝ^n) 1) {r : ℝ} (hr : 0 < r) :
    deriv (fun ρ : ℝ ↦ fundamentalSolution n (ρ • (ω : ℝ^n))) r *
        PDE.Analysis.sphereArea n r = -1 := by
  simpa [PDE.Analysis.sphereArea, abs_of_pos hr] using
    deriv_fundamentalSolution_smul_mul_unitSphereArea hn ω hr

/-- The total outward radial flux of the fundamental solution through a sphere centered at its
pole is `-1`, expressed using Mathlib's unit-sphere measure. -/
theorem integral_deriv_fundamentalSolution_smul
    (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    |r| ^ (n - 1) *
        ∫ ω, deriv (fun ρ : ℝ ↦ fundamentalSolution n (ρ • (ω : ℝ^n))) r
          ∂((volume : Measure (ℝ^n)).toSphere) = -1 := by
  simp_rw [deriv_fundamentalSolution_smul hn _ hr]
  rw [MeasureTheory.integral_const]
  simp only [smul_eq_mul]
  change
    |r| ^ (n - 1) *
      (PDE.Analysis.unitSphereArea n *
        (-1 / (r ^ (n - 1) * PDE.Analysis.unitSphereArea n))) = -1
  rw [abs_of_pos hr]
  field_simp [pow_ne_zero (n - 1) hr.ne',
    (ne_of_gt (PDE.Analysis.unitSphereArea_pos (n := n)))]

end

end PotentialTheory
