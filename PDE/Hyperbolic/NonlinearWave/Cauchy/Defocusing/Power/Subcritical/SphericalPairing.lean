/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean

/-!
# Compact spatial testing of the physical wave kernel

Translation invariance and the symmetry of the sphere move spherical averaging
from a continuous field onto a compactly supported test. Compact support is
required only of the test. These identities are the spatial duality step in
testing C¹ nonlinear integral trajectories against the wave equation.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem integrable_spherical_pairing {F φ : ℝ^3 → ℝ}
    (hF : Continuous F) (hφ : Continuous φ) (hφs : HasCompactSupport φ) (r : ℝ) :
    Integrable (fun q : Metric.sphere (0 : ℝ^3) 1 × ℝ^3 ↦ F (q.2 + r • (q.1 : ℝ^3)) * φ q.2)
      (((volume : Measure (ℝ^3)).toSphere).prod volume) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  refine HasCompactSupport.intro (isCompact_univ.prod hφs.isCompact) fun q hq ↦ ?_
  have hx : q.2 ∉ tsupport φ := by simpa only [mem_prod, mem_univ, true_and] using hq
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

private theorem integrable_shifted_spherical_test {F φ : ℝ^3 → ℝ}
    (hF : Continuous F) (hφ : Continuous φ) (hφs : HasCompactSupport φ) (r : ℝ) :
    Integrable (fun q : Metric.sphere (0 : ℝ^3) 1 × ℝ^3 ↦ F q.2 * φ (q.2 - r • (q.1 : ℝ^3)))
      (((volume : Measure (ℝ^3)).toSphere).prod volume) := by
  obtain ⟨R, _, hR⟩ := hφs.exists_pos_le_norm
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro (isCompact_univ.prod (isCompact_closedBall (0 : ℝ^3) (R + |r|)))
  intro q hq
  have hx : R + |r| < ‖q.2‖ := by
    simpa only [mem_prod, mem_univ, true_and, Metric.mem_closedBall,
      dist_zero_right, not_le] using hq
  have hn : ‖r • (q.1 : ℝ^3)‖ = |r| := by
    rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp q.1.property, mul_one]
  have hb := norm_sub_norm_le q.2 (r • (q.1 : ℝ^3))
  rw [hn] at hb
  rw [hR (q.2 - r • (q.1 : ℝ^3)) (by linarith), mul_zero]

/-- Spherical averaging is self-adjoint against a continuous compactly supported
spatial test. The tested field itself need not be integrable or compactly supported. -/
theorem integral_unitSphereAverage_mul_eq {F φ : ℝ^3 → ℝ}
    (hF : Continuous F) (hφ : Continuous φ) (hφs : HasCompactSupport φ) (r : ℝ) :
    (∫ x : ℝ^3, unitSphereAverage 3 F x r * φ x) = ∫ x : ℝ^3, F x * unitSphereAverage 3 φ x r := by
  let σ := (volume : Measure (ℝ^3)).toSphere
  have hleft := integrable_spherical_pairing hF hφ hφs r
  have hright := integrable_shifted_spherical_test hF hφ hφs r
  have hshift (ω : Metric.sphere (0 : ℝ^3) 1) : (∫ x : ℝ^3, F (x + r • (ω : ℝ^3)) * φ x) =
        ∫ x : ℝ^3, F x * φ (x - r • (ω : ℝ^3)) := by
    simpa only [add_sub_cancel_right] using integral_add_right_eq_self
      (fun x : ℝ^3 ↦ F x * φ (x - r • (ω : ℝ^3))) (r • (ω : ℝ^3))
  calc
    _ = (∫ x : ℝ^3, ∫ ω, F (x + r • (ω : ℝ^3)) * φ x ∂σ) /
        unitSphereArea 3 := by
      simp only [unitSphereAverage, div_mul_eq_mul_div, ← integral_mul_const, integral_div, σ]
    _ = (∫ ω, ∫ x : ℝ^3, F (x + r • (ω : ℝ^3)) * φ x ∂volume ∂σ) /
        unitSphereArea 3 := by
      congr 1
      exact integral_integral_swap (f := fun (x : ℝ^3) (ω : Metric.sphere (0 : ℝ^3) 1) ↦
          F (x + r • (ω : ℝ^3)) * φ x) hleft.swap
    _ = (∫ ω, ∫ x : ℝ^3, F x * φ (x - r • (ω : ℝ^3)) ∂volume ∂σ) /
        unitSphereArea 3 := by simp_rw [hshift]
    _ = (∫ x : ℝ^3, ∫ ω, F x * φ (x - r • (ω : ℝ^3)) ∂σ) /
        unitSphereArea 3 := by rw [integral_integral_swap hright]
    _ = ∫ x : ℝ^3, F x * unitSphereAverage 3 φ x (-r) := by
      simp only [unitSphereAverage, neg_smul, ← sub_eq_add_neg, integral_const_mul, σ]
      simp_rw [← mul_div_assoc]
      rw [integral_div]
    _ = _ := by simp_rw [unitSphereAverage_neg_radius]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
