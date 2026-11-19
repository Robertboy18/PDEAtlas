/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ExponentialTilt
public import PDE.Parabolic.Heat.InitialValue
import PDE.Parabolic.Heat.Kernel.Integrability
import Mathlib.MeasureTheory.Measure.Haar.Unique
import CAS.ExactTactic

/-!
# Gaussian representation of exponential tilts

Completing the square moves the exponential tilt from the heat solution to its
initial datum. Bounded amplitudes consequently give integrable convolutions
even after multiplication by an exponentially growing weight.
-/

@[expose] public noncomputable section

open PDE.Common MeasureTheory

namespace HeatEquation

/-- Completing the square in a one-dimensional Gaussian transfers the exponential
weight from the solution to the integration variable. -/
theorem exponentialTilt_kernel_identity {ν : ℝ} (hν : 0 < ν) (k : ℝ)
    (p : ℝ^2) (hp : 0 < p 0) (y : ℝ^1) :
    exponentialTiltWeight ν k p *
        fundamentalSolutionHeat (spatialPartCLM 1 (exponentialTiltChart ν k p) - y) (ν * p 0) =
      fundamentalSolutionHeat (spatialPartCLM 1 p - y) (ν * p 0) * Real.exp (k * y 0) := by
  have ht := mul_pos hν hp
  have he :
      Real.exp (k * p 1 + ν * k ^ 2 * p 0) *
          Real.exp (-(‖spatialPartCLM 1 (exponentialTiltChart ν k p) - y‖ ^ 2 /
            (4 * (ν * p 0)))) =
        Real.exp (-(‖spatialPartCLM 1 p - y‖ ^ 2 / (4 * (ν * p 0)))) *
          Real.exp (k * y 0) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one, PiLp.sub_apply,
      spatialPartCLM_apply, exponentialTiltChart,
      Fin.succ_zero_eq_one, Matrix.cons_val_one]
    cas using ht.ne'
  simp only [fundamentalSolutionHeat, ite_eq_right ht.not_ge, exponentialTiltWeight]
  rw [mul_left_comm, he]
  exact (mul_assoc _ _ _).symm

/-- A tilted bounded-data heat formula is exactly the heat convolution of the
exponentially weighted datum. The identity itself requires no integrability assumption. -/
theorem exponentialTilt_initialValueSolution_eq_integral
    {ν : ℝ} (hν : 0 < ν) (k : ℝ) (g : ℝ^1 → ℝ)
    (p : ℝ^2) (hp : 0 < p 0) :
    exponentialTilt ν k
        (fun q : ℝ^2 ↦ initialValueSolution g (spatialPartCLM 1 q) (q 0)) p =
      ∫ y : ℝ^1, fundamentalSolutionHeat (spatialPartCLM 1 p - y) (ν * p 0) *
        (Real.exp (k * y 0) * g y) := by
  have ht := mul_pos hν hp
  unfold exponentialTilt
  change exponentialTiltWeight ν k p *
    initialValueSolution g (spatialPartCLM 1 (exponentialTiltChart ν k p)) (ν * p 0) = _
  rw [initialValueSolution, ite_eq_right ht.not_ge, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ by
    dsimp only
    rw [← mul_assoc, exponentialTilt_kernel_identity hν k p hp y, mul_assoc]

/-- Gaussian decay dominates an exponentially tilted bounded continuous amplitude. -/
theorem integrable_exponentialTilt_kernel_mul
    {ν : ℝ} (hν : 0 < ν) (k : ℝ) (g : ℝ^1 → ℝ)
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M)
    (p : ℝ^2) (hp : 0 < p 0) :
    Integrable (fun y : ℝ^1 ↦
      fundamentalSolutionHeat (spatialPartCLM 1 p - y) (ν * p 0) *
        (Real.exp (k * y 0) * g y)) := by
  obtain ⟨M, hM⟩ := hgb
  have hK := (fundamentalSolutionHeat_integrable (n := 1) (ν * p 0)
    (mul_pos hν hp)).comp_sub_left (spatialPartCLM 1 (exponentialTiltChart ν k p))
  have hI := hK.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  apply (hI.const_mul (exponentialTiltWeight ν k p)).congr
  exact ae_of_all _ fun y ↦ by
    dsimp only
    rw [← mul_assoc, exponentialTilt_kernel_identity hν k p hp y, mul_assoc]

end HeatEquation
