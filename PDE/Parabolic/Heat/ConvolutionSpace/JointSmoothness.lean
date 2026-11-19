/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import PDE.Parabolic.Heat.InitialValue
import PDE.Analysis.Calculus.GaussianIntegral.Regularity
import CAS.ExactTactic

/-!
# Joint smoothness of the heat-kernel convolution

The heat evolution of bounded continuous data is jointly `C∞` at positive time. Expanding `‖x-y‖²`
expresses the convolution as a smooth prefactor times a Gaussian integral with parameters
`(1/(4t), x/(2t))`. Repeated dominated differentiation of that integral uses polynomial moments of a
slower Gaussian. No derivative or integrability of the initial datum is assumed.

This is part (i) of Evans's §2.3.1(b), Theorem 1. The heat equation and joint initial trace of this
same formula are proved in `PointwiseIVP`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), Theorem 1 (Solution of initial-value problem) and
  step 1 of its proof, p. 47.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Common PDE.Analysis.GaussianIntegral
open scoped Topology ContDiff

namespace HeatEquation

variable {n : ℕ}

private theorem initialValueSolution_eq_gaussian_integral
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    initialValueSolution g x t =
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))) *
        ∫ y, Real.exp (exponentCLM y (1 / (4 * t), (1 / (2 * t)) • x)) • g y := by
  have hexp (y : ℝ^n) :
      Real.exp (-(‖x - y‖ ^ 2 / (4 * t))) =
        Real.exp (-‖x‖ ^ 2 / (4 * t)) *
          Real.exp (exponentCLM y (1 / (4 * t), (1 / (2 * t)) • x)) := by
    rw [← Real.exp_add, exponentCLM_apply, inner_smul_right, real_inner_comm x y,
      norm_sub_sq_real]
    congr 1
    cas using ht.ne'
  rw [initialValueSolution, ite_eq_right ht.not_ge, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  simp only [fundamentalSolutionHeat, ite_eq_right ht.not_ge, hexp, smul_eq_mul]
  ring

/-- Every joint derivative of the heat-kernel convolution exists and is continuous
near each positive-time point, for bounded continuous initial data. -/
theorem contDiffAt_initialValueSolution_timeSpace
    (g : ℝ^n → ℝ) (x : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ^n ↦ initialValueSolution g p.2 p.1) (t, x) := by
  obtain ⟨M, hM⟩ := hgb
  have htransform := contDiffOn_integral_exp_smul g hg (C := M) 0
    (fun y ↦ by simpa only [pow_zero, mul_one, Real.norm_eq_abs] using hM y)
  let P : ℝ × ℝ^n → ℝ × ℝ^n :=
    fun p ↦ (1 / (4 * p.1), (1 / (2 * p.1)) • p.2)
  have h4 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ^n ↦ 4 * p.1) (t, x) :=
    contDiffAt_const.mul contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ^n ↦ 2 * p.1) (t, x) :=
    contDiffAt_const.mul contDiffAt_fst
  have hP : ContDiffAt ℝ ∞ P (t, x) :=
    (contDiffAt_const.div h4 (by positivity)).prodMk
      ((contDiffAt_const.div h2 (by positivity)).smul contDiffAt_snd)
  have hopen : IsOpen {p : ℝ × ℝ^n | 0 < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hpositive : 0 < (P (t, x)).1 := by dsimp [P]; positivity
  have hI : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ^n ↦ ∫ y, Real.exp (exponentCLM y (P p)) • g y) (t, x) :=
    (htransform.contDiffAt (hopen.mem_nhds hpositive)).comp (t, x) hP
  have hnorm : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ^n ↦ ‖p.2‖ ^ 2) (t, x) :=
    contDiffAt_snd.norm_sq ℝ
  have hpref : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ^n ↦ (4 * Real.pi * p.1) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖p.2‖ ^ 2 / (4 * p.1))) (t, x) :=
    ((contDiffAt_const.mul contDiffAt_fst).rpow_const_of_ne (by positivity)).mul
      ((hnorm.neg.div h4 (by positivity)).exp)
  apply (hpref.mul hI).congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds ht] with p hp
  exact initialValueSolution_eq_gaussian_integral g p.2 p.1 hp

/-- The heat convolution of bounded continuous data is jointly smooth throughout
the positive-time half-space. -/
theorem contDiffOn_initialValueSolution_timeSpace
    (g : ℝ^n → ℝ) (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ^n ↦ initialValueSolution g p.2 p.1) {p | 0 < p.1} :=
  fun p hp ↦
    (contDiffAt_initialValueSolution_timeSpace g p.2 p.1 hp hg hgb).contDiffWithinAt

/-- Joint smoothness in the Euclidean spacetime coordinates used by the PDE operators. -/
theorem contDiffOn_initialValueSolution_spacetime
    (g : ℝ^n → ℝ) (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ^(n + 1) ↦ initialValueSolution g (spatialPartCLM n p) (p 0))
      {p | 0 < p 0} := by
  intro p hp
  exact ((contDiffAt_initialValueSolution_timeSpace g (spatialPartCLM n p) (p 0)
    hp hg hgb).comp p
      ((EuclideanSpace.proj (0 : Fin (n + 1))).contDiff.contDiffAt.prodMk
        (spatialPartCLM n).contDiff.contDiffAt)).contDiffWithinAt

end HeatEquation
