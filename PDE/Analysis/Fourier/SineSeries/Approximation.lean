/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalLp
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Uniform approximation of interval Dirichlet data

Subtracting the affine interpolant of the endpoint errors from a polynomial
approximant preserves uniform approximation and makes both boundary values zero.
Sine coefficients respect subtraction and are bounded by the uniform data norm.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open Set MeasureTheory PDE.Representations

/-- Continuous zero-boundary interval data admit uniformly close `C²` approximants
with the same boundary values. No smooth extension of the data is required. -/
theorem exists_contDiffOn_zero_boundary_near {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ → ℝ, ContDiffOn ℝ 2 q (Icc 0 1) ∧ q 0 = 0 ∧ q 1 = 0 ∧
      ∀ x ∈ Icc 0 1, ‖q x - g x‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg (ε / 4) (by positivity)
  let q : ℝ → ℝ := fun x ↦ p.eval x - (1 - x) * p.eval 0 - x * p.eval 1
  have hpc : ContDiff ℝ 2 (fun x : ℝ ↦ p.eval x) := by
    simpa using p.contDiff_aeval (𝕜 := ℝ) 2
  have hq : ContDiff ℝ 2 q :=
    (hpc.sub ((contDiff_const.sub contDiff_id).mul contDiff_const)).sub
      (contDiff_id.mul contDiff_const)
  refine ⟨q, hq.contDiffOn, by simp [q], by simp [q], ?_⟩
  intro x hx
  have hp0 : ‖p.eval 0‖ < ε / 4 := by
    simpa only [hzero, sub_zero, Real.norm_eq_abs] using hp 0 ⟨le_rfl, zero_le_one⟩
  have hp1 : ‖p.eval 1‖ < ε / 4 := by
    simpa only [hone, sub_zero, Real.norm_eq_abs] using hp 1 ⟨zero_le_one, le_rfl⟩
  have hpX : ‖p.eval x - g x‖ < ε / 4 := hp x hx
  have h0 : ‖(1 - x) * p.eval 0‖ ≤ ‖p.eval 0‖ := by
    rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hx.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hx.1])
  have h1 : ‖x * p.eval 1‖ ≤ ‖p.eval 1‖ := by
    rw [norm_mul, Real.norm_of_nonneg hx.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  have he : q x - g x = (p.eval x - g x) - (1 - x) * p.eval 0 - x * p.eval 1 := by
    dsimp only [q]
    ring
  rw [he]
  have hnorm := norm_sub_le ((p.eval x - g x) - (1 - x) * p.eval 0) (x * p.eval 1)
  have hnorm' := norm_sub_le (p.eval x - g x) ((1 - x) * p.eval 0)
  linarith

/-- Sine coefficients are linear under subtraction of continuous interval data. -/
theorem intervalCoefficient_sub {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1)) (n : ℕ) :
    intervalCoefficient (fun x ↦ g x - h x) n =
      intervalCoefficient g n - intervalCoefficient h n := by
  have hi {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
      IntervalIntegrable (fun x ↦ f x * intervalDirichletSineMode n x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using
      hf.fun_mul (contDiff_intervalDirichletSineMode (k := 0) n).continuous.continuousOn
  unfold intervalCoefficient
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hi hg) (hi hh)]
  ring

/-- A uniform bound for the data gives a uniform bound for all sine coefficients. -/
theorem norm_intervalCoefficient_le_of_bound {g : ℝ → ℝ} {M : ℝ}
    (hbound : ∀ x ∈ Icc 0 1, ‖g x‖ ≤ M) (n : ℕ) :
    ‖intervalCoefficient g n‖ ≤ 2 * M := by
  unfold intervalCoefficient
  rw [norm_mul, Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun x ↦ g x * intervalDirichletSineMode n x) ?_
  · simpa using h
  · intro x hx
    have hx' : x ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le zero_le_one] using hx
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [intervalDirichletSineMode, Real.norm_eq_abs] using
        Real.abs_sin_le_one (((n.succ : ℝ) * Real.pi) * x))).trans
      (hbound x (Ioc_subset_Icc_self hx'))

end PDE.Analysis.Fourier.SineSeries
