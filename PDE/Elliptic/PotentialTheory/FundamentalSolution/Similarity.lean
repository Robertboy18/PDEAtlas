/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Congruence

/-!
# Fundamental solutions under translations and dilations

A positive dilation changes the planar fundamental solution by a constant and
multiplies the Newtonian kernel by the appropriate power of the scale. Both
operations preserve harmonicity away from the pole. Translation then gives the
image kernels used in Green functions.
-/

@[expose] public section

open PDE (laplacian)

namespace PotentialTheory

open Filter Topology PDE.Analysis

/-- A positive dilation adds a constant to the planar logarithmic kernel. -/
theorem fundamentalSolution_two_smul {c : ℝ} (hc : 0 < c) {x : ℝ^2} (hx : x ≠ 0) :
    fundamentalSolution 2 (c • x) =
      fundamentalSolution 2 x - (1 / (2 * Real.pi)) * Real.log c := by
  rw [fundamentalSolution_two, fundamentalSolution_two, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hx)]
  ring

/-- In dimension at least three the Newtonian kernel is homogeneous of degree `2 - n`.
The identity also respects its chosen value at the pole. -/
theorem fundamentalSolution_smul_of_three_le {n : ℕ} (hn : 3 ≤ n)
    {c : ℝ} (hc : 0 < c) (x : ℝ^n) :
    fundamentalSolution n (c • x) = (c ^ (n - 2))⁻¹ * fundamentalSolution n x := by
  rw [fundamentalSolution_of_three_le hn, fundamentalSolution_of_three_le hn,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  simp only [one_div, mul_inv_rev]
  ring

/-- Positive dilations preserve harmonicity of the fundamental solution off the pole. -/
theorem laplacian_fundamentalSolution_smul_eq_zero (n : ℕ) [Fact (0 < n)]
    {c : ℝ} (hc : 0 < c) {x : ℝ^n} (hx : x ≠ 0) :
    laplacian (fun y ↦ fundamentalSolution n (c • y)) x = 0 := by
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by have := Fact.out (p := 0 < n); omega) with h | h | h
  · subst n
    have hscaled : (fun y : ℝ^1 ↦ fundamentalSolution 1 (c • y)) =
        fun y ↦ c * fundamentalSolution 1 y := by
      funext y
      rw [fundamentalSolution_one, fundamentalSolution_one, norm_smul,
        Real.norm_eq_abs, abs_of_pos hc]
      ring
    rw [hscaled, PDE.laplacian_const_smul, laplacian_fundamentalSolution_eq_zero 1 x hx, mul_zero]
  · subst n
    have hscaled : (fun y : ℝ^2 ↦ fundamentalSolution 2 (c • y)) =ᶠ[𝓝 x]
        fun y ↦ fundamentalSolution 2 y - (1 / (2 * Real.pi)) * Real.log c := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      exact fundamentalSolution_two_smul hc hy
    rw [EuclideanLaplacian.laplacian_congr_nhds hscaled,
      PDE.laplacian_sub _ _ x ((contDiffAt_fundamentalSolution 2 x hx).of_le (by norm_num))
        contDiffAt_const,
      laplacian_fundamentalSolution_eq_zero 2 x hx, PDE.laplacian_const, sub_self]
  · have hscaled : (fun y : ℝ^n ↦ fundamentalSolution n (c • y)) =
        fun y ↦ (c ^ (n - 2))⁻¹ * fundamentalSolution n y :=
      funext (fundamentalSolution_smul_of_three_le h hc)
    rw [hscaled, PDE.laplacian_const_smul,
      laplacian_fundamentalSolution_eq_zero n x hx, mul_zero]

/-- A translated and positively dilated fundamental solution is smooth away from its pole. -/
theorem contDiffAt_fundamentalSolution_smul_sub (n : ℕ) [Fact (0 < n)]
    {c : ℝ} (hc : 0 < c) (a x : ℝ^n) (hx : x ≠ a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ fundamentalSolution n (c • (y - a))) x :=
  (contDiffAt_fundamentalSolution n _ (smul_ne_zero hc.ne' (sub_ne_zero.mpr hx))).comp x
    ((contDiffAt_id.sub contDiffAt_const).const_smul c)

/-- The image kernel obtained by translation and positive dilation is harmonic off its pole. -/
theorem laplacian_fundamentalSolution_smul_sub_eq_zero (n : ℕ) [Fact (0 < n)]
    {c : ℝ} (hc : 0 < c) (a x : ℝ^n) (hx : x ≠ a) :
    laplacian (fun y ↦ fundamentalSolution n (c • (y - a))) x = 0 := by
  have hsmooth : ContDiffAt ℝ 2 (fun y ↦ fundamentalSolution n (c • y)) (x - a) :=
    ((contDiffAt_fundamentalSolution n _
      (smul_ne_zero hc.ne' (sub_ne_zero.mpr hx))).comp (x - a)
        (contDiffAt_id.const_smul c)).of_le (by norm_num)
  rw [PDE.laplacian_comp_sub_right _ a x hsmooth]
  exact laplacian_fundamentalSolution_smul_eq_zero n hc (sub_ne_zero.mpr hx)

end PotentialTheory
