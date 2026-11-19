/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.Estimates
import CAS.ExactTactic

/-!
# Uniform convergence to the harmonic-mean Dirichlet solution

For every positive continuous one-periodic medium and every continuous source,
the constructed solutions converge uniformly on `[0,1]` as `ε → 0⁺`. The quantitative
theorem provides constants derived from the data, with no convergence or solution
assumption. The gradient reconstruction uses the periodic cell corrector.
-/

@[expose] public section

noncomputable section

open PDE.Analysis (primitive)

namespace PDE.Elliptic.Homogenization.PeriodicMedium

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped Topology

variable (a : PeriodicMedium)

/-- Continuous forcing admits an error constant and a positive range of microscopic scales. -/
theorem exists_solution_error_bound {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
      ∀ x ∈ Icc (0 : ℝ) 1,
        |a.solution f ε x - a.homogenizedSolution f x| ≤ C * |ε| := by
  obtain ⟨K, hK, hb⟩ := exists_fluctuation_bound a.continuous_reciprocal a.periodic_reciprocal
  obtain ⟨M, hM, hfM⟩ := (isCompact_Icc.image hf).isBounded.exists_pos_norm_le
  have hfb : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M := fun y hy ↦ by
    simpa only [Real.norm_eq_abs] using hfM (f y) (mem_image_of_mem f hy)
  refine ⟨15 * M * K, by positivity, a.meanReciprocal / (2 * K), by
    exact div_pos a.meanReciprocal_pos (by positivity), ?_⟩
  intro ε hε hsmall x hx
  have hs : |ε| * K ≤ a.meanReciprocal / 2 := by
    have := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp hsmall
    nlinarith
  calc
    |a.solution f ε x - a.homogenizedSolution f x| ≤ 15 * M * (|ε| * K) :=
      a.solution_error_le hf hK.le hM.le hb hfb hε hs hx
    _ = (15 * M * K) * |ε| := by cas

/-- Uniform convergence of the constructed Dirichlet solutions as `ε → 0⁺`. -/
theorem tendstoUniformlyOn_solution {f : ℝ → ℝ} (hf : Continuous f) :
    TendstoUniformlyOn (a.solution f) (a.homogenizedSolution f)
      (𝓝[>] (0 : ℝ)) (Icc (0 : ℝ) 1) := by
  obtain ⟨C, hC, ε₀, hε₀, hb⟩ := a.exists_solution_error_bound hf
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have ht : Tendsto (fun ε : ℝ ↦ |ε|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hm : 0 < min ε₀ (η / C) := lt_min hε₀ (div_pos hη hC)
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hm)] with ε hε hs x hx
  rw [Real.dist_eq, abs_sub_comm]
  calc
    |a.solution f ε x - a.homogenizedSolution f x| ≤ C * |ε| :=
      hb ε (ne_of_gt hε) (lt_of_lt_of_le hs (min_le_left _ _)).le x hx
    _ < η := by
      have := (lt_div_iff₀ hC).mp (lt_of_lt_of_le hs (min_le_right _ _))
      linarith

/-- Pointwise convergence is a consequence of the uniform theorem. -/
theorem tendsto_solution {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun ε ↦ a.solution f ε x) (𝓝[>] (0 : ℝ)) (𝓝 (a.homogenizedSolution f x)) :=
  (a.tendstoUniformlyOn_solution hf).tendsto_at hx

/-- The cell gradient reconstructs the oscillatory gradient up to the flux-constant error. -/
theorem gradient_corrector_error {f : ℝ → ℝ} (hf : Continuous f) (ε x : ℝ) :
    deriv (a.solution f ε) x -
        (1 + deriv a.corrector (x / ε)) * deriv (a.homogenizedSolution f) x =
      (a.fluxConstant f ε - primitive (primitive f) 1) * a.reciprocal (x / ε) := by
  rw [(a.hasDerivAt_solution hf ε x).deriv,
    (a.hasDerivAt_homogenizedSolution hf x).deriv, (a.hasDerivAt_corrector (x / ε)).deriv]
  have hm := a.meanReciprocal_pos.ne'
  dsimp [effective]
  field_simp
  ring

/-- The corrected gradients converge uniformly with order-`|ε|` error. -/
theorem exists_gradient_corrector_error_bound {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
      ∀ x ∈ Icc (0 : ℝ) 1,
        |deriv (a.solution f ε) x -
          (1 + deriv a.corrector (x / ε)) * deriv (a.homogenizedSolution f) x| ≤
            C * |ε| := by
  obtain ⟨K, hK, hb⟩ := exists_fluctuation_bound a.continuous_reciprocal a.periodic_reciprocal
  obtain ⟨M, hM, hfM⟩ := (isCompact_Icc.image hf).isBounded.exists_pos_norm_le
  obtain ⟨Q, hQ, hq⟩ := (a.periodic_reciprocal.isBounded_of_continuous
    one_ne_zero a.continuous_reciprocal).exists_pos_norm_le
  have hfb : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M := fun y hy ↦ by
    simpa only [Real.norm_eq_abs] using hfM (f y) (mem_image_of_mem f hy)
  have hqb (y : ℝ) : |a.reciprocal y| ≤ Q := by
    simpa only [Real.norm_eq_abs] using hq _ (mem_range_self y)
  refine ⟨6 * M * K / a.meanReciprocal * Q, by
    exact mul_pos (div_pos (by positivity) a.meanReciprocal_pos) hQ,
    a.meanReciprocal / (2 * K), div_pos a.meanReciprocal_pos (by positivity), ?_⟩
  intro ε hε hsmall x _
  have hs : |ε| * K ≤ a.meanReciprocal / 2 := by
    have := (le_div_iff₀ (show 0 < 2 * K by positivity)).mp hsmall
    nlinarith
  have hm := a.meanReciprocal_pos
  rw [a.gradient_corrector_error hf, abs_mul]
  calc
    |a.fluxConstant f ε - primitive (primitive f) 1| * |a.reciprocal (x / ε)| ≤
        (6 * M * (|ε| * K) / a.meanReciprocal) * Q :=
      mul_le_mul (a.fluxConstant_error_le hf hK.le hM.le hb hfb hε hs)
        (hqb _) (abs_nonneg _) (by positivity)
    _ = (6 * M * K / a.meanReciprocal * Q) * |ε| := by cas

end PDE.Elliptic.Homogenization.PeriodicMedium
