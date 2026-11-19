/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import CAS.IntegrationTactic

/-!
# Localizing primitives while preserving critical points

Multiplying a derivative by a smooth cutoff and then integrating produces a
smooth zero-preserving primitive of bounded slope. On the inner interval it
equals the original potential minus its value at zero, and every critical
point of the original potential remains critical. Cutting off the potential
itself would introduce an unwanted derivative of the cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff

namespace PDE.Analysis

/-- Localize an actual smooth derivative, preserving its zeros and the primitive
on a prescribed interval. The construction uses a smooth cutoff of the derivative,
followed by its actual interval integral. -/
theorem exists_localized_primitive
    {G g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hd : ∀ s, HasDerivAt G (g s) s) {R : ℝ} (hR : 0 < R) :
    ∃ (F F' : ℝ → ℝ) (M : ℝ), 0 < M ∧
      ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ F' ∧
      (∀ s, HasDerivAt F (F' s) s) ∧ F 0 = 0 ∧
      (∀ s, |F' s| ≤ M) ∧ (∀ s, g s = 0 → F' s = 0) ∧
      (∀ s, |s| ≤ R → F s = G s - G 0) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩
  let F' : ℝ → ℝ := fun s ↦ χ s * g s
  let F : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..s, F' t
  have hF' : ContDiff ℝ ∞ F' := χ.contDiff.mul hg
  have hdF (s : ℝ) : HasDerivAt F (F' s) s := by
    dsimp only [F]
    cas
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun s ↦ (hdF s).differentiableAt, ?_⟩
    have heq : deriv F = F' := funext fun s ↦ (hdF s).deriv
    rw [heq]
    exact hF'
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℝ) (R + 1)).image
    hg.continuous).isBounded.exists_norm_le
  refine ⟨F, F', max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    hF, hF', hdF, by simp [F], ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ closedBall (0 : ℝ) (R + 1)
    · have hgs : |g s| ≤ B := hB _ ⟨s, hs, rfl⟩
      have hχ : |χ s| ≤ 1 := by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one
      calc
        |F' s| = |χ s| * |g s| := abs_mul _ _
        _ ≤ 1 * |g s| := mul_le_mul_of_nonneg_right hχ (abs_nonneg _)
        _ ≤ max 1 B := by simpa using hgs.trans (le_max_right _ _)
    · have hzero : χ s = 0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hs))
      simp [F', hzero]
  · intro s hs
    simp [F', hs]
  · intro s hs
    have hinterval : ∀ t ∈ uIcc (0 : ℝ) s, χ t = 1 := by
      intro t ht
      apply χ.one_of_mem_closedBall
      have ht' : -R ≤ t ∧ t ≤ R := by
        rcases mem_uIcc.mp ht with ht | ht
        · constructor <;> linarith [abs_le.mp hs]
        · constructor <;> linarith [abs_le.mp hs]
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, χ] using abs_le.mpr ht'
    calc
      F s = ∫ t in (0 : ℝ)..s, g t := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [F', hinterval t ht, one_mul]
      _ = G s - G 0 := by cas

end PDE.Analysis
