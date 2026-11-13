/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform bounds for expanding cutoffs

The same smooth bump is used at every radius. Expanding its support cannot
increase its Lipschitz constant, and every fixed point eventually lies in the
region where the cutoff is exactly one, so integrals against expanding cutoffs
converge to the integral.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped NNReal Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- All cutoffs with radius at least one share a Lipschitz constant. -/
theorem exists_lipschitzWith_cutoff :
    ∃ L : ℝ≥0, ∀ R : ℝ, 1 ≤ R → LipschitzWith L (cutoff (n := n) R) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (PDE.Analysis.standardBump n).hasCompactSupport
    (show ContDiff ℝ (⊤ : ℕ∞) (PDE.Analysis.standardBump n) from
      (PDE.Analysis.standardBump n).contDiff) (by simp)
  refine ⟨L, fun R hR ↦ LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  calc
    dist (cutoff R x) (cutoff R y) ≤ (L : ℝ) * dist (R⁻¹ • x) (R⁻¹ • y) :=
      hL.dist_le_mul _ _
    _ ≤ (L : ℝ) * dist x y := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR0), ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (dist_nonneg : 0 ≤ dist x y) hinv) L.2

/-- A fixed point eventually lies in the plateau of an expanding cutoff. -/
theorem eventually_cutoff_eq_one {ι : Type*} {l : Filter ι} {R : ι → ℝ}
    (hR : Tendsto R l atTop) (x : ℝ^n) :
    ∀ᶠ i in l, cutoff (R i) x = 1 := by
  filter_upwards [hR.eventually (eventually_ge_atTop (max 1 ‖x‖))] with i hi
  apply cutoff_eq_one_of_mem_closedBall
    (zero_lt_one.trans_le ((le_max_left _ _).trans hi))
  simpa only [Metric.mem_closedBall, dist_zero_right] using (le_max_right _ _).trans hi

/-- A positive-radius cutoff vanishes outside the closed ball of twice its radius. -/
theorem cutoff_eq_zero_of_notMem_closedBall {R : ℝ} (hR : 0 < R) {x : ℝ^n}
    (hx : x ∉ Metric.closedBall (0 : ℝ^n) (2 * R)) : cutoff R x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_cutoff_subset_closedBall hR h)

/-- Integrals against the expanding cutoffs `χ_{k+1}` converge to the integral. -/
theorem tendsto_integral_mul_cutoff {f : ℝ^n → ℝ} (hf : Integrable f) :
    Tendsto (fun k : ℕ ↦ ∫ x, f x * cutoff ((k : ℝ) + 1) x) atTop (𝓝 (∫ x, f x)) := by
  have hR : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    (fun k ↦ hf.aestronglyMeasurable.mul (cutoff_contDiff _).continuous.aestronglyMeasurable)
    hf.norm (fun k ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa [Real.norm_eq_abs] using cutoff_abs_le_one ((k : ℝ) + 1) x)
  · exact tendsto_const_nhds.congr'
      ((eventually_cutoff_eq_one hR x).mono fun k hk ↦ by simp only [hk, mul_one])

end SobolevSpace.Approximation
