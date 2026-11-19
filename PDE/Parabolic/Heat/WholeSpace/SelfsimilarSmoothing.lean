/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Selfsimilar

/-!
# One-order smoothing for the actual free self-similar evolution

The physical formula combines the verified heat gain with actual graph
dilation. The explicit bound below retains the factors from the graph change of
variables; it does not claim a sharp long-time spectral estimate.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev Topology

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Strictly positive similarity time corresponds to strictly positive heat time. -/
theorem selfsimilarHeatTime_pos {τ : ℝ≥0} (hτ : 0 < τ) :
    0 < (selfsimilarHeatTime τ : ℝ) := by
  rw [coe_selfsimilarHeatTime]
  exact sub_pos.2 (Real.one_lt_exp_iff.2 (NNReal.coe_pos.2 hτ))

/-- The actual free self-similar evolution gains one weak derivative at positive time. -/
def selfsimilarHeatGain (n k : ℕ) (τ : ℝ≥0) (hτ : 0 < τ) :
    W^{k,2}(ℝ^n) →L[ℝ] W^{k + 1,2}(ℝ^n) :=
  selfsimilarFactor τ •
    (dilationWkpCLM (by norm_num) (selfsimilarFactor τ)
      (selfsimilarFactor_pos τ).ne').comp
        (heatGainSobolev n k (selfsimilarHeatTime τ) (selfsimilarHeatTime_pos hτ))

theorem selfsimilarHeatGain_apply (τ : ℝ≥0) (hτ : 0 < τ) (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatGain n k τ hτ u = selfsimilarFactor τ •
      dilationWkpCLM (by norm_num) (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne'
        (heatGainSobolev n k (selfsimilarHeatTime τ) (selfsimilarHeatTime_pos hτ) u) := rfl

/-- The gaining operator describes the same literal physical evolution as the semigroup. -/
theorem baseL2_selfsimilarHeatGain (τ : ℝ≥0) (hτ : 0 < τ) (u : W^{k,2}(ℝ^n)) :
    baseL2 (selfsimilarHeatGain n k τ hτ u) = selfsimilarFactor τ •
      Lp.compSMul volume 2 (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne'
        (heatL2 n (selfsimilarHeatTime τ) (baseL2 u)) := by
  rw [selfsimilarHeatGain_apply, baseL2_smul, baseL2_dilationWkpCLM,
    baseL2_heatGainSobolev]

/-- Forgetting the extra derivative recovers the same physical semigroup orbit. -/
theorem baseL2_selfsimilarHeatGain_eq (τ : ℝ≥0) (hτ : 0 < τ) (u : W^{k,2}(ℝ^n)) :
    baseL2 (selfsimilarHeatGain n k τ hτ u) =
      baseL2 (selfsimilarHeatSobolev n k τ u) := by
  rw [baseL2_selfsimilarHeatGain, baseL2_selfsimilarHeatSobolev]

/-- After gaining a derivative, subsequent evolution acts in the stronger graph space. -/
theorem selfsimilarHeatGain_add (s t : ℝ≥0) (ht : 0 < t) (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatGain n k (s + t) (add_pos_of_nonneg_of_pos bot_le ht) u =
      selfsimilarHeatSobolev n (k + 1) s (selfsimilarHeatGain n k t ht u) := by
  apply baseL2_injective
  rw [baseL2_selfsimilarHeatGain_eq, selfsimilarHeatSobolev_add]
  simp only [baseL2_selfsimilarHeatSobolev, baseL2_selfsimilarHeatGain]

/-- A positive final evolution step gains a derivative after any nonnegative initial step. -/
theorem selfsimilarHeatGain_add_of_pos_left (s t : ℝ≥0) (hs : 0 < s)
    (u : W^{k,2}(ℝ^n)) :
    selfsimilarHeatGain n k (s + t) (add_pos_of_pos_of_nonneg hs bot_le) u =
      selfsimilarHeatGain n k s hs (selfsimilarHeatSobolev n k t u) := by
  apply baseL2_injective
  rw [baseL2_selfsimilarHeatGain_eq, baseL2_selfsimilarHeatGain_eq,
    selfsimilarHeatSobolev_add]

/-- A directly derived graph norm bound for self-similar one-order smoothing. -/
theorem norm_selfsimilarHeatGain_le (τ : ℝ≥0) (hτ : 0 < τ) (u : W^{k,2}(ℝ^n)) :
    ‖selfsimilarHeatGain n k τ hτ u‖ ≤
      selfsimilarFactor τ *
        (selfsimilarFactor τ ^ (k + 1) * |(selfsimilarFactor τ ^ n)⁻¹| ^
          (1 / (2 : ℝ≥0∞)).toReal) *
        (graphGainConstant n k * gainBound (selfsimilarHeatTime τ)) * ‖u‖ := by
  rw [selfsimilarHeatGain_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (selfsimilarFactor_pos τ)]
  calc
    _ ≤ selfsimilarFactor τ *
        (selfsimilarFactor τ ^ (k + 1) * |(selfsimilarFactor τ ^ n)⁻¹| ^
          (1 / (2 : ℝ≥0∞)).toReal *
          ‖heatGainSobolev n k (selfsimilarHeatTime τ) (selfsimilarHeatTime_pos hτ) u‖) :=
      mul_le_mul_of_nonneg_left
        (norm_dilationWkpCLM_le_of_one_le (by norm_num) (one_le_selfsimilarFactor τ) _)
        (selfsimilarFactor_pos τ).le
    _ ≤ selfsimilarFactor τ *
        (selfsimilarFactor τ ^ (k + 1) * |(selfsimilarFactor τ ^ n)⁻¹| ^
          (1 / (2 : ℝ≥0∞)).toReal *
          (graphGainConstant n k * gainBound (selfsimilarHeatTime τ) * ‖u‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_heatGainSobolev_le (selfsimilarHeatTime_pos hτ) u)
          (mul_nonneg (pow_nonneg (selfsimilarFactor_pos τ).le _)
            (Real.rpow_nonneg (abs_nonneg _) _))) (selfsimilarFactor_pos τ).le
    _ = _ := by ring

end HeatEquation.WholeSpace
