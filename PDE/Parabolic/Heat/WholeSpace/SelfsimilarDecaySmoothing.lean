/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarDecay
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarSmoothing
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Self-similar smoothing with free decay

Short-time heat smoothing and the semigroup law combine the square-root
singularity at zero with the exact free decay at large similarity times.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The physical heat time controls the similarity-time square-root singularity. -/
theorem gainBound_selfsimilarHeatTime_le (τ : ℝ≥0) (hτ : 0 < τ) :
    gainBound (selfsimilarHeatTime τ) ≤ 1 + (Real.sqrt (τ : ℝ))⁻¹ := by
  have ht : (τ : ℝ) ≤ selfsimilarHeatTime τ := by
    rw [coe_selfsimilarHeatTime]
    linarith [Real.add_one_le_exp (τ : ℝ)]
  have hpi : 1 ≤ 8 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have htime : (τ : ℝ) ≤ 8 * Real.pi ^ 2 * (selfsimilarHeatTime τ : ℝ) :=
    ht.trans (le_mul_of_one_le_left (selfsimilarHeatTime τ).property hpi)
  unfold gainBound
  apply add_le_add le_rfl
  simpa only [one_div] using one_div_le_one_div_of_le
    (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ)) (Real.sqrt_le_sqrt htime)

/-- The explicit smoothing constant for similarity times at most one. -/
def selfsimilarShortGainConstant (n k : ℕ) : ℝ :=
  graphGainConstant n k * Real.exp (((k + 1 : ℕ) : ℝ) / 2)

theorem selfsimilarShortGainConstant_nonneg (n k : ℕ) :
    0 ≤ selfsimilarShortGainConstant n k :=
  mul_nonneg (graphGainConstant_nonneg n k) (Real.exp_pos _).le

/-- Short-time smoothing retains the exact free exponential factor. -/
theorem norm_selfsimilarHeatGain_le_of_le_one (τ : ℝ≥0) (hτ : 0 < τ)
    (hτ₁ : τ ≤ 1) (u : W^{k,2}(ℝ^n)) :
    ‖selfsimilarHeatGain n k τ hτ u‖ ≤
      selfsimilarShortGainConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) *
        (1 + (Real.sqrt (τ : ℝ))⁻¹) * ‖u‖ := by
  have hg : 0 ≤ graphGainConstant n k := graphGainConstant_nonneg n k
  have hb : 0 ≤ gainBound (selfsimilarHeatTime τ) := gainBound_nonneg _
  have ha : selfsimilarFactor τ ^ (k + 1) ≤ Real.exp (((k + 1 : ℕ) : ℝ) / 2) := by
    rw [selfsimilarFactor_pow]
    apply Real.exp_le_exp.mpr
    have hτ' : (τ : ℝ) ≤ 1 := hτ₁
    have hk : (0 : ℝ) ≤ k + 1 := by positivity
    push_cast
    nlinarith
  calc
    _ ≤ selfsimilarFactor τ *
        (selfsimilarFactor τ ^ (k + 1) * |(selfsimilarFactor τ ^ n)⁻¹| ^
          (1 / (2 : ℝ≥0∞)).toReal) *
        (graphGainConstant n k * gainBound (selfsimilarHeatTime τ)) * ‖u‖ :=
      norm_selfsimilarHeatGain_le τ hτ u
    _ = graphGainConstant n k * selfsimilarFactor τ ^ (k + 1) *
        Real.exp (((2 : ℝ) - n) * τ / 4) *
        gainBound (selfsimilarHeatTime τ) * ‖u‖ := by
      rw [← selfsimilar_volume_factor]
      ring
    _ ≤ graphGainConstant n k * Real.exp (((k + 1 : ℕ) : ℝ) / 2) *
        Real.exp (((2 : ℝ) - n) * τ / 4) *
        (1 + (Real.sqrt (τ : ℝ))⁻¹) * ‖u‖ := by
      gcongr
      exact gainBound_selfsimilarHeatTime_le τ hτ
    _ = _ := rfl

/-- A constant valid for the singular short-time and decaying long-time estimates. -/
def selfsimilarSmoothingConstant (n k : ℕ) : ℝ :=
  max (selfsimilarShortGainConstant n k)
    (2 * selfsimilarGraphConstant n (k + 1) * selfsimilarShortGainConstant n k)

theorem selfsimilarSmoothingConstant_nonneg (n k : ℕ) :
    0 ≤ selfsimilarSmoothingConstant n k :=
  (selfsimilarShortGainConstant_nonneg n k).trans (le_max_left _ _)

/-- One-derivative smoothing has the same free decay as the order-preserving semigroup. -/
theorem norm_selfsimilarHeatGain_le_exp (τ : ℝ≥0) (hτ : 0 < τ)
    (u : W^{k,2}(ℝ^n)) :
    ‖selfsimilarHeatGain n k τ hτ u‖ ≤
      selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) *
        (1 + (Real.sqrt (τ : ℝ))⁻¹) * ‖u‖ := by
  have hshort : 0 ≤ selfsimilarShortGainConstant n k :=
    selfsimilarShortGainConstant_nonneg n k
  have hgraph : 0 ≤ selfsimilarGraphConstant n (k + 1) :=
    selfsimilarGraphConstant_nonneg n (k + 1)
  rcases le_total τ 1 with hτ₁ | h₁τ
  · apply (norm_selfsimilarHeatGain_le_of_le_one τ hτ hτ₁ u).trans
    gcongr
    exact le_max_left _ _
  · let s : ℝ≥0 := τ - 1
    have hs : s + 1 = τ := tsub_add_cancel_of_le h₁τ
    have hG := norm_selfsimilarHeatGain_le_of_le_one
      (n := n) (k := k) 1 (by norm_num) le_rfl u
    norm_num only [NNReal.coe_one, Real.sqrt_one, inv_one] at hG
    have hS := norm_selfsimilarHeatSobolev_le s
      (selfsimilarHeatGain n k 1 (by norm_num) u)
    have hcomp : selfsimilarHeatGain n k τ hτ u =
        selfsimilarHeatSobolev n (k + 1) s
          (selfsimilarHeatGain n k 1 (by norm_num) u) := by
      simpa only [hs] using selfsimilarHeatGain_add s 1 (by norm_num) u
    have hexp : Real.exp (((2 : ℝ) - n) * s / 4) *
        Real.exp (((2 : ℝ) - n) * 1 / 4) =
          Real.exp (((2 : ℝ) - n) * τ / 4) := by
      rw [← Real.exp_add]
      congr 1
      have hs' : (s : ℝ) + 1 = τ := by exact_mod_cast hs
      rw [← hs']
      ring
    calc
      _ ≤ selfsimilarGraphConstant n (k + 1) *
          Real.exp (((2 : ℝ) - n) * s / 4) *
          ‖selfsimilarHeatGain n k 1 (by norm_num) u‖ := by
        rw [hcomp]
        exact hS
      _ ≤ selfsimilarGraphConstant n (k + 1) *
          Real.exp (((2 : ℝ) - n) * s / 4) *
          (selfsimilarShortGainConstant n k * Real.exp (((2 : ℝ) - n) * 1 / 4) *
            2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hgraph (Real.exp_pos _).le)
      _ = (2 * selfsimilarGraphConstant n (k + 1) * selfsimilarShortGainConstant n k) *
          Real.exp (((2 : ℝ) - n) * τ / 4) * ‖u‖ := by
        rw [← hexp]
        ring
      _ ≤ selfsimilarSmoothingConstant n k *
          Real.exp (((2 : ℝ) - n) * τ / 4) * ‖u‖ := by
        gcongr
        exact le_max_right _ _
      _ ≤ selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * τ / 4) *
          (1 + (Real.sqrt (τ : ℝ))⁻¹) * ‖u‖ := by
        have hC := selfsimilarSmoothingConstant_nonneg n k
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (mul_nonneg hC (Real.exp_pos _).le)
            (le_add_of_nonneg_right (by positivity))) (norm_nonneg u)

end HeatEquation.WholeSpace
