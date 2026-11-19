/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Estimates
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution
import CAS.ExactTactic

/-!
# Identifying characteristic segments with d'Alembert's formula

The changes of variables are valid for the integrals, without
assuming differentiability of the source. This connects the cone construction
to the one-dimensional C² Duhamel theorem for C¹ forcing.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The zero-displacement free wave is a normalized segment average. -/
theorem dAlembertFormula_zero_eq_segment (h : ℝ → ℝ) (r t : ℝ) :
    dAlembertFormula (fun _ ↦ 0) h r t = t * ∫ b : I, h (r + t * (2 * (b : ℝ) - 1)) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_add h (2 * t) (r - t) (a := 0) (b := 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at hscale
  have hend : 2 * t + (r - t) = r + t := by cas
  rw [hend] at hscale
  have he (b : ℝ) : 2 * t * b + (r - t) = r + t * (2 * b - 1) := by cas
  simp_rw [he] at hscale
  rw [integral_unitInterval (fun b ↦ h (r + t * (2 * b - 1)))]
  simp only [dAlembertFormula, add_zero, mul_zero, zero_add]
  rw [← hscale]
  cas

/-- Duhamel's one-dimensional solution is the normalized double segment integral. -/
theorem dAlembertDuhamelSolution_eq_segment (F : ℝ^2 → ℝ) {p : ℝ^2} (hp : 0 ≤ p 0) :
    dAlembertDuhamelSolution F p = (p 0) ^ 2 * ∫ s : I, (1 - (s : ℝ)) * ∫ b : I,
      F (timeSpaceCons ((p 0) * (s : ℝ)) (EuclideanSpace.single (0 : Fin 1)
      (p 1 + (p 0) * ((1 - (s : ℝ)) * (2 * (b : ℝ) - 1))))) := by
  rw [dAlembertDuhamelSolution_eq_doubleIntegral]
  let g : ℝ → ℝ := fun s ↦ dAlembertFormula (fun _ ↦ 0)
    (fun y ↦ F (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))) (p 1) (p 0 - s)
  have hscale : (p 0) * (∫ s in (0 : ℝ)..1, g ((p 0) * s)) =
      ∫ s in (0 : ℝ)..p 0, g s := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left g (p 0) (a := 0) (b := 1)
  change (∫ s in (0 : ℝ)..p 0, g s) = _
  rw [← hscale, ← integral_unitInterval]
  simp only [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  have hs : 0 ≤ (p 0) * (s : ℝ) := mul_nonneg hp s.2.1
  dsimp only [g]
  rw [dAlembertFormula_zero_eq_segment, max_eq_right hs]
  have he : p 0 - p 0 * (s : ℝ) = p 0 * (1 - (s : ℝ)) := by cas
  rw [he]
  simp only [integral_const_mul, mul_assoc]
  cas

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
