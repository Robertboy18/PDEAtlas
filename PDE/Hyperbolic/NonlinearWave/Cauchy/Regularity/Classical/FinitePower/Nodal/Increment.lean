/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import CAS.ExactTactic

/-!
# Symmetric increments at nodal values

Normalized symmetric increments of signed powers detect a transverse zero. The zero-derivative
case has vanishing normalized increment.
-/

@[expose] public noncomputable section

section

open Set Filter
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- At a simple or degenerate zero, a Hölder power has the scaled limit dictated
by the ordinary first derivative. -/
theorem tendsto_abs_rpow_div_of_zero {u : ℝ → ℝ} {a α : ℝ}
    (hu : HasDerivAt u a 0) (hu₀ : u 0 = 0) (hα : 0 ≤ α) :
    Tendsto (fun h : ℝ ↦ |u h| ^ α / h ^ α) (𝓝[>] 0) (𝓝 (|a| ^ α)) := by
  have hq : Tendsto (fun h : ℝ ↦ u h / h) (𝓝[>] 0) (𝓝 a) := by
    simpa only [zero_add, hu₀, sub_zero, smul_eq_mul, div_eq_inv_mul] using
      hu.tendsto_slope_zero_right
  have habs : Tendsto (fun h : ℝ ↦ |u h| / h) (𝓝[>] 0) (𝓝 |a|) := by
    apply hq.abs.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [abs_div, abs_of_pos hh]
  apply ((Real.continuous_rpow_const hα).tendsto |a| |>.comp habs).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh using Real.div_rpow (abs_nonneg _) hh.le α

/-- Symmetric increments of a differentiable function vanish after any scaling
between linear and a strictly positive Hölder power. -/
theorem tendsto_symmetric_increment_div_rpow {d : ℝ → ℝ} {a α : ℝ}
    (hd : HasDerivAt d a 0) (hα : α ≤ 1) :
    Tendsto (fun h : ℝ ↦ (d h + d (-h) - 2 * d 0) / (2 * h ^ α)) (𝓝[>] 0) (𝓝 0) := by
  have hm : HasDerivAt (fun h : ℝ ↦ d (-h)) (-a) 0 := by
    have hc := hd.comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    rw [mul_neg_one] at hc
    convert hc using 1
    all_goals (funext h; rfl)
  have hp : Tendsto (fun h : ℝ ↦ (d h - d 0) / h) (𝓝[>] 0) (𝓝 a) := by
    simpa only [zero_add, smul_eq_mul, div_eq_inv_mul] using hd.tendsto_slope_zero_right
  have hn : Tendsto (fun h : ℝ ↦ (d (-h) - d 0) / h) (𝓝[>] 0) (𝓝 (-a)) := by
    simpa only [zero_add, neg_zero, smul_eq_mul, div_eq_inv_mul] using hm.tendsto_slope_zero_right
  have hs : Tendsto (fun h : ℝ ↦ (((d h - d 0) / h + (d (-h) - d 0) / h) / 2) * h ^ (1 - α))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_neg_cancel, zero_div, zero_mul] using ((hp.add hn).div_const 2).mul
        ((Real.continuous_rpow_const (sub_nonneg.mpr hα)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [Real.rpow_sub hh, Real.rpow_one]
  cas using hh.ne' (Real.rpow_pos_of_pos hh α).ne'

/-- The scaled symmetric increment of the signed-power derivative coefficient
is supported exactly on zeros of the underlying curve. -/
theorem tendsto_symmetric_abs_rpow_mul_increment {u v : ℝ → ℝ} {a α : ℝ} (hu : HasDerivAt u a 0)
    (hv : DifferentiableAt ℝ v 0) (hα : 0 < α) (hα₁ : α ≤ 1) :
    Tendsto (fun h : ℝ ↦ (|u h| ^ α * v h + |u (-h)| ^ α * v (-h) - 2 * |u 0| ^ α * v 0) /
      (2 * h ^ α)) (𝓝[>] 0) (𝓝 (if u 0 = 0 then |a| ^ α * v 0 else 0)) := by
  by_cases hu₀ : u 0 = 0
  · rw [ite_eq_left hu₀]
    have hm : HasDerivAt (fun h : ℝ ↦ u (-h)) (-a) 0 := by
      have hc := hu.comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
      rw [mul_neg_one] at hc
      convert hc using 1
      all_goals (funext h; rfl)
    have hp := (tendsto_abs_rpow_div_of_zero hu hu₀ hα.le).mul
      (hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have hn := (tendsto_abs_rpow_div_of_zero hm (by simpa using hu₀) hα.le).mul
      ((hv.continuousAt.comp_of_eq
        (by fun_prop : ContinuousAt (fun h : ℝ ↦ -h) 0) (by simp)).tendsto
        |>.mono_left nhdsWithin_le_nhds)
    have hs : Tendsto (fun h : ℝ ↦ (|u h| ^ α / h ^ α * v h + |u (-h)| ^ α / h ^ α * v (-h)) / 2)
        (𝓝[>] 0) (𝓝 (|a| ^ α * v 0)) := by
      have he : (|a| ^ α * v 0 + |-a| ^ α * v (-0)) / 2 = |a| ^ α * v 0 := by
        rw [abs_neg, neg_zero]
        cas
      simpa only [Function.comp_def, he] using (hp.add hn).div_const 2
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hu₀, abs_zero, Real.zero_rpow hα.ne']
    cas using (Real.rpow_pos_of_pos hh α).ne'
  · rw [ite_eq_right hu₀]
    have hd : DifferentiableAt ℝ (fun h : ℝ ↦ |u h| ^ α * v h) 0 :=
      ((hu.differentiableAt.abs hu₀).rpow_const (Or.inl (abs_ne_zero.mpr hu₀))).mul hv
    simpa only [mul_assoc] using tendsto_symmetric_increment_div_rpow hd.hasDerivAt hα₁

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter BoundedContinuousFunction
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- At a zero, continuity of the velocity suffices for the nodal limit. -/
theorem tendsto_symmetric_abs_rpow_mul_increment_of_zero {u v : ℝ → ℝ} {a α : ℝ}
    (hu : HasDerivAt u a 0) (hv : ContinuousAt v 0) (hu₀ : u 0 = 0) (hα : 0 < α) :
    Tendsto (fun h : ℝ ↦ (|u h| ^ α * v h + |u (-h)| ^ α * v (-h) - 2 * |u 0| ^ α * v 0) /
      (2 * h ^ α)) (𝓝[>] 0) (𝓝 (|a| ^ α * v 0)) := by
  have hm : HasDerivAt (fun h : ℝ ↦ u (-h)) (-a) 0 := by
    have hc := hu.comp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    rw [mul_neg_one] at hc
    convert hc using 1
    all_goals (funext h; rfl)
  have hp := (tendsto_abs_rpow_div_of_zero hu hu₀ hα.le).mul
    (hv.tendsto.mono_left nhdsWithin_le_nhds)
  have hn := (tendsto_abs_rpow_div_of_zero hm (by simpa using hu₀) hα.le).mul ((hv.comp_of_eq
      (by fun_prop : ContinuousAt (fun h : ℝ ↦ -h) 0) (by simp)).tendsto
      |>.mono_left nhdsWithin_le_nhds)
  have hs : Tendsto (fun h : ℝ ↦ (|u h| ^ α / h ^ α * v h + |u (-h)| ^ α / h ^ α * v (-h)) / 2)
      (𝓝[>] 0) (𝓝 (|a| ^ α * v 0)) := by
    have he : (|a| ^ α * v 0 + |-a| ^ α * v (-0)) / 2 = |a| ^ α * v 0 := by
      rw [abs_neg, neg_zero]
      cas
    simpa only [Function.comp_def, he] using (hp.add hn).div_const 2
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [hu₀, abs_zero, Real.zero_rpow hα.ne']
  cas using (Real.rpow_pos_of_pos hh α).ne'

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
