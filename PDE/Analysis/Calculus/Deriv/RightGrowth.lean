/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Linear growth detected by a right composition germ

A scalar local inverse with positive derivative preserves the right side of zero.
A differentiable right germ of the composition therefore detects a right-sided
linear bound on the outer function. Clipping at zero makes that bound two-sided.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

/-- Inverting a scalar path with positive derivative transports a differentiable
right germ of the composition to a right-sided linear growth bound. -/
theorem isBigO_right_of_comp_of_deriv_pos
    {f g : ℝ → ℝ} (hg : ContDiffAt ℝ 1 g 0) (hgzero : g 0 = 0)
    (hgpos : 0 < deriv g 0) (hfzero : f 0 = 0)
    (hfg : DifferentiableWithinAt ℝ (f ∘ g) (Ici 0) 0) :
    f =O[𝓝[≥] 0] (fun z : ℝ ↦ z) := by
  have hs := hg.hasStrictDerivAt (by norm_num)
  let v := hs.localInverse g (deriv g 0) 0 (ne_of_gt hgpos)
  have hvzero : v 0 = 0 := by
    simpa only [hgzero] using
      (hs.hasStrictFDerivAt_equiv (ne_of_gt hgpos)).localInverse_apply_image
  have hv' : HasDerivAt v (deriv g 0)⁻¹ 0 := by
    simpa only [hgzero] using (hs.to_localInverse (ne_of_gt hgpos)).hasDerivAt
  have hvpos : ∀ᶠ z in 𝓝[>] (0 : ℝ), 0 < v z := by
    have hlim := hv'.tendsto_slope_zero_right
    have hlt := hlim.eventually (Ioi_mem_nhds (inv_pos.mpr hgpos))
    filter_upwards [hlt, eventually_mem_nhdsWithin] with z hz hzpos
    simp only [zero_add, hvzero, sub_zero, smul_eq_mul] at hz
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hzpos)).mp hz
  have hvnonneg : ∀ᶠ z in 𝓝[≥] (0 : ℝ), 0 ≤ v z := by
    rw [← nhdsGT_sup_nhdsWithin_singleton, eventually_sup]
    exact ⟨hvpos.mono fun _ hz ↦ hz.le, by simp [hvzero]⟩
  have hvt : Tendsto v (𝓝[≥] 0) (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa only [hvzero] using
        hv'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ici 0)), hvnonneg⟩
  have hfgO : (f ∘ g) =O[𝓝[≥] 0] (fun z : ℝ ↦ z) := by
    simpa only [Function.comp_def, hgzero, hfzero, sub_zero] using hfg.isBigO_sub
  have hvO : v =O[𝓝[≥] 0] (fun z : ℝ ↦ z) := by
    simpa only [hvzero, sub_zero] using
      hv'.differentiableAt.isBigO_sub.mono (nhdsWithin_le_nhds (s := Ici 0))
  have hright : ∀ᶠ z in 𝓝[≥] (0 : ℝ), g (v z) = z := by
    simpa only [hgzero] using
      (hs.eventually_right_inverse (ne_of_gt hgpos)).filter_mono nhdsWithin_le_nhds
  exact ((hfgO.comp_tendsto hvt).trans hvO).congr'
    (hright.mono fun z hz ↦ by simp only [Function.comp_apply, hz])
    (Eventually.of_forall fun _ ↦ rfl)

/-- A right-sided growth bound becomes two-sided after clipping the argument
at zero. No differentiability of the reaction is required. -/
theorem isBigO_max_zero_of_isBigO_right {f : ℝ → ℝ}
    (hf : f =O[𝓝[≥] 0] (fun z : ℝ ↦ z)) :
    (fun z ↦ f (max z 0)) =O[𝓝 0] (fun z : ℝ ↦ z) := by
  have hm : Tendsto (fun z : ℝ ↦ max z 0) (𝓝 0) (𝓝[≥] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using (continuous_id.max (continuous_const (y := (0 : ℝ)))).tendsto (0 : ℝ),
      Eventually.of_forall fun z ↦ le_max_right z 0⟩
  have hO : (fun z : ℝ ↦ max z 0) =O[𝓝 0] (fun z : ℝ ↦ z) := by
    apply Asymptotics.IsBigO.of_bound 1
    apply Eventually.of_forall
    intro z
    by_cases hz : 0 ≤ z
    · simp only [max_eq_left hz, one_mul, le_refl]
    · simp only [max_eq_right (le_of_not_ge hz), norm_zero, one_mul, norm_nonneg]
  exact (hf.comp_tendsto hm).trans hO

end PDE.Analysis
