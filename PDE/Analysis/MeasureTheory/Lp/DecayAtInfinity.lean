/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Decay at infinity of uniformly continuous `Lᵖ` functions

On a finite-dimensional real normed space with an additive Haar measure, a uniformly continuous
function in `Lᵖ` with `0 < p < ∞` tends to zero at infinity. If `‖f x‖ ≥ ε` at a point far
away, uniform continuity gives `‖f‖ ≥ ε / 2` on a ball of fixed radius around it, whose
measure does not depend on the center; this contradicts the approximation of `f` in `Lᵖ` by a
compactly supported continuous function. In particular a differentiable function in `Lᵖ` with
bounded derivative tends to zero at infinity.
-/

@[expose] public section

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {p : ℝ≥0∞}

/-- A uniformly continuous function in `Lᵖ`, `0 < p < ∞`, on a finite-dimensional real normed
space with an additive Haar measure tends to zero at infinity. -/
theorem MemLp.tendsto_cocompact_zero_of_uniformContinuous (hf : MemLp f p μ) (hp₀ : p ≠ 0)
    (hp : p ≠ ∞) (hu : UniformContinuous f) : Tendsto f (cocompact E) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (half_pos hε)
  set q := p.toReal
  have hq : 0 < q := ENNReal.toReal_pos hp₀ hp
  set c : ℝ≥0∞ := ENNReal.ofReal (ε / 2) ^ q * μ (ball 0 δ)
  have hc₀ : c ≠ 0 := mul_ne_zero
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (half_pos hε)) ENNReal.ofReal_ne_top).ne'
    (measure_ball_pos μ 0 hδ).ne'
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
    measure_ball_lt_top.ne
  have hη : (c / 2) ^ q⁻¹ ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.half_pos hc₀) (ENNReal.div_ne_top hc two_ne_zero)).ne'
  obtain ⟨g, hg, hfg, -, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hη
  filter_upwards [(hg.isCompact.cthickening (r := δ)).compl_mem_cocompact] with x hx
  rw [dist_zero_right]
  by_contra hfx
  rw [not_lt] at hfx
  have hball : ball x δ ⊆ {y | ENNReal.ofReal (ε / 2) ≤ ‖(f - g) y‖ₑ} := by
    intro y hy
    have hgy : g y = 0 := image_eq_zero_of_notMem_tsupport fun hyg ↦
      hx (mem_cthickening_of_dist_le x y δ _ hyg (dist_comm x y ▸ (mem_ball.mp hy).le))
    have hxy := hfδ (mem_ball'.mp hy)
    rw [dist_eq_norm] at hxy
    have : ε / 2 ≤ ‖f y‖ := by
      have := norm_sub_norm_le (f x) (f y)
      linarith
    change ENNReal.ofReal (ε / 2) ≤ ‖f y - g y‖ₑ
    rw [hgy, sub_zero, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal this
  have hle : c ≤ eLpNorm (f - g) p μ ^ q := by
    calc c = ENNReal.ofReal (ε / 2) ^ q * μ (ball x δ) := by rw [Measure.addHaar_ball_center]
      _ ≤ ENNReal.ofReal (ε / 2) ^ q * μ {y | ENNReal.ofReal (ε / 2) ≤ ‖(f - g) y‖ₑ} := by
        gcongr
      _ ≤ eLpNorm (f - g) p μ ^ q := mul_meas_ge_le_pow_eLpNorm' μ hp₀ hp _
  have hlt : eLpNorm (f - g) p μ ^ q < c :=
    calc eLpNorm (f - g) p μ ^ q ≤ ((c / 2) ^ q⁻¹) ^ q := ENNReal.rpow_le_rpow hfg hq.le
      _ = c / 2 := ENNReal.rpow_inv_rpow hq.ne' _
      _ < c := ENNReal.half_lt_self hc₀ hc
  exact (hle.trans_lt hlt).false

/-- A differentiable function in `Lᵖ`, `0 < p < ∞`, on a finite-dimensional real normed space
with an additive Haar measure, whose derivative is bounded, tends to zero at infinity. -/
theorem MemLp.tendsto_cocompact_zero_of_norm_fderiv_le (hf : MemLp f p μ) (hp₀ : p ≠ 0)
    (hp : p ≠ ∞) (hd : Differentiable ℝ f) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) :
    Tendsto f (cocompact E) (𝓝 0) :=
  hf.tendsto_cocompact_zero_of_uniformContinuous hp₀ hp
    (lipschitzWith_of_nnnorm_fderiv_le (C := ⟨max C 0, le_max_right C 0⟩) hd fun x ↦
      NNReal.coe_le_coe.mp ((hC x).trans (le_max_left C 0))).uniformContinuous

end MeasureTheory
