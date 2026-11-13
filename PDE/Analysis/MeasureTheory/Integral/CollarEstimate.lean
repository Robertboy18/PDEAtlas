/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy--Schwarz for normalized collar integrals

A uniform normalized energy bound and a convergent normalized test energy
control the limit of a collar pairing. The hypotheses concern volume integrals
of L² fields; no boundary representative of the first field is required.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two L² representatives have an integrable pointwise real inner product. -/
theorem integrable_inner_of_memLp_two
    {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Cauchy--Schwarz in terms of the actual volume representatives. -/
theorem sq_integral_inner_le_integral_norm_sq_mul
    {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hi : inner ℝ F G = ∫ x, inner ℝ (f x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hF : ‖F‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    exact integral_congr_ae (hf.coeFn_toLp.fun_comp fun z ↦ ‖z‖ ^ 2)
  have hG : ‖G‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    exact integral_congr_ae (hg.coeFn_toLp.fun_comp fun z ↦ ‖z‖ ^ 2)
  rw [← hi, ← hF, ← hG]
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℝ F G))
    (norm_inner_le_norm F G) 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hcs

/-- Normalized collar energy and test-energy limits bound the limiting
pairing. Both inputs may vary with the positive collar thickness. -/
theorem sq_le_mul_of_tendsto_normalized_inner
    {ν : ℝ → Measure X} {F G : ℝ → X → E} {L B S : ℝ}
    (hF : ∀ᶠ t in 𝓝[>] (0 : ℝ), MemLp (F t) 2 (ν t))
    (hG : ∀ᶠ t in 𝓝[>] (0 : ℝ), MemLp (G t) 2 (ν t))
    (henergy : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * ∫ x, ‖F t x‖ ^ 2 ∂ν t ≤ B)
    (hpair : Tendsto (fun t : ℝ ↦ t⁻¹ * ∫ x, inner ℝ (F t x) (G t x) ∂ν t)
      (𝓝[>] 0) (𝓝 L))
    (htest : Tendsto (fun t : ℝ ↦ t⁻¹ * ∫ x, ‖G t x‖ ^ 2 ∂ν t)
      (𝓝[>] 0) (𝓝 S)) :
    L ^ 2 ≤ B * S := by
  apply le_of_tendsto_of_tendsto (hpair.pow 2) (htest.const_mul B)
  filter_upwards [self_mem_nhdsWithin, hF, hG, henergy] with t ht hf hg he
  have hcs := mul_le_mul_of_nonneg_left
    (sq_integral_inner_le_integral_norm_sq_mul hf hg) (sq_nonneg t⁻¹)
  have hs : (t⁻¹ * ∫ x, inner ℝ (F t x) (G t x) ∂ν t) ^ 2 ≤
      (t⁻¹ * ∫ x, ‖F t x‖ ^ 2 ∂ν t) * (t⁻¹ * ∫ x, ‖G t x‖ ^ 2 ∂ν t) := by
    nlinarith only [hcs]
  exact hs.trans (mul_le_mul_of_nonneg_right he
    (mul_nonneg (inv_nonneg.mpr ht.le) (integral_nonneg fun _ ↦ sq_nonneg _)))

end MeasureTheory
