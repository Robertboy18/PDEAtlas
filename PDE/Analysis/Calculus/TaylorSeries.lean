/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Taylor series from factorial derivative bounds

A smooth map into a real Banach space agrees with its Taylor series wherever uniform
factorial derivative bounds give a convergent series. No finite-dimensional assumption
on the domain is needed.

The coefficients are the iterated Fréchet derivatives divided by their factorials.
A geometric bound gives a positive convergence radius. Mathlib's multidimensional Taylor
integral formula bounds the remainder by `C (k + 1) q^(k + 1)`, which tends to zero for
`q < 1` and identifies the sum with the original map.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ContDiff NNReal ENNReal

noncomputable section

/-- Uniform factorial bounds on the derivatives of a smooth function identify its Taylor
series with the function. The condition `K * r ≤ 1` gives convergence throughout the
open ball of radius `r`, and the series has coefficients `Dᵏf(x) / k!`. -/
theorem ContDiffOn.hasFPowerSeriesOnBall_of_iteratedFDeriv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x : E} {r : ℝ≥0} {C K : ℝ}
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (ball x r))
    (hr : 0 < r) (hC : 0 ≤ C) (hK : 0 < K) (hKr : K * r ≤ 1)
    (hbound : ∀ k : ℕ, ∀ y ∈ ball x (r : ℝ),
      ‖iteratedFDeriv ℝ k f y‖ ≤ (k.factorial : ℝ) * C * K ^ k) :
    HasFPowerSeriesOnBall f
      (fun k ↦ (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x) x r := by
  let p : FormalMultilinearSeries ℝ E F :=
    fun k ↦ (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x
  have hp (k : ℕ) : ‖p k‖ ≤ C * K ^ k := by
    rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ (by positivity), ← mul_assoc]
    exact hbound k x (mem_ball_self hr)
  have hradius : (r : ℝ≥0∞) ≤ p.radius := p.le_radius_of_bound C fun k ↦
    calc ‖p k‖ * (r : ℝ) ^ k ≤ C * (K * r) ^ k :=
          (mul_le_mul_of_nonneg_right (hp k) (by positivity)).trans_eq (by ring)
      _ ≤ C := mul_le_of_le_one_right hC (pow_le_one₀ (by positivity) hKr)
  refine ⟨hradius, by exact_mod_cast hr, fun {y} hy ↦ ?_⟩
  have hy' : ‖y‖ < (r : ℝ) := by
    simpa only [eball_coe, mem_ball, dist_zero_right] using hy
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • y ∈ ball x (r : ℝ) := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans_lt hy'
  have hrem (k : ℕ) :
      ‖f (x + y) - ∑ i ∈ Finset.range (k + 1), p i (fun _ ↦ y)‖ ≤
        C * (k + 1 : ℕ) * (K * ‖y‖) ^ (k + 1) := by
    have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv fun t ht ↦
      ((hf _ (hpath t ht)).contDiffAt (isOpen_ball.mem_nhds (hpath t ht))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (k + 1))
    change f (x + y) = (∑ i ∈ Finset.range (k + 1), p i (fun _ ↦ y)) + (k.factorial : ℝ)⁻¹ •
      ∫ t in (0 : ℝ)..1, (1 - t) ^ k • iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ ↦ y)
      at htaylor
    have hintegrand (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
        ‖(1 - t) ^ k • iteratedFDeriv ℝ (k + 1) f (x + t • y) (fun _ ↦ y)‖ ≤
          ((k + 1).factorial : ℝ) * C * K ^ (k + 1) * ‖y‖ ^ (k + 1) := by
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht0 k)]
      calc _ ≤ 1 * (‖iteratedFDeriv ℝ (k + 1) f (x + t • y)‖ * ‖y‖ ^ (k + 1)) := by
            gcongr
            · exact pow_le_one₀ ht0 (by linarith [ht.1])
            · simpa using (iteratedFDeriv ℝ (k + 1) f (x + t • y)).le_opNorm (fun _ ↦ y)
        _ ≤ _ := by
          rw [one_mul]
          gcongr
          exact hbound (k + 1) _ (hpath t (Ioc_subset_Icc_self ht))
    rw [htaylor, add_sub_cancel_left, norm_smul, norm_inv, Real.norm_natCast]
    calc _ ≤ (k.factorial : ℝ)⁻¹ * (((k + 1).factorial : ℝ) * C * K ^ (k + 1) * ‖y‖ ^ (k + 1)) := by
          gcongr
          exact (intervalIntegral.norm_integral_le_of_norm_le_const hintegrand).trans_eq (by simp)
      _ = C * (k + 1 : ℕ) * (K * ‖y‖) ^ (k + 1) := by
        rw [Nat.factorial_succ, Nat.cast_mul, mul_pow]
        field_simp
  have hlimit : Tendsto (fun k : ℕ ↦ C * (k + 1 : ℕ) * (K * ‖y‖) ^ (k + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, mul_assoc] using
      ((tendsto_self_mul_const_pow_of_lt_one (by positivity)
        ((mul_lt_mul_of_pos_left hy' hK).trans_le hKr)).comp (tendsto_add_atTop_nat 1)).const_mul C
  refine (hasSum_iff_tendsto_nat_of_summable_norm
    (p.summable_norm_apply (hy.trans_le hradius))).mpr ((tendsto_add_atTop_iff_nat 1).mp ?_)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun k ↦ by simpa only [norm_sub_rev] using hrem k) hlimit
