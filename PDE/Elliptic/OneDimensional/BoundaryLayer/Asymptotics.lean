/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Explicit
import CAS.ExactTactic

/-!
# Matching and error bounds for the convection-diffusion layer

The reduced solution converges uniformly on every interval separated from the left
endpoint. On the whole interval it misses the prescribed left value by a fixed amount.
Adding the exponential layer gives a uniformly exponentially accurate composite
approximation. At distances `x = εy`, the limiting profile is nonconstant whenever
the boundary mismatch is nonzero.

All estimates concern the explicit solution of the differential boundary-value problem
in `Explicit`, with arbitrary positive drift and interval length.
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.BoundaryLayer

open Filter Set
open scoped Topology

/-- The layer is positive. -/
theorem layer_pos (ε b x : ℝ) : 0 < layer ε b x :=
  Real.exp_pos _

/-- Positive drift makes the layer decrease away from the left endpoint. -/
theorem layer_antitone {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    Antitone (layer ε b) := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hb.le)) hε.le

/-- The normalized profile is nonnegative to the left of the right endpoint. -/
theorem profile_nonneg {ε b L x : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (hx : x ≤ L) : 0 ≤ profile ε b L x :=
  div_nonneg (sub_nonneg.mpr (layer_antitone hε hb hx)) (denominator_pos hε hb hL).le

/-- The normalized profile is bounded above by the exponential divided by its normalization. -/
theorem profile_le {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L) (x : ℝ) :
    profile ε b L x ≤ layer ε b x / (1 - layer ε b L) :=
  div_le_div_of_nonneg_right
    (sub_le_self _ (layer_pos ε b L).le) (denominator_pos hε hb hL).le

/-- An interior estimate uniform in `x ≥ δ`; its right side decays exponentially. -/
theorem interior_error_le {ε b L δ x : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (hx : x ∈ Icc δ L) (A B f : ℝ) :
    |solution ε b L A B f x - outer b L B f x| ≤
      |mismatch b L A B f| * layer ε b δ / (1 - layer ε b L) := by
  have hp := profile_nonneg hε hb hL hx.2
  have hbound := (profile_le hε hb hL x).trans (div_le_div_of_nonneg_right
    (layer_antitone hε hb hx.1) (denominator_pos hε hb hL).le)
  simp only [solution, add_sub_cancel_left, abs_mul, abs_of_nonneg hp]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

/-- The exact correction differs from the matched exponential only by an endpoint tail. -/
theorem profile_sub_layer {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (x : ℝ) :
    profile ε b L x - layer ε b x =
      layer ε b L * (layer ε b x - 1) / (1 - layer ε b L) := by
  have hd := (denominator_pos hε hb hL).ne'
  unfold profile
  cas using hd

/-- The matched composite approximation has a uniform exponentially small remainder. -/
theorem composite_error_le {ε b L x : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (hx : x ∈ Icc 0 L) (A B f : ℝ) :
    |solution ε b L A B f x - composite ε b L A B f x| ≤
      |mismatch b L A B f| * layer ε b L / (1 - layer ε b L) := by
  have hd := denominator_pos hε hb hL
  have hxle : layer ε b x ≤ 1 := by
    simpa [layer] using layer_antitone hε hb hx.1
  have hdiff : |layer ε b x - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxle)]
    linarith [layer_pos ε b x]
  have heq : solution ε b L A B f x - composite ε b L A B f x =
      mismatch b L A B f * (profile ε b L x - layer ε b x) := by
    unfold solution composite
    cas
  rw [heq, profile_sub_layer hε hb hL, abs_mul, abs_div, abs_mul,
    abs_of_pos (layer_pos ε b L), abs_of_pos hd]
  calc
    _ ≤ |mismatch b L A B f| * (layer ε b L * 1 / (1 - layer ε b L)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff (layer_pos ε b L).le) hd.le) (abs_nonneg _)
    _ = _ := by simp [mul_div_assoc]

/-- At every fixed positive distance the exponential layer vanishes as `ε ↓ 0`. -/
theorem layer_tendsto {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    Tendsto (fun ε ↦ layer ε b x) (𝓝[>] 0) (𝓝 0) := by
  have ht := tendsto_inv_nhdsGT_zero.const_mul_atTop (mul_pos hb hx)
  simpa only [layer, div_eq_mul_inv, neg_mul, Function.comp_def] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

/-- The uniform interior error bound tends to zero, without an assumed convergence premise. -/
theorem interior_bound_tendsto {b L δ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hδ : 0 < δ) (D : ℝ) :
    Tendsto (fun ε ↦ |D| * layer ε b δ / (1 - layer ε b L)) (𝓝[>] 0) (𝓝 0) := by
  simpa only [mul_zero, sub_zero, zero_div] using!
    ((layer_tendsto hb hδ).const_mul |D|).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (layer_tendsto hb hL)) (by norm_num)

/-- Uniform convergence of the exact solution to the reduced solution away from the layer. -/
theorem solution_tendstoUniformlyOn {b L δ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hδ : 0 < δ) (A B f : ℝ) :
    TendstoUniformlyOn (fun ε ↦ solution ε b L A B f) (outer b L B f)
      (𝓝[>] 0) (Icc δ L) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have he := (interior_bound_tendsto hb hL hδ (mismatch b L A B f)).eventually
    (gt_mem_nhds hη)
  filter_upwards [he, self_mem_nhdsWithin] with ε he hε
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (interior_error_le hε hb hL hx A B f).trans_lt he

/-- The reduced solution cannot converge even pointwise at the mismatched left endpoint. -/
theorem boundary_error {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (A B f : ℝ) :
    |solution ε b L A B f 0 - outer b L B f 0| = |mismatch b L A B f| := by
  rw [solution_zero hε hb hL]
  rfl

/-- A nonzero mismatch rules out uniform convergence to the outer solution on `[0,L]`. -/
theorem not_solution_tendstoUniformlyOn {b L A B f : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hD : mismatch b L A B f ≠ 0) :
    ¬TendstoUniformlyOn (fun ε ↦ solution ε b L A B f) (outer b L B f)
      (𝓝[>] 0) (Icc 0 L) := by
  intro h
  have hpos := abs_pos.mpr hD
  have he := Metric.tendstoUniformlyOn_iff.mp h (|mismatch b L A B f| / 2)
    (half_pos hpos)
  obtain ⟨ε, he, hε⟩ := (he.and self_mem_nhdsWithin).exists
  have hz := he 0 (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
  rw [Real.dist_eq, abs_sub_comm, boundary_error hε hb hL] at hz
  linarith

/-- The composite remainder converges uniformly to zero on the entire interval. -/
theorem composite_remainder_tendstoUniformlyOn {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) (A B f : ℝ) :
    TendstoUniformlyOn
      (fun ε x ↦ solution ε b L A B f x - composite ε b L A B f x)
      (fun _ ↦ 0) (𝓝[>] 0) (Icc 0 L) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have he := (interior_bound_tendsto hb hL hL (mismatch b L A B f)).eventually
    (gt_mem_nhds hη)
  filter_upwards [he, self_mem_nhdsWithin] with ε he hε
  intro x hx
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact (composite_error_le hε hb hL hx A B f).trans_lt he

/-- The layer remains visible at distances proportional to `ε`. -/
theorem layer_stretched {ε : ℝ} (hε : ε ≠ 0) (b y : ℝ) :
    layer ε b (ε * y) = Real.exp (-b * y) := by
  unfold layer
  congr 1
  cas using hε

/-- The inner limit matches the outer value plus a nontrivial exponential correction. -/
theorem solution_stretched_tendsto {b L : ℝ} (hb : 0 < b) (hL : 0 < L)
    (A B f y : ℝ) :
    Tendsto (fun ε ↦ solution ε b L A B f (ε * y)) (𝓝[>] 0)
      (𝓝 (outer b L B f 0 + mismatch b L A B f * Real.exp (-b * y))) := by
  have houter : Tendsto (fun ε : ℝ ↦ outer b L B f (ε * y)) (𝓝[>] 0)
      (𝓝 (outer b L B f 0)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ outer b L B f (ε * y)) 0 := by
      unfold outer
      fun_prop
    simpa only [zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprof : Tendsto
      (fun ε ↦ (Real.exp (-b * y) - layer ε b L) / (1 - layer ε b L))
      (𝓝[>] 0) (𝓝 (Real.exp (-b * y))) := by
    simpa only [sub_zero, div_one] using!
      ((tendsto_const_nhds (x := Real.exp (-b * y))).sub (layer_tendsto hb hL)).div
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (layer_tendsto hb hL)) (by norm_num)
  apply (houter.add (hprof.const_mul (mismatch b L A B f))).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [solution, profile, layer_stretched (ne_of_gt hε)]

/-- The far end of the inner profile matches the left trace of the outer solution. -/
theorem inner_matching_tendsto {b : ℝ} (hb : 0 < b) (L A B f : ℝ) :
    Tendsto (fun y ↦ outer b L B f 0 + mismatch b L A B f * Real.exp (-b * y))
      atTop (𝓝 (outer b L B f 0)) := by
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hb)
  simpa only [Function.comp_def, id_eq, neg_mul, mul_zero, add_zero] using!
    tendsto_const_nhds.add (ht.const_mul (mismatch b L A B f))

end PDE.Elliptic.BoundaryLayer
