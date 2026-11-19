/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Outer
public import PDE.Elliptic.OneDimensional.BoundaryLayer.Asymptotics
import CAS.ExactTactic

/-!
# Uniform and inner limits from boundary-layer error bounds

The exact-correction remainder and the frozen-profile error imply a uniform
O(ε) composite estimate. The outer approximation converges uniformly away from
the left boundary, and on the whole interval exactly when its left trace matches.
At each fixed nonnegative stretched coordinate, the limit is the frozen
exponential profile. Matching and nonconstancy of that profile are the defining features
of a boundary layer.

These follow from the error estimates; `Expansion` constructs the required solution
family from raw local C¹ coefficients.
-/

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology
namespace PDE.Elliptic.BoundaryLayer.Variable

/-- The endpoint exponential tail has a global bound of order ε. -/
theorem exponential_tail_le {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L) :
    Real.exp (-b * L / ε) ≤ ε / (b * L) := by
  have ht : 0 < b * L / ε := div_pos (mul_pos hb hL) hε
  have h : (b * L / ε) * Real.exp (-(b * L / ε)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have heq : (b * L / ε) * (ε / (b * L)) = 1 := by
    cas using And.intro hε.ne' (mul_pos hb hL).ne'
  apply (mul_le_mul_iff_right₀ ht).mp
  simpa only [neg_div, neg_mul, heq] using h

/-- The composite error retains both spatial decay and the finite-interval endpoint tail. -/
theorem composite_pointwise_bound {L ε α μ b M C : ℝ} (u v H : ℝ → ℝ) (D : ℝ)
    (hexact : ∀ x ∈ Icc 0 L, |u x - v x - D * H x| ≤ ε * M * (L - x) / α)
    (hprofile : ∀ x ∈ Icc 0 L, |H x - Real.exp (-b * x / ε)| ≤
      C * ε * Real.exp (-μ * x / ε) + Real.exp (-b * L / ε)) :
    ∀ x ∈ Icc 0 L, |u x - (v x + D * Real.exp (-b * x / ε))| ≤
      ε * M * (L - x) / α +
        |D| * (C * ε * Real.exp (-μ * x / ε) + Real.exp (-b * L / ε)) := by
  intro x hx
  have hsplit : u x - (v x + D * Real.exp (-b * x / ε)) =
      (u x - v x - D * H x) + D * (H x - Real.exp (-b * x / ε)) := by ring
  rw [hsplit]
  calc
    _ ≤ |u x - v x - D * H x| + |D * (H x - Real.exp (-b * x / ε))| := abs_add_le _ _
    _ = |u x - v x - D * H x| + |D| * |H x - Real.exp (-b * x / ε)| := by rw [abs_mul]
    _ ≤ _ :=
      add_le_add (hexact x hx) (mul_le_mul_of_nonneg_left (hprofile x hx) (abs_nonneg _))

/-- Exact-correction and frozen-profile estimates yield a uniform composite error bound. -/
theorem composite_bound {L ε α μ b M C : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hμ : 0 < μ) (hM : 0 ≤ M) (hC : 0 ≤ C) (u v H : ℝ → ℝ) (D : ℝ)
    (hexact : ∀ x ∈ Icc 0 L, |u x - v x - D * H x| ≤ ε * M * (L - x) / α)
    (hprofile : ∀ x ∈ Icc 0 L, |H x - Real.exp (-b * x / ε)| ≤
      C * ε * Real.exp (-μ * x / ε) + Real.exp (-b * L / ε)) :
    ∀ x ∈ Icc 0 L, |u x - (v x + D * Real.exp (-b * x / ε))| ≤
      ε * M * L / α + |D| * (C * ε + Real.exp (-b * L / ε)) := by
  intro x hx
  have hE : Real.exp (-μ * x / ε) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμ.le) hx.1) hε.le)
  calc
    _ ≤ ε * M * (L - x) / α +
        |D| * (C * ε * Real.exp (-μ * x / ε) + Real.exp (-b * L / ε)) :=
      composite_pointwise_bound u v H D hexact hprofile x hx
    _ ≤ _ := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sub_le_self L hx.1) (mul_nonneg hε.le hM)) hα.le
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg D)
        apply add_le_add _ le_rfl
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hE (mul_nonneg hC hε.le)

/-- A single ε-independent constant controls the composite remainder on the closed interval. -/
theorem composite_linear_bound {L ε α μ b M C : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hα : 0 < α) (hμ : 0 < μ) (hb : 0 < b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (u v H : ℝ → ℝ) (D : ℝ)
    (hexact : ∀ x ∈ Icc 0 L, |u x - v x - D * H x| ≤ ε * M * (L - x) / α)
    (hprofile : ∀ x ∈ Icc 0 L, |H x - Real.exp (-b * x / ε)| ≤
      C * ε * Real.exp (-μ * x / ε) + Real.exp (-b * L / ε)) :
    ∀ x ∈ Icc 0 L, |u x - (v x + D * Real.exp (-b * x / ε))| ≤
      ε * (M * L / α + |D| * (C + 1 / (b * L))) := by
  intro x hx
  calc
    _ ≤ ε * M * L / α + |D| * (C * ε + Real.exp (-b * L / ε)) :=
      composite_bound hε hα hμ hM hC u v H D hexact hprofile x hx
    _ ≤ ε * M * L / α + |D| * (C * ε + ε / (b * L)) := by
      gcongr
      exact exponential_tail_le hε hb hL
    _ = _ := by ring

/-- The outer approximation is uniform on each interval separated from the inflow boundary. -/
theorem outer_tendstoUniformlyOn {L α M δ : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (hδ : 0 < δ) (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) (D : ℝ)
    (herror : ∀ ε > 0, ∀ x ∈ Icc 0 L,
      |u ε x - v x| ≤ |D| * Real.exp (-α * x / ε) + ε * M * (L - x) / α) :
    TendstoUniformlyOn u v (𝓝[>] 0) (Icc δ L) := by
  have ht : Tendsto (fun ε ↦ |D| * Real.exp (-α * δ / ε) + ε * M * L / α)
      (𝓝[>] 0) (𝓝 0) := by
    have he := (BoundaryLayer.layer_tendsto hα hδ).const_mul |D|
    have hl := (((show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const M).mul_const L).div_const α
    simpa only [BoundaryLayer.layer, mul_zero, zero_mul, zero_div, add_zero] using he.add hl
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [ht.eventually (gt_mem_nhds hη), self_mem_nhdsWithin] with ε he hε
  change 0 < ε at hε
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  refine (herror ε hε x ⟨hδ.le.trans hx.1, hx.2⟩).trans_lt (lt_of_le_of_lt ?_ he)
  have hexp : Real.exp (-α * x / ε) ≤ Real.exp (-α * δ / ε) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonpos_left hx.1 (neg_nonpos.mpr hα.le)) hε.le)
  exact add_le_add (mul_le_mul_of_nonneg_left hexp (abs_nonneg D))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_self L (hδ.le.trans hx.1))
        (mul_nonneg hε.le hM)) hα.le)

/-- A zero boundary mismatch permits uniform outer convergence on the whole interval. -/
theorem outer_tendstoUniformlyOn_of_zero_mismatch {L α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (herror : ∀ ε > 0, ∀ x ∈ Icc 0 L, |u ε x - v x| ≤ ε * M * (L - x) / α) :
    TendstoUniformlyOn u v (𝓝[>] 0) (Icc 0 L) := by
  have ht : Tendsto (fun ε : ℝ ↦ ε * M * L / α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, zero_div] using
      (((show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const M).mul_const L).div_const α
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [ht.eventually (gt_mem_nhds hη), self_mem_nhdsWithin] with ε he hε
  change 0 < ε at hε
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  refine (herror ε hε x hx).trans_lt (lt_of_le_of_lt ?_ he)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_self L hx.1) (mul_nonneg hε.le hM)) hα.le

/-- Fixed left traces obstruct uniform outer convergence whenever the mismatch is nonzero. -/
theorem not_outer_tendstoUniformlyOn {L A : ℝ} (hL : 0 ≤ L)
    (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) (htrace : ∀ ε > 0, u ε 0 = A) (hD : A - v 0 ≠ 0) :
    ¬TendstoUniformlyOn u v (𝓝[>] 0) (Icc 0 L) := by
  intro hu
  have hpoint := hu.tendsto_at (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)
  have hA : Tendsto (fun ε ↦ u ε 0) (𝓝[>] 0) (𝓝 A) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (htrace ε hε).symm
  exact hD (sub_eq_zero.mpr (tendsto_nhds_unique hA hpoint))

/-- A uniform linear error estimate yields convergence of the composite remainder. -/
theorem composite_tendstoUniformlyOn {L b C : ℝ} (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ) (D : ℝ)
    (herror : ∀ ε > 0, ∀ x ∈ Icc 0 L,
      |u ε x - (v x + D * Real.exp (-b * x / ε))| ≤ ε * C) :
    TendstoUniformlyOn (fun ε x ↦ u ε x - (v x + D * Real.exp (-b * x / ε)))
      (fun _ ↦ 0) (𝓝[>] 0) (Icc 0 L) := by
  have ht : Tendsto (fun ε : ℝ ↦ ε * C) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [ht.eventually (gt_mem_nhds hη), self_mem_nhdsWithin] with ε he hε
  intro x hx
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact (herror ε hε x hx).trans_lt he

/-- At every fixed nonnegative stretched coordinate, the solution approaches the frozen profile. -/
theorem stretched_tendsto {L b C : ℝ} (hL : 0 < L) (u : ℝ → ℝ → ℝ)
    (v : ℝ → ℝ) (hv : Continuous v) (D : ℝ)
    (herror : ∀ ε > 0, ∀ x ∈ Icc 0 L,
      |u ε x - (v x + D * Real.exp (-b * x / ε))| ≤ ε * C)
    {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun ε ↦ u ε (ε * y)) (𝓝[>] 0) (𝓝 (v 0 + D * Real.exp (-b * y))) := by
  have hcoord : Tendsto (fun ε : ℝ ↦ ε * y) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const y
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * y ∈ Icc 0 L := by
    filter_upwards [hcoord.eventually (gt_mem_nhds hL), self_mem_nhdsWithin] with ε he hε
    exact ⟨mul_nonneg hε.le hy, he.le⟩
  have hremainder : Tendsto (fun ε ↦ u ε (ε * y) -
      (v (ε * y) + D * Real.exp (-b * y))) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun ε : ℝ ↦ ε * C)
    · filter_upwards [hin, self_mem_nhdsWithin] with ε hx hε
      have heq : -b * (ε * y) / ε = -b * y := by
        have hεpos : 0 < ε := hε
        cas using hεpos.ne'
      simpa only [Real.norm_eq_abs, heq] using herror ε hε (ε * y) hx
    · simpa only [zero_mul] using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C
  have houter := (hv.tendsto 0).comp hcoord
  have hsum := hremainder.add (houter.add_const (D * Real.exp (-b * y)))
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hsum

/-- The frozen inner profile matches the left value of the outer solution at infinity. -/
theorem inner_matching {b : ℝ} (hb : 0 < b) (v₀ D : ℝ) :
    Tendsto (fun y ↦ v₀ + D * Real.exp (-b * y)) atTop (𝓝 v₀) := by
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
  simpa only [Function.comp_def, id_eq, neg_mul, mul_zero, add_zero] using
    tendsto_const_nhds.add (ht.const_mul D)

/-- A nonzero mismatch gives a genuinely nonconstant inner profile on the physical half-line. -/
theorem inner_nonconstant {b D : ℝ} (hb : 0 < b) (hD : D ≠ 0) (v₀ : ℝ) :
    v₀ + D * Real.exp (-b * 0) ≠ v₀ + D * Real.exp (-b * 1) := by
  simp only [mul_zero, Real.exp_zero, mul_one, ne_eq, add_right_inj]
  intro h
  have he : Real.exp (-b) = 1 := (mul_left_cancel₀ hD (by simpa using h.symm))
  have ht : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb)
  linarith

end PDE.Elliptic.BoundaryLayer.Variable
