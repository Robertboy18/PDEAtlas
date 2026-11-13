/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import PDE.Common.Euclidean
import PDE.Spaces.Holder.On

/-!
# Hölder bounds from Lipschitz bounds, and interpolation of derivatives

A function that is `L`-Lipschitz and bounded by `M` on a set is `α`-Hölder there with constant
`max L (2 M)` for every `0 ≤ α ≤ 1`.

If `g` has derivative `g'` along a segment from `x` to `x + h e` and `g'` is `α`-Hölder with
constant `M` at `x` along that segment, then
`‖g' x e‖ ≤ ‖g (x + h e) - g x‖ / h + M (h ‖e‖)^α ‖e‖`: the mean value inequality applied to
`g - g' x`. On the closed upper half-plane `{y | 0 ≤ y 1}` one of `e`, `-e` points inside for
every vector `e`, so a bound `‖g‖ ≤ ε` and a Hölder bound `M` on the derivative within the closed
half-plane give `‖g' x‖ ≤ 2 ε / h + M h^α` for every `h > 0`, and with the optimal `h`,
`‖g' x‖ ≤ 3 ε^{α/(1+α)} M^{1/(1+α)}`. Uniform convergence of functions with equi-Hölder
derivatives therefore forces uniform convergence of the derivatives.

## Main results

* `norm_sub_le_max_mul_rpow`: an `L`-Lipschitz function bounded by `M` is `α`-Hölder with
  constant `max L (2 M)`.
* `norm_apply_le_of_segment`: `‖g' x e‖ ≤ ‖g (x + h e) - g x‖ / h + M (h ‖e‖)^α ‖e‖`.
* `norm_le_of_halfPlane`: `‖g' x‖ ≤ 2 ε / h + M h^α` on the closed upper half-plane, for every
  `h > 0`.
* `norm_le_rpow_mul_rpow_of_halfPlane`: `‖g' x‖ ≤ 3 ε^{α/(1+α)} M^{1/(1+α)}` on the closed upper
  half-plane.
* `exists_norm_le_of_halfPlane`: uniform smallness of `g` with an `α`-Hölder bound on its
  derivative, `α > 0`, forces uniform smallness of the derivative.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

section Lipschitz

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

/-- An `L`-Lipschitz function bounded by `M` on `S` is `α`-Hölder on `S` with constant
`max L (2 M)`, for `0 ≤ α ≤ 1`. -/
theorem norm_sub_le_max_mul_rpow {f : X → F} {S : Set X} {L M α : ℝ}
    (hL : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ L * dist x y) (hM : ∀ x ∈ S, ‖f x‖ ≤ M)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f x - f y‖ ≤ max L (2 * M) * dist x y ^ α := by
  obtain ⟨K, hK⟩ : ∃ K : NNReal, (K : ℝ) = max L (2 * M) :=
    ⟨⟨_, le_max_of_le_right (by linarith [norm_nonneg (f x), hM x hx])⟩, rfl⟩
  obtain ⟨r, rfl⟩ : ∃ r : NNReal, (r : ℝ) = α := ⟨⟨α, hα0⟩, rfl⟩
  have hr : r ≤ 1 := by exact_mod_cast hα1
  have hlip : LipschitzOnWith K f S := .of_dist_le_mul fun z hz w hw ↦ by
    rw [dist_eq_norm, hK]; exact (hL z hz w hw).trans (by gcongr; exact le_max_left _ _)
  have hb (z) (hz : z ∈ S) : ‖f z‖ ≤ (K / 2 : NNReal) := by
    rw [NNReal.coe_div, hK, NNReal.coe_ofNat]; linarith [hM z hz, le_max_right L (2 * M)]
  have h1 : ((1 - r : NNReal) : ℝ) + r = 1 := by
    rw [← NNReal.coe_add, tsub_add_cancel_of_le hr, NNReal.coe_one]
  have h := (hlip.holderOnWith_of_norm_le hb hr).dist_le hx hy
  rwa [mul_div_cancel₀ K two_ne_zero, ← NNReal.rpow_add' (by rw [h1]; exact one_ne_zero), h1,
    NNReal.rpow_one, dist_eq_norm, hK] at h

end Lipschitz

section Segment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Interpolation along a segment.** If `g` has derivative `g' y` within `S` at every point
`y` of the segment from `x` to `x + h e`, which lies in `S`, and
`‖g' y - g' x‖ ≤ M ‖y - x‖^α` there, then
`‖g' x e‖ ≤ ‖g (x + h e) - g x‖ / h + M (h ‖e‖)^α ‖e‖`. -/
theorem norm_apply_le_of_segment {g : E → F} {g' : E → E →L[ℝ] F} {S : Set E} {x e : E}
    {h M α : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hseg : segment ℝ x (x + h • e) ⊆ S)
    (hg : ∀ y ∈ segment ℝ x (x + h • e), HasFDerivWithinAt g (g' y) S y)
    (hg' : ∀ y ∈ segment ℝ x (x + h • e), ‖g' y - g' x‖ ≤ M * ‖y - x‖ ^ α) :
    ‖g' x e‖ ≤ ‖g (x + h • e) - g x‖ / h + M * (h * ‖e‖) ^ α * ‖e‖ := by
  set G : E → F := fun y ↦ g y - g' x y with hG
  have hGd (y : E) (hy : y ∈ segment ℝ x (x + h • e)) :
      HasFDerivWithinAt G (g' y - g' x) (segment ℝ x (x + h • e)) y :=
    ((hg y hy).mono hseg).sub (g' x).hasFDerivWithinAt
  have hbound (y : E) (hy : y ∈ segment ℝ x (x + h • e)) :
      ‖g' y - g' x‖ ≤ M * (h * ‖e‖) ^ α := by
    refine (hg' y hy).trans (mul_le_mul_of_nonneg_left ?_ hM)
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have : a • x + b • (x + h • e) - x = (b * h) • e := by
      have ha' : a = 1 - b := by linarith
      subst ha'
      rw [smul_add, smul_smul, sub_smul, one_smul]
      abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb1 : b ≤ 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (mul_nonneg hh.le (norm_nonneg e))]
  have hmvt := (convex_segment x (x + h • e)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hGd hbound (left_mem_segment ℝ x (x + h • e)) (right_mem_segment ℝ x (x + h • e))
  have hGeq : G (x + h • e) - G x = (g (x + h • e) - g x) - h • g' x e := by
    simp only [hG, map_add, map_smul]
    abel
  rw [hGeq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hmvt
  have hsmul : ‖h • g' x e‖ = h * ‖g' x e‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have htri : h * ‖g' x e‖ ≤ ‖g (x + h • e) - g x‖ + M * (h * ‖e‖) ^ α * (h * ‖e‖) := by
    have := norm_sub_le (g (x + h • e) - g x) ((g (x + h • e) - g x) - h • g' x e)
    rw [sub_sub_cancel, hsmul] at this
    linarith
  calc ‖g' x e‖ = (h * ‖g' x e‖) / h := by field_simp
    _ ≤ (‖g (x + h • e) - g x‖ + M * (h * ‖e‖) ^ α * (h * ‖e‖)) / h := by gcongr
    _ = ‖g (x + h • e) - g x‖ / h + M * (h * ‖e‖) ^ α * ‖e‖ := by field_simp

end Segment


section HalfPlane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The closed upper half-plane `{y | 0 ≤ y 1}` is convex. -/
theorem convex_closedUpperHalfPlane : Convex ℝ {y : ℝ^2 | 0 ≤ y 1} :=
  convex_halfSpace_ge (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0

/-- On the closed upper half-plane `{y | 0 ≤ y 1}`, a bound `‖g‖ ≤ ε` and an `α`-Hölder bound
`M` on the derivative of `g` within the closed half-plane give `‖g' x‖ ≤ 2 ε / h + M h^α` for
every `h > 0`. -/
theorem norm_le_of_halfPlane {g : ℝ^2 → F} {g' : ℝ^2 → ℝ^2 →L[ℝ] F} {ε M α : ℝ}
    (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hg : ∀ y : ℝ^2, 0 ≤ y 1 → HasFDerivWithinAt g (g' y) {y | 0 ≤ y 1} y)
    (hε : ∀ y : ℝ^2, 0 ≤ y 1 → ‖g y‖ ≤ ε)
    (hg' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖g' y - g' z‖ ≤ M * ‖y - z‖ ^ α)
    {x : ℝ^2} (hx : 0 ≤ x 1) {h : ℝ} (hh : 0 < h) :
    ‖g' x‖ ≤ 2 * ε / h + M * h ^ α := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε x hx)
  have hsum : 0 ≤ 2 * ε / h + M * h ^ α := by positivity
  -- the bound in a unit direction pointing into the half-plane
  have hunit (e : ℝ^2) (he : ‖e‖ = 1) (he1 : 0 ≤ e 1) : ‖g' x e‖ ≤ 2 * ε / h + M * h ^ α := by
    have hxe : 0 ≤ (x + h • e) 1 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      positivity
    have hseg : segment ℝ x (x + h • e) ⊆ {y : ℝ^2 | 0 ≤ y 1} :=
      convex_closedUpperHalfPlane.segment_subset hx hxe
    have := norm_apply_le_of_segment hh hM hα hseg (fun y hy ↦ hg y (hseg hy))
      (fun y hy ↦ hg' y x (hseg hy) hx)
    rw [he, mul_one, mul_one] at this
    refine this.trans ?_
    gcongr
    calc ‖g (x + h • e) - g x‖ ≤ ‖g (x + h • e)‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hε _ hxe, hε x hx]
  refine ContinuousLinearMap.opNorm_le_bound _ hsum fun v ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hc : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rcases le_total 0 (v 1) with hv1 | hv1
  · have he : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
    have h1 := hunit (‖v‖⁻¹ • v) he (by
      simp only [PiLp.smul_apply, smul_eq_mul]; positivity)
    rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
    rw [inv_mul_le_iff₀ hc] at h1
    linarith
  · have he : ‖-(‖v‖⁻¹ • v)‖ = 1 := by
      rw [norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
    have h1 := hunit (-(‖v‖⁻¹ • v)) he (by
      simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
      nlinarith [inv_pos.mpr hc])
    rw [map_neg, norm_neg, map_smul, norm_smul, norm_inv, norm_norm] at h1
    rw [inv_mul_le_iff₀ hc] at h1
    linarith

/-- With the optimal `h`: on the closed upper half-plane, `‖g‖ ≤ ε` and an `α`-Hölder bound
`M` on the derivative within the closed half-plane give
`‖g' x‖ ≤ 3 ε^{α/(1+α)} M^{1/(1+α)}`. -/
theorem norm_le_rpow_mul_rpow_of_halfPlane {g : ℝ^2 → F} {g' : ℝ^2 → ℝ^2 →L[ℝ] F}
    {ε M α : ℝ} (hε0 : 0 < ε) (hM0 : 0 < M) (hα : 0 ≤ α)
    (hg : ∀ y : ℝ^2, 0 ≤ y 1 → HasFDerivWithinAt g (g' y) {y | 0 ≤ y 1} y)
    (hε : ∀ y : ℝ^2, 0 ≤ y 1 → ‖g y‖ ≤ ε)
    (hg' : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖g' y - g' z‖ ≤ M * ‖y - z‖ ^ α)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖g' x‖ ≤ 3 * ε ^ (α / (1 + α)) * M ^ (1 / (1 + α)) := by
  set p : ℝ := 1 / (1 + α) with hp
  set q : ℝ := α / (1 + α) with hq
  have h1α : 0 < 1 + α := by linarith
  have hpq : q + p = 1 := by rw [hp, hq, ← add_div, add_comm, div_self h1α.ne']
  have hpα : p * α = q := by rw [hp, hq]; field_simp
  set h : ℝ := ε ^ p * M ^ (-p) with hh
  have hpos : 0 < h := by positivity
  have hfirst : ε / h = ε ^ q * M ^ p := by
    rw [div_eq_iff hpos.ne', hh]
    calc ε = ε ^ (q + p) * M ^ (p + -p) := by
          rw [hpq, add_neg_cancel, Real.rpow_one, Real.rpow_zero, mul_one]
      _ = ε ^ q * M ^ p * (ε ^ p * M ^ (-p)) := by
          rw [Real.rpow_add hε0, Real.rpow_add hM0]; ring
  have hsecond : M * h ^ α = ε ^ q * M ^ p := by
    rw [hh, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hε0.le,
      ← Real.rpow_mul hM0.le, hpα]
    rw [show -p * α = -q by rw [neg_mul, hpα]]
    have hMp : M * M ^ (-q) = M ^ p := by
      rw [show p = 1 + -q by linarith, Real.rpow_add hM0, Real.rpow_one]
    calc M * (ε ^ q * M ^ (-q)) = ε ^ q * (M * M ^ (-q)) := by ring
      _ = ε ^ q * M ^ p := by rw [hMp]
  have := norm_le_of_halfPlane hM0.le hα hg hε hg' hx hpos
  rw [mul_div_assoc, hfirst, hsecond] at this
  linarith

/-- Uniform smallness of `g` on the closed upper half-plane, with an `α`-Hölder bound `M` on its
derivative within the closed half-plane (`α > 0`), forces uniform smallness of the
derivative. -/
theorem exists_norm_le_of_halfPlane {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α) {δ : ℝ}
    (hδ : 0 < δ) : ∃ η > 0, ∀ (g : ℝ^2 → F) (g' : ℝ^2 → ℝ^2 →L[ℝ] F),
      (∀ y : ℝ^2, 0 ≤ y 1 → HasFDerivWithinAt g (g' y) {y | 0 ≤ y 1} y) →
      (∀ y : ℝ^2, 0 ≤ y 1 → ‖g y‖ ≤ η) →
      (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖g' y - g' z‖ ≤ M * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 ≤ x 1 → ‖g' x‖ ≤ δ := by
  set h : ℝ := (δ / (2 * (M + 1))) ^ (1 / α) with hh
  have hbase : 0 < δ / (2 * (M + 1)) := by positivity
  have hpos : 0 < h := by positivity
  have hpow : h ^ α = δ / (2 * (M + 1)) := by
    rw [hh, ← Real.rpow_mul hbase.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨δ * h / 4, by positivity, fun g g' hg hε hg' x hx ↦ ?_⟩
  have := norm_le_of_halfPlane hM hα.le hg hε hg' hx hpos
  have hfirst : 2 * (δ * h / 4) / h = δ / 2 := by field_simp; ring
  have hsecond : M * h ^ α ≤ δ / 2 := by
    rw [hpow]
    have : M * (δ / (2 * (M + 1))) = δ / 2 * (M / (M + 1)) := by field_simp
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  linarith

end HalfPlane

end PDE.Analysis
