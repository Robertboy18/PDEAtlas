/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Analysis.Calculus.HalfSpaceGluing
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Hölder derivatives up to the boundary of the half-plane

Let `v` be continuous on the closed upper half-plane `H̄ = {x₁ ≥ 0}` and differentiable on the
open half-plane `H`, with `‖Dv(y) - Dv(y')‖ ≤ C |y - y'|^α` on `H` for some `α > 0`. Then the
interior derivatives are uniformly continuous, so they converge at every point of `H̄`; a function
continuous on the closure of a convex open set whose derivative converges at a boundary point is
differentiable within the closure there (Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv`).
Hence `v` is differentiable within `H̄` at every point of `H̄`, its derivative within `H̄` is the
limit of the interior derivatives, and it is `α`-Hölder on `H̄` with the same constant.

## Main results

* `hasFDerivWithinAt_closedUpper_of_holder`: `v` is differentiable within `H̄` at every point of
  `H̄`, with derivative the limit of the interior derivatives.
* `norm_fderivWithin_closedUpper_sub_le_of_holder`: the derivative within `H̄` is `α`-Hölder on
  `H̄` with the interior constant `C`.
-/

@[expose] public section

noncomputable section

open Filter Set Metric
open scoped Topology
open SobolevSpace

namespace PDE.Analysis

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The open upper half-plane `HalfSpace.upper 2` is convex. -/
private theorem convex_upper : Convex ℝ (HalfSpace.upper 2) :=
  convex_halfSpace_gt (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0

/-- A point of `H̄` moved by `t > 0` along the normal `e₁` lies in the open upper half-plane. -/
private theorem mem_upper_add_smul {x : ℝ^2} (hx : 0 ≤ x 1) {t : ℝ} (ht : 0 < t) :
    x + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ∈ HalfSpace.upper 2 := by
  change (0 : ℝ) < (x + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp
  linarith

/-- Points of the closed half-plane are limits from inside along the normal direction. -/
private theorem tendsto_shift (x : ℝ^2) (hx : 0 ≤ x 1) :
    Tendsto (fun t : ℝ ↦ x + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (𝓝[>] 0)
      (𝓝[HalfSpace.upper 2] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Tendsto (fun t : ℝ ↦ x + t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (𝓝 0)
        (𝓝 (x + (0 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :=
      tendsto_const_nhds.add (tendsto_id.smul_const _)
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mem_upper_add_smul hx ht

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {v : ℝ^2 → F} {C α : ℝ}

section Holder

variable (hα : 0 < α) (hv : ContinuousOn v H̄) (hd : DifferentiableOn ℝ v (HalfSpace.upper 2))
  (hC : ∀ y ∈ HalfSpace.upper 2, ∀ y' ∈ HalfSpace.upper 2,
    ‖fderiv ℝ v y - fderiv ℝ v y'‖ ≤ C * ‖y - y'‖ ^ α)
include hα hC

omit [CompleteSpace F] in
/-- The interior derivatives form a Cauchy family at every point of the closed half-plane. -/
private theorem cauchy_fderiv {x : ℝ^2} (hx : 0 ≤ x 1) :
    Cauchy (map (fderiv ℝ v) (𝓝[HalfSpace.upper 2] x)) := by
  have hcl : x ∈ closure (HalfSpace.upper 2) := by rw [HalfSpace.closure_upper_two]; exact hx
  have : (𝓝[HalfSpace.upper 2] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hK : 0 < |C| + 1 := by positivity
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  set r := (ε / (2 * (|C| + 1))) ^ (1 / α) / 2 with hrdef
  have hr : 0 < r := by positivity
  refine ⟨fderiv ℝ v '' (HalfSpace.upper 2 ∩ ball x r), image_mem_map
    (inter_mem_nhdsWithin _ (ball_mem_nhds x hr)), ?_⟩
  rintro _ ⟨a, ⟨haH, har⟩, rfl⟩ _ ⟨b, ⟨hbH, hbr⟩, rfl⟩
  rw [dist_eq_norm]
  have hab : ‖a - b‖ < 2 * r := by
    rw [mem_ball, dist_eq_norm] at har hbr
    have := norm_sub_le_norm_sub_add_norm_sub a x b
    rw [norm_sub_rev x b] at this
    linarith
  have hpow : ‖a - b‖ ^ α < ε / (2 * (|C| + 1)) := by
    have h2r : 2 * r = (ε / (2 * (|C| + 1))) ^ (1 / α) := by rw [hrdef]; ring
    have := Real.rpow_lt_rpow (norm_nonneg _) (hab.trans_eq h2r) hα
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at this
  calc ‖fderiv ℝ v a - fderiv ℝ v b‖ ≤ C * ‖a - b‖ ^ α := hC a haH b hbH
    _ ≤ (|C| + 1) * ‖a - b‖ ^ α := by
        gcongr
        linarith [le_abs_self C]
    _ ≤ (|C| + 1) * (ε / (2 * (|C| + 1))) := by gcongr
    _ < ε := by
        rw [show (|C| + 1) * (ε / (2 * (|C| + 1))) = ε / 2 by field_simp]
        linarith

include hv hd in
/-- **Differentiability up to the boundary.** At every point of the closed half-plane, `v` is
differentiable within it, and its derivative within it is the limit of the interior
derivatives. -/
theorem hasFDerivWithinAt_closedUpper_of_holder {x : ℝ^2} (hx : 0 ≤ x 1) :
    HasFDerivWithinAt v (fderivWithin ℝ v H̄ x) H̄ x ∧
      Tendsto (fderiv ℝ v) (𝓝[HalfSpace.upper 2] x) (𝓝 (fderivWithin ℝ v H̄ x)) := by
  obtain ⟨L, hL⟩ := CompleteSpace.complete (cauchy_fderiv hα hC hx)
  have hdc := hasFDerivWithinAt_closure_of_tendsto_fderiv hd convex_upper
    (HalfSpace.isOpen_upper 2)
    (fun y hy ↦ (hv y (by rwa [HalfSpace.closure_upper_two] at hy)).mono (fun z hz ↦
      (le_of_lt (show (0 : ℝ) < z 1 from hz) : (0 : ℝ) ≤ z 1))) hL
  rw [HalfSpace.closure_upper_two] at hdc
  have heq : fderivWithin ℝ v H̄ x = L :=
    hdc.fderivWithin (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2) x hx)
  rw [heq]
  exact ⟨hdc, hL⟩

include hv hd in
/-- **Hölder continuity of the derivative up to the boundary**, with the interior constant. -/
theorem norm_fderivWithin_closedUpper_sub_le_of_holder {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖fderivWithin ℝ v H̄ x - fderivWithin ℝ v H̄ x'‖ ≤ C * ‖x - x'‖ ^ α := by
  set e := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have h1 := (hasFDerivWithinAt_closedUpper_of_holder hα hv hd hC hx).2.comp (tendsto_shift x hx)
  have h2 :=
    (hasFDerivWithinAt_closedUpper_of_holder hα hv hd hC hx').2.comp (tendsto_shift x' hx')
  refine le_of_tendsto (h1.sub h2).norm ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hb := hC _ (mem_upper_add_smul hx ht) _ (mem_upper_add_smul hx' ht)
  rwa [show x + t • e - (x' + t • e) = x - x' by abel] at hb

end Holder

end PDE.Analysis
