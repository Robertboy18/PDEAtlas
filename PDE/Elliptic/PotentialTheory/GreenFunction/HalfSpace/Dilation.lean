/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundedSource

/-!
# Dilations of the planar half-space Green potential

A dilation `y ↦ λ y` with `λ > 0` maps the upper half-plane onto itself and commutes with the
reflection in its boundary. The planar Green function
`G(y, x) = (2π)⁻¹ (log |x - y*| - log |x - y|)` is a difference of two logarithms of distances, so
it is invariant, `G(λ y, λ x) = G(y, x)` away from the two poles. With the Jacobian `λ²` of the
change of variables, the potential of the dilated source `f(λ ·)` at `x` is `λ⁻²` times the
potential of `f` at `λ x`. Like the translation identity, it is an identity of total integrals
and needs no integrability of the source.

## Main results

* `halfSpaceGreenFunction_two_smul_smul`: `G(λ y, λ x) = G(y, x)` for `λ > 0` away from the poles
  `x = y` and `x = y*`.
* `halfSpaceGreenPotential_comp_smul`: for `λ > 0` the potential of `f(λ ·)` at `x` is `λ⁻²`
  times the potential of `f` at `λ x`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open SobolevSpace
open scoped Pointwise

namespace GreenFunction

variable {lam : ℝ}

/-- Positive dilations preserve the upper half-plane. -/
theorem smul_upper_two (hlam : 0 < lam) : lam • HalfSpace.upper 2 = HalfSpace.upper 2 := by
  ext y
  rw [mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  simp only [HalfSpace.upper, mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, gt_iff_lt]
  constructor
  · intro h
    have := mul_pos hlam h
    rwa [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at this
  · intro h
    exact mul_pos (inv_pos.mpr hlam) h

/-- The reflection in the boundary line commutes with dilations. -/
theorem reflect_two_smul (lam : ℝ) (y : ℝ^2) :
    HalfSpace.reflect 2 (lam • y) = lam • HalfSpace.reflect 2 y := by
  rw [← HalfSpace.reflectLinearEquiv_apply, map_smul, HalfSpace.reflectLinearEquiv_apply]

/-- **Dilation invariance of the planar Green function**: `G(λ y, λ x) = G(y, x)` for `λ > 0`
away from the poles `x = y` and `x = y*`. -/
theorem halfSpaceGreenFunction_two_smul_smul (hlam : 0 < lam) {y x : ℝ^2} (hxy : x ≠ y)
    (hxy' : x ≠ HalfSpace.reflect 2 y) :
    halfSpaceGreenFunction (lam • y) (lam • x) = halfSpaceGreenFunction y x := by
  have h1 : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have h2 : ‖x - HalfSpace.reflect 2 y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy')
  rw [halfSpaceGreenFunction_two_eq, halfSpaceGreenFunction_two_eq, reflect_two_smul, ← smul_sub,
    ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hlam.le,
    Real.log_mul hlam.ne' h1, Real.log_mul hlam.ne' h2]
  ring

/-- **The Green potential of a dilated source**: for `λ > 0`, the potential of `f(λ ·)` at `x` is
`λ⁻²` times the potential of `f` at `λ x`. -/
theorem halfSpaceGreenPotential_comp_smul (hlam : 0 < lam) (f : ℝ^2 → ℝ) (x : ℝ^2) :
    halfSpaceGreenPotential (fun y ↦ f (lam • y)) x =
      (lam ^ 2)⁻¹ * halfSpaceGreenPotential f (lam • x) := by
  unfold halfSpaceGreenPotential
  have hcv := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun y ↦ halfSpaceGreenFunction y (lam • x) * f y) (HalfSpace.upper 2) hlam
  rw [smul_upper_two hlam, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hcv
  rw [← hcv]
  have hnull : (volume : Measure (ℝ^2)) ({x, HalfSpace.reflect 2 x} : Set (ℝ^2)) = 0 :=
    (Set.toFinite _).measure_zero _
  refine setIntegral_congr_ae (HalfSpace.measurableSet_upper (n := 2)) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy _
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy
  rw [halfSpaceGreenFunction_two_smul_smul hlam (Ne.symm hy.1) ?_]
  intro h
  apply hy.2
  rw [h, HalfSpace.reflect_involutive]

end GreenFunction
