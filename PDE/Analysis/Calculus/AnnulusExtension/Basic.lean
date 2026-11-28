/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Analysis.Calculus.ReflectionGluing

/-!
# Extension of a `C²` function from the annulus `1 ≤ |y| ≤ 2` to the whole space

A `C²` function `v` on a finite-dimensional real inner product space, with values in a real
normed space, is extended from the closed annulus `1 ≤ |y| ≤ 2` to a `C²` function with compact
support on the whole space. The extension agrees with `v` on the annulus and uses no other
values of `v`, so its derivatives are controlled by those of `v` on the annulus alone
(`PDE.Analysis.Calculus.AnnulusExtension.Bounds`). Agmon's inequality on the annulus is built
on it. Only the radii `1` and `2` and the order two are treated.

## Main results

* `annulusExtension v`: the extension, for every `v : E → F`.
* `contDiff_annulusExtension`, `hasCompactSupport_annulusExtension`: for `C²` functions `v` it
  is `C²`, and it always has compact support.
* `annulusExtension_eq`: it agrees with `v` on `1 ≤ |y| ≤ 2`.

## How it works

We reflect across each of the two spheres. For the unit sphere, `q(y) = y/|y| - y` points from
`y` to the sphere along its ray, and the point `y + t q(y)` lies at distance
`(t - 1)(1 - |y|)` beyond the sphere. Inside the unit ball we put

`6 v(y + 2 q(y)) - 8 v(y + 3 q(y)) + 3 v(y + 4 q(y))`.

The coefficients `(6, -8, 3)` and the nodes `(2, 3, 4)` satisfy `∑ c = 1`, `∑ c t = 0` and
`∑ c t² = 0`, so this sum agrees with `v` to second order on the sphere
(`fderiv_fderiv_reflectionSum_eq`), and the glued function is `C²` (`contDiff_two_ite`). The
same sum with `q(y) = 2y/|y| - y` continues `v` beyond the sphere of radius two. For
`3/4 < |y| < 1` and for `2 < |y| < 9/4` the three reflected points lie in the open annulus, so
a cutoff that is one on the annulus and vanishes outside `3/4 < |y| < 9/4` leaves a function
that uses only values of `v` on the annulus. A second cutoff removes the singularity of
`y/|y|` at the origin, far from where the reflections are used.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology ContDiff

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## The two cutoffs -/

/-- A smooth function that vanishes for `|y| ≤ 1/4` and is one for `|y| ≥ 1/2`. -/
def originCut (y : E) : ℝ :=
  1 - (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : E)) y

/-- A smooth function that is one for `1 ≤ |y| ≤ 2` and vanishes for `|y| ≤ 3/4` and for
`|y| ≥ 9/4`. -/
def annulusCut (y : E) : ℝ :=
  (⟨2, 9 / 4, by norm_num, by norm_num⟩ : ContDiffBump (0 : E)) y *
    (1 - (⟨3 / 4, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : E)) y)

/-- The cutoff near the origin is smooth. -/
theorem contDiff_originCut : ContDiff ℝ ∞ (originCut (E := E)) :=
  contDiff_const.sub (ContDiffBump.contDiff _)

/-- The cutoff near the origin vanishes for `|y| ≤ 1/4`. -/
theorem originCut_eq_zero {y : E} (h : ‖y‖ ≤ 1 / 4) : originCut y = 0 := by
  rw [originCut, ContDiffBump.one_of_mem_closedBall _ (mem_closedBall_zero_iff.2 h), sub_self]

/-- The cutoff near the origin is one for `|y| ≥ 1/2`. -/
theorem originCut_eq_one {y : E} (h : 1 / 2 ≤ ‖y‖) : originCut y = 1 := by
  rw [originCut, ContDiffBump.zero_of_le_dist _ (by simpa [dist_zero_right] using h), sub_zero]

/-- The cutoff of the annulus is smooth. -/
theorem contDiff_annulusCut : ContDiff ℝ ∞ (annulusCut (E := E)) :=
  (ContDiffBump.contDiff _).mul (contDiff_const.sub (ContDiffBump.contDiff _))

/-- The cutoff of the annulus is one for `1 ≤ |y| ≤ 2`. -/
theorem annulusCut_eq_one {y : E} (h1 : 1 ≤ ‖y‖) (h2 : ‖y‖ ≤ 2) : annulusCut y = 1 := by
  rw [annulusCut, ContDiffBump.one_of_mem_closedBall _ (mem_closedBall_zero_iff.2 h2),
    ContDiffBump.zero_of_le_dist _ (by simpa [dist_zero_right] using h1), sub_zero, mul_one]

/-- The cutoff of the annulus vanishes for `|y| ≤ 3/4`. -/
theorem annulusCut_eq_zero_of_le {y : E} (h : ‖y‖ ≤ 3 / 4) : annulusCut y = 0 := by
  rw [annulusCut, ContDiffBump.one_of_mem_closedBall (⟨3 / 4, 1, by norm_num, by norm_num⟩ :
    ContDiffBump (0 : E)) (mem_closedBall_zero_iff.2 h), sub_self, mul_zero]

/-- The cutoff of the annulus vanishes for `|y| ≥ 9/4`. -/
theorem annulusCut_eq_zero_of_ge {y : E} (h : 9 / 4 ≤ ‖y‖) : annulusCut y = 0 := by
  rw [annulusCut, ContDiffBump.zero_of_le_dist (⟨2, 9 / 4, by norm_num, by norm_num⟩ :
    ContDiffBump (0 : E)) (by simpa [dist_zero_right] using h), zero_mul]

/-- The cutoff of the annulus has compact support. -/
theorem hasCompactSupport_annulusCut : HasCompactSupport (annulusCut (E := E)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (9 / 4))
    fun y hy ↦ ?_
  by_contra h
  exact hy (annulusCut_eq_zero_of_ge (not_le.1 fun h' ↦ h (mem_closedBall_zero_iff.2 h')).le)

/-! ## The shift to a sphere -/

/-- The vector from `y` to the sphere of radius `R` along the ray of `y`, `R y/|y| - y`, cut off
near the origin. -/
def sphereShift (R : ℝ) (y : E) : E :=
  originCut y • ((R * ‖y‖⁻¹) • y - y)

/-- The shift towards the sphere of radius `R` is smooth, the origin included. -/
theorem contDiff_sphereShift (R : ℝ) : ContDiff ℝ ∞ (sphereShift (E := E) R) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  rcases eq_or_ne y 0 with rfl | hy
  · refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
    rw [sphereShift, originCut_eq_zero (mem_ball_zero_iff.1 hz).le, zero_smul]
  · exact contDiff_originCut.contDiffAt.smul
      (((contDiffAt_const.mul ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy))).smul
        contDiffAt_id).sub contDiffAt_id)

/-- Away from the origin the shift is `R y/|y| - y`. -/
theorem sphereShift_eq {R : ℝ} {y : E} (hy : 1 / 2 ≤ ‖y‖) :
    sphereShift R y = (R * ‖y‖⁻¹) • y - y := by
  rw [sphereShift, originCut_eq_one hy, one_smul]

/-- The shift vanishes on its sphere. -/
theorem sphereShift_eq_zero {R : ℝ} (hR : 1 / 2 ≤ R) {y : E} (hy : ‖y‖ = R) :
    sphereShift R y = 0 := by
  have hR0 : R ≠ 0 := by linarith
  rw [sphereShift_eq (hy ▸ hR), hy, mul_inv_cancel₀ hR0, one_smul, sub_self]

/-- Away from the origin the shifted point is a multiple of `y`. -/
theorem add_smul_sphereShift {R : ℝ} (t : ℝ) {y : E} (hy : 1 / 2 ≤ ‖y‖) :
    y + t • sphereShift R y = ((1 - t) + t * R * ‖y‖⁻¹) • y := by
  rw [sphereShift_eq hy]
  module

/-! ## The coefficients -/

/-- The coefficients `(6, -8, 3)` of the reflection. -/
def reflCoeff : Fin 3 → ℝ := ![6, -8, 3]

/-- The nodes `(2, 3, 4)` of the reflection. -/
def reflNode : Fin 3 → ℝ := ![2, 3, 4]

/-- The moment condition of order zero: the coefficients add up to one. -/
theorem sum_reflCoeff : ∑ j, reflCoeff j = 1 := by
  simp [Fin.sum_univ_three, reflCoeff]
  norm_num

/-- The moment condition of order one. -/
theorem sum_reflCoeff_mul_reflNode : ∑ j, reflCoeff j * reflNode j = 0 := by
  simp [Fin.sum_univ_three, reflCoeff, reflNode]
  norm_num

/-- The moment condition of order two. -/
theorem sum_reflCoeff_mul_reflNode_sq : ∑ j, reflCoeff j * reflNode j ^ 2 = 0 := by
  simp [Fin.sum_univ_three, reflCoeff, reflNode]
  norm_num

/-! ## The extension -/

/-- The reflection of `v` across the sphere of radius `R`:
`6 v(y + 2 q) - 8 v(y + 3 q) + 3 v(y + 4 q)` with `q = sphereShift R y`. -/
def sphereReflection (R : ℝ) (v : E → F) : E → F :=
  reflectionSum Finset.univ reflCoeff reflNode (sphereShift R) v

/-- The reflection of a `C²` function across a sphere is `C²`. -/
theorem contDiff_sphereReflection {v : E → F} (hv : ContDiff ℝ 2 v) (R : ℝ) :
    ContDiff ℝ 2 (sphereReflection R v) := by
  have hq : ContDiff ℝ 2 (sphereShift (E := E) R) := (contDiff_sphereShift R).of_le (by simp)
  have h (j : Fin 3) :
      ContDiff ℝ 2 (fun y : E ↦ reflCoeff j • v (y + reflNode j • sphereShift R y)) :=
    (hv.comp (contDiff_id.add (hq.const_smul (reflNode j)))).const_smul (reflCoeff j)
  change ContDiff ℝ 2
    (fun y : E ↦ ∑ j ∈ Finset.univ, reflCoeff j • v (y + reflNode j • sphereShift R y))
  exact ContDiff.sum fun j _ ↦ h j

/-- The function that is `v` on the annulus, its reflection across the unit sphere inside, and
its reflection across the sphere of radius two outside. -/
def annulusGlue (v : E → F) (y : E) : F :=
  if 1 ≤ ‖y‖ then (if -2 ≤ -‖y‖ then v y else sphereReflection 2 v y)
  else sphereReflection 1 v y

/-- **The extension of `v` from the annulus `1 ≤ |y| ≤ 2`**: the glued reflections, cut off
outside `3/4 < |y| < 9/4`. -/
def annulusExtension (v : E → F) (y : E) : F :=
  annulusCut y • annulusGlue v y

/-- The function glued from `v` and its two reflections is `C²`. -/
theorem contDiff_annulusGlue {v : E → F} (hv : ContDiff ℝ 2 v) : ContDiff ℝ 2 (annulusGlue v) := by
  have hq (R : ℝ) : ContDiff ℝ 2 (sphereShift (E := E) R) :=
    (contDiff_sphereShift R).of_le (by simp)
  have hqd (R : ℝ) : Differentiable ℝ (sphereShift (E := E) R) :=
    (hq R).differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  -- across the sphere of radius two
  have houter : ContDiff ℝ 2
      (fun y : E ↦ if -2 ≤ -‖y‖ then v y else sphereReflection 2 v y) := by
    have h0 (p : E) (hp : -‖p‖ = -2) : sphereShift (E := E) 2 p = 0 :=
      sphereShift_eq_zero (by norm_num) (neg_inj.1 hp)
    exact contDiff_two_ite (contDiff_sphereReflection hv 2) hv continuous_norm.neg (-2)
      (fun p hp ↦ (reflectionSum_eq (h0 p hp) sum_reflCoeff).symm)
      (fun p hp ↦ (fderiv_reflectionSum_eq hvd (hqd 2 p) (h0 p hp) sum_reflCoeff
        sum_reflCoeff_mul_reflNode).symm)
      (fun p hp ↦ (fderiv_fderiv_reflectionSum_eq hv (hq 2) (h0 p hp) sum_reflCoeff
        sum_reflCoeff_mul_reflNode sum_reflCoeff_mul_reflNode_sq).symm)
  -- across the unit sphere, where the outer function is `v`
  have hev (p : E) (hp : ‖p‖ = 1) :
      (fun y : E ↦ if -2 ≤ -‖y‖ then v y else sphereReflection 2 v y) =ᶠ[𝓝 p] v := by
    filter_upwards [(continuous_norm.tendsto p).eventually
      (eventually_lt_nhds (by rw [hp]; norm_num : ‖p‖ < 2))] with y hy
    rw [ite_eq_left (by linarith)]
  have h1 (p : E) (hp : ‖p‖ = 1) : sphereShift (E := E) 1 p = 0 :=
    sphereShift_eq_zero (by norm_num) hp
  exact contDiff_two_ite (contDiff_sphereReflection hv 1) houter continuous_norm 1
    (fun p hp ↦ (hev p hp).eq_of_nhds.trans (reflectionSum_eq (h1 p hp) sum_reflCoeff).symm)
    (fun p hp ↦ (hev p hp).fderiv_eq.trans (fderiv_reflectionSum_eq hvd (hqd 1 p) (h1 p hp)
      sum_reflCoeff sum_reflCoeff_mul_reflNode).symm)
    (fun p hp ↦ (hev p hp).fderiv.fderiv_eq.trans (fderiv_fderiv_reflectionSum_eq hv (hq 1)
      (h1 p hp) sum_reflCoeff sum_reflCoeff_mul_reflNode sum_reflCoeff_mul_reflNode_sq).symm)

/-- The extension is `C²`. -/
theorem contDiff_annulusExtension {v : E → F} (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (annulusExtension v) :=
  (contDiff_annulusCut.of_le (by simp)).smul (contDiff_annulusGlue hv)

/-- The extension has compact support. -/
theorem hasCompactSupport_annulusExtension (v : E → F) :
    HasCompactSupport (annulusExtension v) :=
  hasCompactSupport_annulusCut.smul_right

/-- The extension agrees with `v` on the closed annulus. -/
theorem annulusExtension_eq (v : E → F) {y : E} (h1 : 1 ≤ ‖y‖) (h2 : ‖y‖ ≤ 2) :
    annulusExtension v y = v y := by
  rw [annulusExtension, annulusCut_eq_one h1 h2, one_smul, annulusGlue, ite_eq_left h1,
    ite_eq_left (by linarith)]

/-! ## The extension on each region -/

/-- In the open annulus the extension is `v`. -/
theorem annulusExtension_eventuallyEq_mid (v : E → F) {y : E} (h1 : 1 < ‖y‖) (h2 : ‖y‖ < 2) :
    annulusExtension v =ᶠ[𝓝 y] v := by
  filter_upwards [(continuous_norm.tendsto y).eventually (eventually_gt_nhds h1),
    (continuous_norm.tendsto y).eventually (eventually_lt_nhds h2)] with z hz1 hz2
  exact annulusExtension_eq v hz1.le hz2.le

/-- Inside the unit ball the extension is the cut-off reflection across the unit sphere. -/
theorem annulusExtension_eventuallyEq_inner (v : E → F) {y : E} (h : ‖y‖ < 1) :
    annulusExtension v =ᶠ[𝓝 y] fun z ↦ annulusCut z • sphereReflection 1 v z := by
  filter_upwards [(continuous_norm.tendsto y).eventually (eventually_lt_nhds h)] with z hz
  rw [annulusExtension, annulusGlue, ite_eq_right (not_le.2 hz)]

/-- Outside the ball of radius two the extension is the cut-off reflection across its sphere. -/
theorem annulusExtension_eventuallyEq_outer (v : E → F) {y : E} (h : 2 < ‖y‖) :
    annulusExtension v =ᶠ[𝓝 y] fun z ↦ annulusCut z • sphereReflection 2 v z := by
  filter_upwards [(continuous_norm.tendsto y).eventually (eventually_gt_nhds h)] with z hz
  rw [annulusExtension, annulusGlue, ite_eq_left (by linarith), ite_eq_right (by linarith)]

/-- Outside `3/4 ≤ |y| ≤ 9/4` the extension vanishes. -/
theorem annulusExtension_eventuallyEq_zero (v : E → F) {y : E} (h : ‖y‖ < 3 / 4 ∨ 9 / 4 < ‖y‖) :
    annulusExtension v =ᶠ[𝓝 y] 0 := by
  rcases h with h | h
  · filter_upwards [(continuous_norm.tendsto y).eventually (eventually_lt_nhds h)] with z hz
    rw [annulusExtension, annulusCut_eq_zero_of_le hz.le, zero_smul, Pi.zero_apply]
  · filter_upwards [(continuous_norm.tendsto y).eventually (eventually_gt_nhds h)] with z hz
    rw [annulusExtension, annulusCut_eq_zero_of_ge hz.le, zero_smul, Pi.zero_apply]

end PDE.Analysis
