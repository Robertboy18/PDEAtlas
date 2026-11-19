/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TestFunctions
import CAS.ExactTactic

/-!
# Normal boundary-cutoff estimates

The derivative lives in the strip between one and two cutoff scales. A test vanishing
on the boundary grows linearly in the normal coordinate, cancelling the inverse-scale
derivative bound. These pointwise estimates are independent of the reflection operator.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace.Extension.GraphSpace.HalfSpace

open Set MeasureTheory Function Filter TopologicalSpace
open SobolevSpace.GraphSpace
open _root_.SobolevSpace.HalfSpace
open scoped ENNReal Topology Distributions RealInnerProductSpace

variable (n : ℕ) [Fact (0 < n)]

/-- Below the transition strip, the boundary cutoff is locally zero. -/
theorem partialDeriv_cutoffAway_last_eq_zero_of_last_lt {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx : x (PDE.Common.lastIndex (n := n)) < δ) :
    (∂[PDE.Common.lastIndex (n := n)]
        (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x = 0 := by
  have heq : _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [(isOpen_lt (PiLp.continuous_apply 2 _ _) continuous_const).mem_nhds hx]
      with y hy using cutoffAway_eq_zero_of_last_le (n := n) hδ (le_of_lt hy)
  simp [partialDeriv, heq.fderiv_eq]

/-- Above the transition strip, the boundary cutoff is locally one. -/
theorem partialDeriv_cutoffAway_last_eq_zero_of_two_mul_lt_last
    {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx : 2 * δ < x (PDE.Common.lastIndex (n := n))) :
    (∂[PDE.Common.lastIndex (n := n)]
        (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x = 0 := by
  have heq : _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ =ᶠ[𝓝 x] fun _ ↦ 1 := by
    filter_upwards [(isOpen_lt continuous_const (PiLp.continuous_apply 2 _ _)).mem_nhds hx]
      with y hy using cutoffAway_eq_one_of_two_mul_le_last (n := n) hδ (le_of_lt hy)
  simp [partialDeriv, heq.fderiv_eq]

/-- The smooth transition has a uniformly bounded derivative on its transition interval. -/
theorem exists_bound_fderiv_smoothTransition_on_Icc :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ (Set.Icc (0 : ℝ) 1), ‖fderiv ℝ Real.smoothTransition t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).continuous_fderiv (by simp)).continuousOn
  exact ⟨C, (norm_nonneg _).trans (hC 0 (left_mem_Icc.2 zero_le_one)), hC⟩

/-- Inside the transition strip, the cutoff derivative is bounded by the inverse strip width. -/
theorem abs_partialDeriv_cutoffAway_last_le {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n}
    (hx₁ : δ ≤ x (PDE.Common.lastIndex (n := n)))
    (hx₂ : x (PDE.Common.lastIndex (n := n)) ≤ 2 * δ) :
    |(∂[PDE.Common.lastIndex (n := n)]
        (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x| ≤
      (Classical.choose exists_bound_fderiv_smoothTransition_on_Icc) * (1 / δ) := by
  set i := PDE.Common.lastIndex (n := n)
  have hC := (Classical.choose_spec exists_bound_fderiv_smoothTransition_on_Icc).2
  have hfun : _root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ =
      Real.smoothTransition ∘ fun y ↦ (EuclideanSpace.proj (𝕜 := ℝ) i y - δ) * δ⁻¹ := by
    funext y
    simp [_root_.SobolevSpace.HalfSpace.cutoffAway, i, div_eq_mul_inv]
  -- the chain rule through the affine map `y ↦ (yₙ - δ) / δ`, of derivative `δ⁻¹ • proj`
  have hst := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hcut := (hst _).hasFDerivAt.comp x <|
    HasFDerivAt.mul_const ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.sub_const δ) δ⁻¹
  have hmem : (x i - δ) / δ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hδ.le, (div_le_one hδ).2 (by linarith)⟩
  rw [partialDeriv, hfun, hcut.fderiv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
  refine (fderiv ℝ Real.smoothTransition _).le_of_opNorm_le_of_le
    (hC _ (by simpa [div_eq_mul_inv] using hmem)) ?_
  simp [abs_of_pos hδ]

/-- A test vanishing on the flat boundary grows at most linearly in the normal distance.
The constant is any global bound for its normal derivative. -/
theorem abs_testFunction_le_last_of_zero_on_boundary
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : ∀ x : ℝ^n, x (PDE.Common.lastIndex (n := n)) = 0 → ψ x = 0)
    {Mψ : ℝ} (hM : ∀ x, |(∂[PDE.Common.lastIndex (n := n)] ψ.toFun) x| ≤ Mψ)
    {x : ℝ^n} (hx : x ∈ ℝ^n₊) :
    |ψ x| ≤ Mψ * x (PDE.Common.lastIndex (n := n)) := by
  set i := PDE.Common.lastIndex (n := n)
  have hx0 : 0 ≤ x i := le_of_lt hx
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  -- the normal segment from the boundary point below `x` up to `x`
  let g : ℝ → ℝ^n := fun t ↦ x + (t - x i) • e
  have hg (t : ℝ) : HasDerivAt g e t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s - x i) 1 t := by
      cas
    simpa [g] using (h1.smul_const e).const_add x
  have hDeriv : ∀ t ∈ Set.Icc (0 : ℝ) (x i),
      HasDerivWithinAt (⇑ψ ∘ g) ((∂[i] (⇑ψ)) (g t)) (Set.Icc (0 : ℝ) (x i)) t := fun t _ ↦
    ((ψ.contDiff.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (hg t)).hasDerivWithinAt
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment' hDeriv
    (fun t _ ↦ by simpa only [Real.norm_eq_abs, TestFunction.toFun_eq_coe] using hM (g t))
    (x i) ⟨hx0, le_rfl⟩
  have hg0 : ψ (g 0) = 0 := hψ _ (by simp [g, e])
  have hgx : g (x i) = x := by simp [g]
  simpa [hgx, hg0, Real.norm_eq_abs, abs_of_nonneg hx0] using hseg

/-- Linear boundary vanishing cancels the inverse scale of the cutoff derivative. -/
theorem abs_partialDeriv_cutoffAway_mul_testFunction_le
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : ∀ x : ℝ^n, x (PDE.Common.lastIndex (n := n)) = 0 → ψ x = 0)
    {Mψ : ℝ} (hMψ0 : 0 ≤ Mψ)
    (hM : ∀ x, |(∂[PDE.Common.lastIndex (n := n)] ψ.toFun) x| ≤ Mψ)
    {δ : ℝ} (hδ : 0 < δ) {x : ℝ^n} (hx : x ∈ ℝ^n₊) :
    |(∂[PDE.Common.lastIndex (n := n)]
      (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) δ)) x * ψ x| ≤
        2 * Classical.choose exists_bound_fderiv_smoothTransition_on_Icc * Mψ := by
  set i := PDE.Common.lastIndex (n := n)
  set C := Classical.choose exists_bound_fderiv_smoothTransition_on_Icc
  have hC0 : 0 ≤ C := (Classical.choose_spec exists_bound_fderiv_smoothTransition_on_Icc).1
  have hconst : 0 ≤ 2 * C * Mψ := mul_nonneg (mul_nonneg zero_le_two hC0) hMψ0
  rw [abs_mul]
  rcases lt_or_ge (x i) δ with hlt | h₁
  · rwa [partialDeriv_cutoffAway_last_eq_zero_of_last_lt n hδ hlt, abs_zero, zero_mul]
  rcases lt_or_ge (2 * δ) (x i) with hgt | h₂
  · rwa [partialDeriv_cutoffAway_last_eq_zero_of_two_mul_lt_last n hδ hgt, abs_zero, zero_mul]
  have hCδ : 0 ≤ C * (1 / δ) := mul_nonneg hC0 (by positivity)
  calc _ ≤ C * (1 / δ) * (Mψ * x i) :=
        mul_le_mul (abs_partialDeriv_cutoffAway_last_le n hδ h₁ h₂)
          (abs_testFunction_le_last_of_zero_on_boundary n ψ hψ hM hx) (abs_nonneg _) hCδ
    _ ≤ C * (1 / δ) * (Mψ * (2 * δ)) := by gcongr
    _ = 2 * C * Mψ := by field_simp

/-- At a fixed interior point, the normal cutoff derivative eventually vanishes. -/
theorem eventually_partialDeriv_cutoffAway_eq_zero {x : ℝ^n} (hx : x ∈ ℝ^n₊) :
    ∀ᶠ m in atTop, (∂[PDE.Common.lastIndex (n := n)]
      (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x = 0 := by
  have hxpos : 0 < x (PDE.Common.lastIndex (n := n)) := hx
  have hlt := tendsto_δSeq.eventually (Iio_mem_nhds (show
    0 < x (PDE.Common.lastIndex (n := n)) / 4 by positivity))
  filter_upwards [hlt] with m hm
  exact partialDeriv_cutoffAway_last_eq_zero_of_two_mul_lt_last n (δSeq_pos m)
    (by linarith)

end SobolevSpace.Extension.GraphSpace.HalfSpace
