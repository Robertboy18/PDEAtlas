/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Convex.Deriv
import CAS.ExactTactic

/-!
# Strong convexity from a Hessian lower bound

Restrict a twice differentiable function to a line and subtract the quadratic
with the prescribed lower curvature. The one-dimensional second derivative
criterion for convexity gives mathlib's `StrongConvexOn` inequality with the
same constant. The argument does not differentiate the norm.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A global lower bound on the Hessian quadratic form implies strong
convexity with the same constant. Continuity of the Hessian is not needed. -/
theorem strongConvexOn_univ_of_hessian_lower_bound
    {f : E → ℝ} (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (fderiv ℝ f)) {θ : ℝ}
    (hbound : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    StrongConvexOn (Set.univ : Set E) θ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let v := y - x
  let c := θ * ‖v‖ ^ 2
  let F : ℝ → ℝ := fun s ↦ f (x + s • v) - c / 2 * s ^ 2
  let F' : ℝ → ℝ := fun s ↦ fderiv ℝ f (x + s • v) v - c * s
  let F'' : ℝ → ℝ := fun s ↦ fderiv ℝ (fderiv ℝ f) (x + s • v) v v - c
  have hline (s : ℝ) : HasDerivAt (fun r : ℝ ↦ x + r • v) v s := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id s).smul_const v).const_add x
  have hF (s : ℝ) : HasDerivAt F (F' s) s := by
    have hquad : HasDerivAt (fun r : ℝ ↦ c / 2 * r ^ 2) (c * s) s := by
      cas
    exact ((hf _).hasFDerivAt.comp_hasDerivAt s (hline s)).sub hquad
  have hF' (s : ℝ) : HasDerivAt F' (F'' s) s := by
    have hlinear : HasDerivAt (fun r : ℝ ↦ c * r) c s := by
      cas
    have h := ((hdf _).hasFDerivAt.comp_hasDerivAt s (hline s)).clm_apply
      (hasDerivAt_const s v)
    simpa only [ContinuousLinearMap.map_zero, add_zero, Function.comp_apply,
      F', F''] using h.fun_sub hlinear
  have hconv : ConvexOn ℝ Set.univ F :=
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun s _ ↦ (hF s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hF s).hasDerivWithinAt)
      (fun s _ ↦ (hF' s).hasDerivWithinAt)
      (fun s _ ↦ sub_nonneg.mpr (hbound (x + s • v) v))
  have hsegment := hconv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  have hxy : x + b • v = a • x + b • y := by
    dsimp only [v]
    calc
      x + b • (y - x) = (1 - b) • x + b • y := by
        rw [sub_smul, one_smul, smul_sub]
        abel
      _ = a • x + b • y := by rw [show 1 - b = a by linarith]
  have hv : ‖v‖ = ‖x - y‖ := norm_sub_rev y x
  have hone : x + v = y := by dsimp only [v]; abel
  simp only [F, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero,
    zero_pow (by decide : 2 ≠ 0), sub_zero, one_smul, hone,
    one_pow] at hsegment
  rw [hxy] at hsegment
  dsimp only [c] at hsegment
  rw [hv] at hsegment
  simp only [smul_eq_mul]
  have haeq : a = 1 - b := by linarith
  rw [haeq] at hsegment ⊢
  nlinarith

/-- A C2 density on a product has strongly convex slices when its Hessian
in the second variable has the corresponding uniform lower bound. -/
theorem strongConvexOn_slice_of_hessian_lower_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} {f : X × E → ℝ}
    (hf : ContDiffOn ℝ 2 f (s ×ˢ Set.univ)) {x : X} (hx : x ∈ s) {θ : ℝ}
    (hbound : ∀ y v, θ * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ (fun z ↦ f (x, z))) y v v) :
    StrongConvexOn Set.univ θ (fun y ↦ f (x, y)) := by
  have hs : ContDiff ℝ 2 (fun y ↦ f (x, y)) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hx, Set.mem_univ _⟩))
  have hd : ContDiff ℝ 1 (fderiv ℝ (fun y ↦ f (x, y))) :=
    hs.fderiv_right (by norm_num)
  exact strongConvexOn_univ_of_hessian_lower_bound
    (hs.differentiable (by norm_num)) hd.differentiable_one hbound

end PDE.Analysis
