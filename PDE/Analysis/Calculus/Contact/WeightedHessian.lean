/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Hessian
public import PDE.Analysis.Calculus.HessianTrace

/-!
# Weighted Hessian bounds at lower contacts

A lower quadratic contact identifies the gradient with its displacement and
makes the contact Jacobian positive. A lower bound on a weighting operator and
an upper bound on the weighted Hessian then control the trace of that Jacobian.
The same estimate applies to elliptic and parabolic differential inequalities;
no equation or coefficient field is part of this analytic statement.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A weighted Hessian inequality bounds the positive contact Jacobian's trace.
The weight need not be symmetric, and the lower quadratic-form bound may have
either sign. -/
theorem mul_trace_fderiv_quadraticContactMap_le
    (A : E →ₗ[ℝ] E) (b : E)
    {u : E → ℝ} {x y : E} {κ α τ B R f : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hκ : 0 < κ)
    (hell : ∀ v : E, α * ‖v‖ ^ 2 ≤ ⟪v, A v⟫)
    (htrace : LinearMap.trace ℝ E A ≤ τ) (hdrift : ‖b‖ ≤ B) (hdist : ‖y - x‖ ≤ R)
    (hres : LinearMap.trace ℝ E (A.comp (fderiv ℝ (∇ u) x).toLinearMap) ≤
      fderiv ℝ u x b + f)
    (hmin : IsLocalMin (quadraticTilt u κ y) x) :
    α * LinearMap.trace ℝ E (fderiv ℝ (quadraticContactMap u κ) x).toLinearMap ≤
      τ + B * R + κ⁻¹ * f := by
  have hpositive := isPositive_fderiv_quadraticContactMap hu hκ hmin
  have hlower := mul_trace_le_trace_comp hpositive hell
  have hvertex := quadraticContactMap_eq_of_isLocalMin hκ.ne'
    (hu.differentiableAt (by norm_num)) hmin
  have hgrad : κ⁻¹ • ∇ u x = y - x := by
    rw [eq_sub_iff_add_eq]
    simpa only [quadraticContactMap, add_comm] using hvertex
  have hinner : κ⁻¹ * fderiv ℝ u x b = ⟪y - x, b⟫ := by
    rw [← hgrad, real_inner_smul_left]
    congr 1
    exact (InnerProductSpace.toDual_symm_apply).symm
  have hweighted : LinearMap.trace ℝ E
      (A.comp (fderiv ℝ (quadraticContactMap u κ) x).toLinearMap) =
        LinearMap.trace ℝ E A +
          κ⁻¹ * LinearMap.trace ℝ E (A.comp (fderiv ℝ (∇ u) x).toLinearMap) := by
    rw [(hasFDerivAt_quadraticContactMap hu κ).fderiv]
    change LinearMap.trace ℝ E
      (A.comp (LinearMap.id + κ⁻¹ • (fderiv ℝ (∇ u) x).toLinearMap)) = _
    rw [LinearMap.comp_add, LinearMap.comp_id, LinearMap.comp_smul, map_add, map_smul,
      smul_eq_mul]
  apply hlower.trans
  rw [hweighted]
  calc
    LinearMap.trace ℝ E A +
        κ⁻¹ * LinearMap.trace ℝ E (A.comp (fderiv ℝ (∇ u) x).toLinearMap) ≤
        τ + κ⁻¹ * (fderiv ℝ u x b + f) :=
      add_le_add htrace (mul_le_mul_of_nonneg_left hres (inv_nonneg.mpr hκ.le))
    _ = τ + ⟪y - x, b⟫ + κ⁻¹ * f := by rw [mul_add, hinner, add_assoc]
    _ ≤ τ + ‖y - x‖ * ‖b‖ + κ⁻¹ * f :=
      add_le_add (add_le_add le_rfl (real_inner_le_norm _ _)) le_rfl
    _ ≤ τ + R * B + κ⁻¹ * f :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul hdist hdrift (norm_nonneg _) ((norm_nonneg _).trans hdist))) le_rfl
    _ = τ + B * R + κ⁻¹ * f := by rw [mul_comm R B]

end PDE.Analysis
