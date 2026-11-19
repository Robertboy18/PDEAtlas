/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Parabolic.Quadratic
public import PDE.Analysis.Calculus.PartialGradient
public import PDE.Analysis.LinearAlgebra.Determinant.Block
import CAS.ExactTactic

/-!
# The parabolic contact Jacobian

The vertex map has Jacobian
`det (I + κ⁻¹ D²ₓu) * (1 - κ⁻¹ uₜ)`. Row elimination cancels the
mixed derivatives; neither spatial invertibility nor a second time derivative
enters the determinant formula. Differentiability of the partial gradient is
needed for this smooth contact-map step.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Differentiating the space and height equations gives a block derivative.
Its second row is a scalar time derivative minus a multiple of the first row. -/
theorem hasFDerivAt_parabolicQuadraticContactMap
    {u : E → ℝ → ℝ} {p : E × ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) p)
    (hg : DifferentiableAt ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p)
    (κ : ℝ) :
    let g := ∇ (fun x ↦ u x p.2) p.1
    let Y := ContinuousLinearMap.fst ℝ E ℝ +
      κ⁻¹ • fderiv ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p
    HasFDerivAt (parabolicQuadraticContactMap u κ)
      (Y.prod ((1 - κ⁻¹ * deriv (u p.1) p.2) • ContinuousLinearMap.snd ℝ E ℝ -
        κ⁻¹ • (innerSL ℝ g).comp Y)) p := by
  dsimp only
  let Y := ContinuousLinearMap.fst ℝ E ℝ +
    κ⁻¹ • fderiv ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p
  let y := fun q : E × ℝ ↦ quadraticContactMap (fun x ↦ u x q.2) κ q.1
  have hy : HasFDerivAt y Y p := hasFDerivAt_fst.add (hg.hasFDerivAt.const_smul κ⁻¹)
  have hq := (hasFDerivAt_fst.sub hy).norm_sq.const_mul (κ / 2)
  have hs := hasFDerivAt_snd.sub ((hu.hasFDerivAt.add hq).const_mul κ⁻¹)
  have hmap := hy.prodMk hs
  convert hmap using 1
  · rfl
  · apply congrArg (ContinuousLinearMap.prod Y)
    apply ContinuousLinearMap.ext
    intro v
    have hfull := fderiv_prod_apply_eq_gradient_fst_add hu v
    rw [fderiv_eq_deriv_mul] at hfull
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', add_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_fst', Pi.sub_apply, smul_eq_mul]
    rw [hfull]
    dsimp only [Function.uncurry]
    have hdisp : p.1 - y p = -(κ⁻¹ • ∇ (fun x ↦ u x p.2) p.1) := by
      dsimp [y, quadraticContactMap]
      abel
    rw [hdisp, inner_neg_left, real_inner_smul_left, inner_sub_right]
    have hYv : Y v = v.1 +
        κ⁻¹ • fderiv ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p v := rfl
    rw [← hYv]
    by_cases hκ : κ = 0
    · simp [hκ]
    · cas using hκ

/-- The Jacobian determinant splits into its spatial factor and its time
factor. Mixed derivatives cancel even when the spatial factor is singular. -/
theorem det_fderiv_parabolicQuadraticContactMap [FiniteDimensional ℝ E]
    {u : E → ℝ → ℝ} {p : E × ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) p)
    (hg : DifferentiableAt ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p)
    (κ : ℝ) :
    (fderiv ℝ (parabolicQuadraticContactMap u κ) p).det =
      (fderiv ℝ (quadraticContactMap (fun x ↦ u x p.2) κ) p.1).det *
        (1 - κ⁻¹ * deriv (u p.1) p.2) := by
  let Y := ContinuousLinearMap.fst ℝ E ℝ +
    κ⁻¹ • fderiv ℝ (fun q : E × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p
  have hy : HasFDerivAt
      (fun q : E × ℝ ↦ quadraticContactMap (fun x ↦ u x q.2) κ q.1) Y p :=
    hasFDerivAt_fst.add (hg.hasFDerivAt.const_smul κ⁻¹)
  have hspace := (hy.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv
  dsimp only [Function.comp_def] at hspace
  rw [(hasFDerivAt_parabolicQuadraticContactMap hu hg κ).fderiv, hspace]
  simpa [ContinuousLinearMap.det, Y, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_add, LinearMap.add_comp, smul_add, LinearMap.det_ring] using
    det_prod_sub_comp Y.toLinearMap
    (κ⁻¹ • (innerSL ℝ (∇ (fun x ↦ u x p.2) p.1)).toLinearMap)
    ((1 - κ⁻¹ * deriv (u p.1) p.2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

end PDE.Analysis
