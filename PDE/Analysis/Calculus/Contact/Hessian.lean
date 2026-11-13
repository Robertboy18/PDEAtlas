/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Quadratic
public import PDE.Analysis.Calculus.Gradient
public import PDE.Analysis.Calculus.SecondDirectionalDerivative
public import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Hessians at lower contacts

Local `C²` regularity suffices for differentiating the gradient. At a local
minimum its derivative is positive: symmetry follows from mixed derivatives,
and the quadratic form is nonnegative by restriction to affine lines.
Consequently the quadratic contact map has positive Jacobian at every interior
lower contact, without a global convexity assumption.
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open scoped Topology ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A local minimum has a positive Hessian operator wherever it is `C²`. -/
theorem isPositive_fderiv_gradient_of_isLocalMin {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hmin : IsLocalMin u x) :
    (fderiv ℝ (∇ u) x).toLinearMap.IsPositive := by
  refine ⟨?_, ?_⟩
  · intro v w
    change ⟪fderiv ℝ (∇ u) x v, w⟫ = ⟪v, fderiv ℝ (∇ u) x w⟫
    rw [show ⟪v, fderiv ℝ (∇ u) x w⟫ = ⟪fderiv ℝ (∇ u) x w, v⟫
      from real_inner_comm _ _, inner_fderiv_gradient_at hu, inner_fderiv_gradient_at hu]
    exact (hu.isSymmSndFDerivAt (by norm_num)).eq v w
  · intro v
    change 0 ≤ ⟪fderiv ℝ (∇ u) x v, v⟫
    rw [inner_fderiv_gradient_at hu]
    have h := secondDirectionalDerivative_nonpos_at_localMax hmin.neg hu.continuousAt.neg v
    rw [secondDirectionalDerivative_neg, secondDirectionalDerivative_eq_fderiv hu] at h
    exact neg_nonpos.mp h

/-- The Jacobian of the quadratic contact map is identity plus scaled Hessian. -/
theorem hasFDerivAt_quadraticContactMap {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (κ : ℝ) :
    HasFDerivAt (quadraticContactMap u κ)
      (ContinuousLinearMap.id ℝ E + κ⁻¹ • fderiv ℝ (∇ u) x) x :=
  (hasFDerivAt_id x).add
    (((contDiffAt_gradient (m := 1) hu).differentiableAt_one).hasFDerivAt.const_smul κ⁻¹)

/-- The Hessian of a quadratic tilt differs from that of the function by `κ I`. -/
theorem fderiv_gradient_quadraticTilt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (κ : ℝ) (y : E) :
    fderiv ℝ (∇ (quadraticTilt u κ y)) x =
      fderiv ℝ (∇ u) x + κ • ContinuousLinearMap.id ℝ E := by
  have hnear : ∇ (quadraticTilt u κ y) =ᶠ[𝓝 x]
      fun z ↦ ∇ u z + κ • (z - y) := by
    filter_upwards [hu.eventually (by simp)] with z hz
    exact gradient_quadraticTilt (hz.differentiableAt (by norm_num)) κ y
  rw [hnear.fderiv_eq]
  exact (((contDiffAt_gradient (m := 1) hu).differentiableAt_one).hasFDerivAt.add
    (((hasFDerivAt_id x).sub_const y).const_smul κ)).fderiv

/-- Interior lower contacts have positive Jacobian. This uses local minimality,
not convexity of the function on its domain. -/
theorem isPositive_fderiv_quadraticContactMap
    {u : E → ℝ} {κ : ℝ} {x y : E} (hu : ContDiffAt ℝ 2 u x) (hκ : 0 < κ)
    (hmin : IsLocalMin (quadraticTilt u κ y) x) :
    (fderiv ℝ (quadraticContactMap u κ) x).toLinearMap.IsPositive := by
  have hq : ContDiffAt ℝ 2 (quadraticTilt u κ y) x :=
    hu.add (contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ))
  have hpositive := (isPositive_fderiv_gradient_of_isLocalMin hq hmin).smul_of_nonneg
    (le_of_lt (inv_pos.mpr hκ))
  rw [fderiv_gradient_quadraticTilt hu] at hpositive
  convert hpositive using 1
  rw [(hasFDerivAt_quadraticContactMap hu κ).fderiv]
  ext v
  simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_add, smul_smul,
    inv_mul_cancel₀ hκ.ne', one_smul]
  exact add_comm _ _

end PDE.Analysis
