/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import CAS.ExactTactic

/-!
# Lower quadratic contacts

Minimizing `u x + κ / 2 * ‖x - y‖²` slides a paraboloid of aperture `κ` below `u`.
At an interior minimum its vertex is `x + κ⁻¹ • gradient u x`. Keeping the full
supporting inequality makes the contact set compact on any compact region where
the function and its gradient are continuous.
-/

@[expose] public section

open scoped Gradient

noncomputable section

namespace PDE.Analysis

open Set Metric
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The function minimized when a paraboloid with vertex `y` is slid from below. -/
def quadraticTilt (u : E → ℝ) (κ : ℝ) (y x : E) : ℝ :=
  u x + κ / 2 * ‖x - y‖ ^ 2

/-- The vertex associated with a differentiable lower quadratic contact. -/
def quadraticContactMap (u : E → ℝ) (κ : ℝ) (x : E) : E :=
  x + κ⁻¹ • ∇ u x

/-- Contacts in `K`, supported over `S`, whose vertices belong to `Y`. -/
def quadraticContactSet (u : E → ℝ) (κ : ℝ) (S K Y : Set E) : Set E :=
  {x | x ∈ K ∧ quadraticContactMap u κ x ∈ Y ∧
    IsMinOn (quadraticTilt u κ (quadraticContactMap u κ x)) S x}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Continuous functions have continuous quadratic tilts on the same set. -/
theorem continuousOn_quadraticTilt {u : E → ℝ} {S : Set E}
    (hu : ContinuousOn u S) (κ : ℝ) (y : E) :
    ContinuousOn (quadraticTilt u κ y) S :=
  hu.add (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).norm.pow 2))

/-- Compactness of the contact set uses continuity only where the contacts lie.
No injectivity of the vertex map is required. -/
theorem isCompact_quadraticContactSet {u : E → ℝ} {κ : ℝ} {S K Y : Set E}
    (hK : IsCompact K) (hY : IsClosed Y) (hu : ContinuousOn u K)
    (hgrad : ContinuousOn (∇ u) K) :
    IsCompact (quadraticContactSet u κ S K Y) := by
  have hF : ContinuousOn (quadraticContactMap u κ) K :=
    continuousOn_id.add (continuousOn_const.smul hgrad)
  have hleft : ContinuousOn
      (fun x ↦ quadraticTilt u κ (quadraticContactMap u κ x) x) K :=
    hu.add (continuousOn_const.mul ((continuousOn_id.sub hF).norm.pow 2))
  have hright (z : E) : ContinuousOn
      (fun x ↦ quadraticTilt u κ (quadraticContactMap u κ x) z) K :=
    continuousOn_const.add
      (continuousOn_const.mul ((continuousOn_const.sub hF).norm.pow 2))
  have hclosed : IsClosed (quadraticContactSet u κ S K Y) := by
    have heq : quadraticContactSet u κ S K Y =
        (K ∩ quadraticContactMap u κ ⁻¹' Y) ∩
          ⋂ z ∈ S, {x | x ∈ K ∧
            quadraticTilt u κ (quadraticContactMap u κ x) x ≤
              quadraticTilt u κ (quadraticContactMap u κ x) z} := by
      ext x
      simp only [quadraticContactSet, mem_ofPred_eq, mem_inter_iff, mem_preimage,
        mem_iInter, isMinOn_iff]
      aesop
    rw [heq]
    exact (hF.preimage_isClosed_of_isClosed hK.isClosed hY).inter
      (isClosed_biInter fun z _ ↦ hK.isClosed.isClosed_le hleft (hright z))
  exact hK.of_isClosed_subset hclosed (fun _ hx ↦ hx.1)

/-- A lower contact in a neighborhood is an unconstrained local minimum. -/
theorem isLocalMin_quadraticTilt_of_mem_contactSet
    {u : E → ℝ} {κ : ℝ} {S K Y : Set E} {x : E}
    (hx : x ∈ quadraticContactSet u κ S K Y) (hS : S ∈ 𝓝 x) :
    IsLocalMin (quadraticTilt u κ (quadraticContactMap u κ x)) x :=
  hx.2.2.isLocalMin hS

/-- Differentiating a quadratic tilt adds its radial linear term to the gradient. -/
theorem gradient_quadraticTilt {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (κ : ℝ) (y : E) :
    ∇ (quadraticTilt u κ y) x = ∇ u x + κ • (x - y) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hquad := (((hasFDerivAt_id x).sub_const y).norm_sq).const_mul (κ / 2)
  convert hu.hasFDerivAt.add hquad using 1
  · rfl
  · ext v
    simp only [map_add, map_smul, add_apply,
      smul_apply, toDual_gradient, InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      innerSL_apply_apply, id_eq]
    congr 1
    cas

/-- At an interior quadratic contact, the contact map recovers the vertex. -/
theorem quadraticContactMap_eq_of_isLocalMin
    {u : E → ℝ} {κ : ℝ} {x y : E} (hκ : κ ≠ 0)
    (hu : DifferentiableAt ℝ u x) (hmin : IsLocalMin (quadraticTilt u κ y) x) :
    quadraticContactMap u κ x = y := by
  have hzero : ∇ (quadraticTilt u κ y) x = 0 := by
    rw [gradient, hmin.fderiv_eq_zero, map_zero]
  rw [gradient_quadraticTilt hu κ y] at hzero
  have hgrad : ∇ u x = -(κ • (x - y)) := eq_neg_of_add_eq_zero_left hzero
  rw [quadraticContactMap, hgrad, smul_neg, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  abel

end PDE.Analysis
