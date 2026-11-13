/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import PDE.Analysis.InnerProductSpace.Calculus.Sphere

/-!
# Singular Jacobians of sphere-valued maps

The value of a map into a nonzero sphere is a nonzero vector in the left kernel of its
actual Jacobian. This proves singularity without assuming an inverse or choosing derivative
data independently of the map.
-/

@[expose] public section

open Filter Matrix
open scoped Topology InnerProductSpace

namespace PDE.Analysis

/-- A differentiable germ valued in a sphere of nonzero radius has zero Jacobian determinant. -/
theorem det_jacobianMatrix_eq_zero_of_eventually_norm_eq {n : ℕ} {w : ℝ^n → ℝ^n}
    {x : ℝ^n} {r : ℝ} (hw : DifferentiableAt ℝ w x) (hr : r ≠ 0)
    (hsphere : ∀ᶠ y in 𝓝 x, ‖w y‖ = r) : (jacobianMatrix w x).det = 0 := by
  classical
  by_contra hdet
  have hkernel : (fun k ↦ w x k) ᵥ* jacobianMatrix w x = 0 := by
    ext i
    simp only [vecMul, dotProduct, jacobianMatrix_apply_eq_fderiv hw, Pi.zero_apply]
    have hi := inner_fderiv_eq_zero_of_eventually_norm_eq hw hsphere
      (EuclideanSpace.single i (1 : ℝ))
    simpa [PiLp.inner_apply, mul_comm] using hi
  have hzero := Matrix.eq_zero_of_vecMul_eq_zero hdet hkernel
  have hwzero : w x = 0 := by
    ext k
    exact congrFun hzero k
  have hnorm := hsphere.self_of_nhds
  rw [hwzero, norm_zero] at hnorm
  exact hr hnorm.symm

end PDE.Analysis
