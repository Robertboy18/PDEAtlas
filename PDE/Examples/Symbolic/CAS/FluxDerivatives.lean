/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Divergence
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Conservative flux calculus with checked scalar derivatives

The divergence of a flux built from a scalar field `u` that is only differentiable at the
point: a weighted planar field and the reciprocal flux `(1 / u) v` where `u ≠ 0`, in arbitrary
dimension. `cas` computes the scalar derivative of the flux curve, and the divergence
rules `divergence_smul` and `divergence_comp_of_hasDerivAt` supply the product and chain rules.
-/

@[expose] public section

namespace PDE.Examples.PDECalculusRegression

open PDE.Analysis

/-- A scalar weight can remain abstract while the vector field is differentiated
component by component. -/
theorem divergence_weighted_planar_field
    {a : ℝ^2 → ℝ} {x : ℝ^2} (ha : DifferentiableAt ℝ a x) :
    ∇· (fun y ↦ a y • WithLp.toLp 2 ![y 0 ^ 2, Real.sin (y 1)]) x =
      fderiv ℝ a x (WithLp.toLp 2 ![x 0 ^ 2, Real.sin (x 1)]) +
        a x * (2 * x 0 + Real.cos (x 1)) := by
  have hF : DifferentiableAt ℝ
      (fun y : ℝ^2 ↦ WithLp.toLp 2 ![y 0 ^ 2, Real.sin (y 1)]) x := by
    apply (differentiableAt_piLp 2).mpr
    intro i
    fin_cases i <;> dsimp <;> cas
  have hdiv :
      ∇· (fun y : ℝ^2 ↦ WithLp.toLp 2 ![y 0 ^ 2, Real.sin (y 1)]) x =
        2 * x 0 + Real.cos (x 1) := by
    simp only [divergence, Fin.sum_univ_two]
    change (∂[0] (fun y : ℝ^2 ↦ y 0 ^ 2)) x +
      (∂[1] (fun y : ℝ^2 ↦ Real.sin (y 1))) x = _
    cas
  rw [divergence_smul ha hF, hdiv]

/-- The flux curve need only be differentiable at the value attained by the
field; its singularity at zero does not require a global smoothness assumption. -/
theorem divergence_reciprocal_flux {n : ℕ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u x) (hne : u x ≠ 0) (v : ℝ^n) :
    ∇· (fun y ↦ (1 / u y) • v) x =
      (-1 / u x ^ 2) * fderiv ℝ u x v := by
  have hflux : HasDerivAt (fun s : ℝ ↦ 1 / s) (-1 / u x ^ 2) (u x) := by
    cas using hne
  simpa only [map_smul, smul_eq_mul] using
    divergence_comp_of_hasDerivAt (hflux.smul_const v) hu

end PDE.Examples.PDECalculusRegression
