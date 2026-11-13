/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
import PDE.Elliptic.Regularity.Global.Poisson

/-!
# Constant Laplace coefficients and their Dirichlet form

The identity principal matrix with zero drift and potential. Its full variational form is
the Dirichlet form, and its classical load is `-Δz`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE (laplacian)
open scoped Sobolev ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Constant identity principal coefficients and zero lower-order coefficients. -/
def laplace : SmoothFullCoefficients n Ω where
  principal _ := scalarIdentityMatrix 1
  drift _ _ := 0
  potential _ := 0
  principal_smooth _ _ _ := ContDiffUpToBoundary.const _
  drift_smooth _ _ := ContDiffUpToBoundary.const 0
  potential_smooth _ := ContDiffUpToBoundary.const 0

/-- The Laplace coefficients induce the Dirichlet form. -/
theorem form_laplace (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (u : H¹₀(Ω)) :
    (laplace (Ω := Ω)).form hΩ hb u = dirichletForm u := by
  have hz : (ContDiffUpToBoundary.const (k := 0) (Ω := Ω) 0).toLp hΩ hb ∞ = 0 :=
    Lp.ext (((ContDiffUpToBoundary.const 0).toLp_coeFn hΩ hb ∞).trans
      (Lp.coeFn_zero ℝ ∞ (domainMeasure n Ω)).symm)
  change fullDivergenceForm
    (multiplicationCoefficientOperator (fun i j : Fin n ↦
      (ContDiffUpToBoundary.const (k := 0) (scalarIdentityMatrix 1 i j)).toLp hΩ hb ∞))
    (fun _ ↦ mulLpLeft ((ContDiffUpToBoundary.const (k := 0) (Ω := Ω) 0).toLp hΩ hb ∞))
    (mulLpLeft ((ContDiffUpToBoundary.const (k := 0) (Ω := Ω) 0).toLp hΩ hb ∞)) u = _
  rw [hz]
  exact fullDivergenceForm_identity_eq_dirichletForm hΩ hb u

/-- The classical Laplace load is minus the coordinate Laplacian. -/
theorem classicalLoad_laplace (z : ℝ^n → ℝ) (x : ℝ^n) :
    (laplace (Ω := Ω)).classicalLoad z x = -laplacian z x := by
  classical
  have hterm (i j : Fin n) :
      (∂[i] (fun y ↦ scalarIdentityMatrix 1 i j * (∂[j] z) y)) x =
        if i = j then (∂[i] (∂[i] z)) x else 0 := by
    by_cases h : i = j
    · subst j
      simp [scalarIdentityMatrix]
    · simp [scalarIdentityMatrix, h, PDE.partialDeriv_const]
  simp only [classicalLoad, laplace, hterm, zero_mul, Finset.sum_const_zero, add_zero]
  simp [laplacian]

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
