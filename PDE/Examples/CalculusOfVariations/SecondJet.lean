/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.NullLagrangian.SecondJet
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# The Euler–Lagrange operator depends only on the second jet

A density with nonlinear matrix dependence and both value and spatial dependence has
the same Euler–Lagrange expression on a `C²` map `ℝ² → ℝ³` and on its quadratic Taylor
polynomial (`coupledDensity_quadratic_replacement`).
-/

@[expose] public section

noncomputable section

open PDE.Analysis PDE.CalculusOfVariations
open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.Examples.SecondJet

/-- A full-variable density with nonlinear dependence on a rectangular matrix. -/
def coupledDensity (P : Matrix (Fin 3) (Fin 2) ℝ) (z : ℝ^3) (x : ℝ^2) : ℝ :=
  (P 0 0 * P 2 1 - P 0 1 * P 2 0) * z 1 + x 0 * P 1 0 + z 0 ^ 2 * x 1

/-- `coupledDensity` is jointly `C²` in `(P, z, x)`. -/
theorem contDiff_coupledDensity :
    ContDiff ℝ 2
      (fun a : Matrix (Fin 3) (Fin 2) ℝ × (ℝ^3 × ℝ^2) ↦
        coupledDensity a.1 a.2.1 a.2.2) := by
  unfold coupledDensity
  fun_prop

/-- Replacing a `C²` map by its quadratic Taylor polynomial at `x` leaves the Euler–Lagrange
expression of the coupled density at `x` unchanged. -/
theorem coupledDensity_quadratic_replacement {u : ℝ^2 → ℝ^3} {x : ℝ^2}
    (hu : ContDiffAt ℝ 2 u x) (k : Fin 3) :
    classicalEulerLagrange coupledDensity u x k =
      classicalEulerLagrange coupledDensity
        (quadraticJet x (u x) (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x)) x k :=
  classicalEulerLagrange_congr_secondJet hu
    ((contDiff_quadraticJet ..).contDiffAt.of_le (by simp))
    contDiff_coupledDensity.contDiffAt
    (quadraticJet_self ..).symm (fderiv_quadraticJet_self ..).symm
    (fderiv_fderiv_quadraticJet_of_symmetric _ _ _ _
      (hu.isSymmSndFDerivAt (by norm_num)) _).symm k

end PDE.Examples.SecondJet
