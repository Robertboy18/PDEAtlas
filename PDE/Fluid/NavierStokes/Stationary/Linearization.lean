/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact first variation of the stationary self-similar velocity operator

At a common C² point, the operator has an exact quadratic expansion along
an affine velocity path. The coefficient of the linear term is therefore
an actual derivative of the stationary equation.
-/

@[expose] public noncomputable section

namespace NavierStokes

variable {n : ℕ}

/-- The stationary self-similar momentum operator before adding pressure. -/
def stationaryVelocityOperator (U : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ^n :=
  (-(1 / 2) : ℝ) • (U x + fderiv ℝ U x x) +
    PDE.advectiveDerivative U U x - PDE.laplacian U x

/-- The velocity expression obtained by linearizing at a prescribed base field. -/
def stationaryVelocityLinearization (U v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ^n :=
  (-(1 / 2) : ℝ) • (v x + fderiv ℝ v x x) +
    PDE.advectiveDerivative U v x + PDE.advectiveDerivative v U x -
      PDE.laplacian v x

/-- The stationary velocity operator has an exact quadratic expansion at every common
C² point. No regularity at other points is required. -/
theorem stationaryVelocityOperator_add_smul
    {U v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hU : ContDiffAt ℝ 2 U x) (hv : ContDiffAt ℝ 2 v x) (t : ℝ) :
    stationaryVelocityOperator (fun y ↦ U y + t • v y) x =
      stationaryVelocityOperator U x + t • stationaryVelocityLinearization U v x +
        t ^ 2 • PDE.advectiveDerivative v v x := by
  have hUd : DifferentiableAt ℝ U x := hU.differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℝ v x := hv.differentiableAt (by norm_num)
  have hD : fderiv ℝ (fun y ↦ U y + t • v y) x =
      fderiv ℝ U x + t • fderiv ℝ v x :=
    (hUd.hasFDerivAt.add (hvd.hasFDerivAt.const_smul t)).fderiv
  have hΔ : PDE.laplacian (fun y ↦ U y + t • v y) x =
      PDE.laplacian U x + t • PDE.laplacian v x := by
    rw [(hU.add (hv.const_smul t)).coordinate_laplacian_eq_laplacian,
      hU.coordinate_laplacian_eq_laplacian, hv.coordinate_laplacian_eq_laplacian]
    calc
      _ = Laplacian.laplacian U x +
          Laplacian.laplacian (fun y ↦ t • v y) x := by
        simpa only [Pi.add_def] using hU.laplacian_add (hv.const_smul t)
      _ = _ := by
        congr 1
        simpa only [Pi.smul_def] using InnerProductSpace.laplacian_smul t hv
  dsimp only [stationaryVelocityOperator, stationaryVelocityLinearization,
    PDE.advectiveDerivative]
  rw [hΔ]
  simp only [hD, add_apply, smul_apply, map_add, map_smul]
  module

/-- The linear coefficient in the expansion is the pointwise derivative at zero. -/
theorem hasDerivAt_stationaryVelocityOperator_affine
    {U v : ℝ^n → ℝ^n} {x : ℝ^n}
    (hU : ContDiffAt ℝ 2 U x) (hv : ContDiffAt ℝ 2 v x) :
    HasDerivAt (fun t : ℝ ↦ stationaryVelocityOperator (fun y ↦ U y + t • v y) x)
      (stationaryVelocityLinearization U v x) 0 := by
  have hexpand :
      (fun t : ℝ ↦ stationaryVelocityOperator (fun y ↦ U y + t • v y) x) =
        fun t ↦ stationaryVelocityOperator U x +
          t • stationaryVelocityLinearization U v x +
            t ^ 2 • PDE.advectiveDerivative v v x :=
    funext (stationaryVelocityOperator_add_smul hU hv)
  rw [hexpand]
  simpa [Pi.add_def] using ((hasDerivAt_const (0 : ℝ) (stationaryVelocityOperator U x)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (stationaryVelocityLinearization U v x))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).smul_const (PDE.advectiveDerivative v v x))

end NavierStokes
