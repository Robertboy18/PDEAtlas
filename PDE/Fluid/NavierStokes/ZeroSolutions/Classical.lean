/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.GlobalSolutions
public import PDE.Fluid.NavierStokes.ZeroData

/-!
# Classical zero solutions of Navier-Stokes

The zero velocity and pressure are global and finite-time pointwise and smooth solutions of the
zero-data problem `zeroProblem n ν`.
-/

@[expose] public section

open PDE (partialDeriv)

namespace NavierStokes

open EuclideanSpace

set_option linter.missingDocs true

/-- The zero velocity and zero pressure solve the zero-data Navier-Stokes problem globally. -/
def zeroGlobalPointwiseResidualSolution {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    GlobalPointwiseResidualSolution (zeroProblem n viscosity hviscosity) where
  u := fun _ ↦ 0
  p := fun _ ↦ 0
  momentum_at := by
    intro x hx
    ext i
    simp [IncompressibleFlow.materialDerivative_apply,
      PDE.spatialGradient_apply,
      IncompressibleFlow.spatialVectorLaplacian_apply,
      IncompressibleFlow.spatialLaplacian_apply, viscousTerm_apply, zeroProblem,
      IncompressibleFlow.zeroInitialValueData, partialDeriv]
  divergenceFreeOn := by
    intro x hx
    simp [IncompressibleFlow.DivergenceFreeAt,
      IncompressibleFlow.spatialDivergence_apply, partialDeriv]
  initial_eq := by
    intro x
    rfl

/-- The zero velocity and zero pressure give a global smooth classical zero-data
Navier-Stokes solution, so the global smooth solution interface is inhabited. -/
def zeroGlobalSmoothSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    GlobalSmoothSolution (zeroProblem n viscosity hviscosity) where
  toGlobalResidualSolution :=
    zeroGlobalPointwiseResidualSolution (n := n) viscosity hviscosity
  velocity_contDiffOn := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n))
      (IncompressibleFlow.globalDomain n)
    fun_prop
  pressure_contDiffOn := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ))
      (IncompressibleFlow.globalDomain n)
    fun_prop

/-- For every positive viscosity, the zero-data Navier-Stokes problem has a global smooth
solution. -/
theorem exists_zero_globalSmoothSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    Nonempty (GlobalSmoothSolution (zeroProblem n viscosity hviscosity)) :=
  ⟨zeroGlobalSmoothSolution (n := n) viscosity hviscosity⟩

/-- The zero velocity and zero pressure solve the zero-data Navier-Stokes problem on every
finite positive time interval.

It is the restriction of the global zero solution. -/
def zeroPointwiseResidualSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    PointwiseResidualSolution (zeroProblem n viscosity hviscosity) :=
  (zeroGlobalPointwiseResidualSolution (n := n) viscosity hviscosity)
    |>.toFiniteTime T hT

/-- The zero-data finite-time Navier-Stokes solution exists with the requested time horizon
exactly equal to `T`. -/
theorem exists_zero_pointwiseResidualSolution_on {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    ∃ sol : PointwiseResidualSolution (zeroProblem n viscosity hviscosity),
      (sol.T : ℝ) = T :=
  ⟨zeroPointwiseResidualSolution (n := n) viscosity hviscosity T hT, rfl⟩

/-- The zero velocity and zero pressure give a smooth finite-time classical zero-data
Navier-Stokes solution on every positive interval. -/
def zeroSmoothSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    SmoothSolution (zeroProblem n viscosity hviscosity) :=
  (zeroGlobalSmoothSolution (n := n) viscosity hviscosity).toFiniteTime T hT

/-- The zero-data finite-time smooth Navier-Stokes solution exists with the requested time horizon
exactly equal to `T`. -/
theorem exists_zero_smoothSolution_on {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity) (T : ℝ) (hT : 0 < T) :
    ∃ sol : SmoothSolution (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroSmoothSolution (n := n) viscosity hviscosity T hT, rfl⟩

end NavierStokes
