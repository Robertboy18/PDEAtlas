/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.GlobalSolutions

/-!
# Classical zero solutions of Euler

The zero velocity and pressure are global and finite-time pointwise and smooth solutions of the
Euler problem with zero forcing and zero initial velocity.
-/

@[expose] public section

open PDE (partialDeriv)

namespace Euler

open EuclideanSpace

set_option linter.missingDocs true

/-- The zero velocity and pressure solve the zero-data Euler problem globally. -/
def zeroGlobalPointwiseResidualSolution (n : ℕ) :
    GlobalPointwiseResidualSolution (IncompressibleFlow.zeroInitialValueData n) where
  u := fun _ ↦ 0
  p := fun _ ↦ 0
  momentum_at := by
    intro x hx
    ext i
    simp [IncompressibleFlow.materialDerivative_apply,
      PDE.spatialGradient_apply,
      IncompressibleFlow.zeroInitialValueData, partialDeriv]
  divergenceFreeOn := by
    intro x hx
    simp [IncompressibleFlow.DivergenceFreeAt,
      IncompressibleFlow.spatialDivergence_apply, partialDeriv]
  initial_eq := by
    intro x
    rfl

/-- The zero velocity and pressure give a global smooth Euler solution. -/
def zeroGlobalSmoothSolution (n : ℕ) :
    GlobalSmoothSolution (IncompressibleFlow.zeroInitialValueData n) where
  toGlobalResidualSolution := zeroGlobalPointwiseResidualSolution n
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

/-- The zero-data global smooth Euler interface is inhabited in every dimension. -/
theorem exists_zero_globalSmoothSolution (n : ℕ) :
    Nonempty (GlobalSmoothSolution (IncompressibleFlow.zeroInitialValueData n)) :=
  ⟨zeroGlobalSmoothSolution n⟩

/-- The global zero Euler solution restricted to a positive finite horizon. -/
def zeroPointwiseResidualSolution (n : ℕ) (T : ℝ) (hT : 0 < T) :
    PointwiseResidualSolution (IncompressibleFlow.zeroInitialValueData n) :=
  (zeroGlobalPointwiseResidualSolution n).toFiniteTime T hT

/-- The global smooth zero Euler solution restricted to a positive finite horizon. -/
def zeroSmoothSolution (n : ℕ) (T : ℝ) (hT : 0 < T) :
    SmoothSolution (IncompressibleFlow.zeroInitialValueData n) :=
  (zeroGlobalSmoothSolution n).toFiniteTime T hT

/-- A smooth zero Euler solution exists on every positive finite horizon. -/
theorem exists_zero_smoothSolution_on (n : ℕ) (T : ℝ) (hT : 0 < T) :
    ∃ sol : SmoothSolution (IncompressibleFlow.zeroInitialValueData n), (sol.T : ℝ) = T :=
  ⟨zeroSmoothSolution n T hT, rfl⟩

end Euler
