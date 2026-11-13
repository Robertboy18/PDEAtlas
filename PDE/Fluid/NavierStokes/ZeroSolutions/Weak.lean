/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.WeakSolutions
public import PDE.Fluid.NavierStokes.ZeroData
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# The zero weak Navier-Stokes solution

The zero velocity with zero pressure solves the zero-data Navier-Stokes problem `zeroProblem n ν`
in the weak sense on every closed slab `[0, T]` with `T > 0`: `zeroPressureWeakSolution` is the
pressure-retaining weak solution, `zeroWeakSolution` forgets the pressure, and all of its `L²`
slices are zero.

These inhabit the weak-solution interfaces of `PDE.Fluid.NavierStokes.WeakSolutions`. Every
integrability, trace, and weak-equation field is discharged for the trivial solution, which shows
the interfaces are consistent and gives a base case for statements quantifying over weak
solutions.

## Main declarations

* `zeroPressureWeakSolution`, `zeroWeakSolution`: the zero solutions with and without pressure.
* `zeroWeakSolution_velocityL2Slice_eq_zero`, `zeroWeakSolution_gradientL2Slice_eq_zero`,
  `zeroWeakSolution_initialVelocityL2_eq_zero`: the `L²` classes carried by the zero solution.
* `exists_zero_weakSolution_on`, `exists_zero_pressureWeakSolution_on`: weak solutions of the
  zero problem exist on every prescribed positive finite slab.
-/

@[expose] public section

open PDE (partialDeriv)

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- The zero velocity and zero pressure solve the zero-data weak Navier-Stokes problem on every
closed finite positive time slab `[0,T]`. -/
def zeroPressureWeakSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    PressureWeakSolution (zeroProblem n viscosity hviscosity) where
  u := fun _ ↦ 0
  p := fun _ ↦ 0
  Du := fun _ ↦ 0
  T := ⟨T, hT⟩
  initialVelocity_memLp := by
    simp [zeroProblem, IncompressibleFlow.zeroInitialValueData]
  velocity_memLp_at := by
    intro t _ht
    exact MemLp.zero
  gradient_memLp_at := by
    intro t _ht
    exact MemLp.zero
  hasWeakSpatialDerivative := by
    intro t ht i j
    change SobolevSpace.HasWeakDerivativeOn (n := n) Set.univ [j]
      (fun _ : ℝ^n ↦ (0 : ℝ))
      (fun _ : ℝ^n ↦ (0 : ℝ))
    exact SobolevSpace.hasWeakDerivativeOn_zero
      (n := n) (Set.univ : Set (ℝ^n)) [j]
  pressure_memLp_at := by
    intro t ht
    simp
  force_memLp_at := by
    intro t ht
    simp [zeroProblem, IncompressibleFlow.zeroInitialValueData]
  weak_momentum_integrable_on := by
    intro φ hφ
    have hpoint :
        ∀ t x, weakMomentumIntegrand (zeroProblem n viscosity hviscosity)
          (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) φ t x = 0 := by
      intro t x
      simp [weakMomentumIntegrand, IncompressibleFlow.inviscidWeakMomentumIntegrand, zeroProblem,
        IncompressibleFlow.zeroInitialValueData]
    have hslice :
        weakMomentumSlice (zeroProblem n viscosity hviscosity)
          (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) φ = 0 := by
      funext t
      simp [weakMomentumSlice, hpoint]
    refine ⟨?_, ?_⟩
    · intro t ht
      simp [hpoint]
    · rw [hslice]
      exact integrableOn_zero
  weak_momentum_eq := by
    intro φ hφ
    have hslice :
        weakMomentumSlice (zeroProblem n viscosity hviscosity)
          (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) φ = 0 := by
      funext t
      simp [weakMomentumSlice, weakMomentumIntegrand,
        IncompressibleFlow.inviscidWeakMomentumIntegrand, zeroProblem,
        IncompressibleFlow.zeroInitialValueData, partialDeriv]
    rw [hslice]
    simp [IncompressibleFlow.initialVelocityTestPairing,
      IncompressibleFlow.initialVelocityTestPairingDensity, zeroProblem,
      IncompressibleFlow.zeroInitialValueData]
  distributionallyDivergenceFree_at := by
    intro t ht ψ hψsmooth hψcompact
    exact IncompressibleFlow.distributionallyDivergenceFree_zero n
      ψ hψsmooth hψcompact

/-- Forgetting the zero pressure gives the pressure-free zero weak solution. -/
def zeroWeakSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) : WeakSolution (zeroProblem n viscosity hviscosity) :=
  (zeroPressureWeakSolution (n := n) viscosity hviscosity T hT).toWeakSolution

/-- Every `L²` velocity slice of the zero weak solution is zero. -/
theorem zeroWeakSolution_velocityL2Slice_eq_zero {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    (zeroWeakSolution (n := n) viscosity hviscosity T hT).velocityL2Slice = 0 := by
  funext t
  by_cases ht : t ∈ Set.Icc 0
      ((zeroWeakSolution (n := n) viscosity hviscosity T hT).T : ℝ)
  · apply Lp.ext
    filter_upwards [
      (zeroWeakSolution (n := n) viscosity hviscosity T hT).velocityL2Slice_apply_ae ht] with x hx
    rw [hx]
    simp [zeroWeakSolution, PressureWeakSolution.toWeakSolution,
      zeroPressureWeakSolution, IncompressibleFlow.velocitySlice]
  · exact IncompressibleFlow.velocityL2SliceOn_of_notMem _ ht

/-- Every `L²` weak-gradient slice of the zero weak solution is zero. -/
theorem zeroWeakSolution_gradientL2Slice_eq_zero {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    (zeroWeakSolution (n := n) viscosity hviscosity T hT).gradientL2Slice = 0 := by
  funext t
  by_cases ht : t ∈ Set.Ioc 0
      ((zeroWeakSolution (n := n) viscosity hviscosity T hT).T : ℝ)
  · apply Lp.ext
    filter_upwards [
      (zeroWeakSolution (n := n) viscosity hviscosity T hT).gradientL2Slice_apply_ae ht] with x hx
    rw [hx]
    simp [zeroWeakSolution, PressureWeakSolution.toWeakSolution,
      zeroPressureWeakSolution, IncompressibleFlow.spatialGradientSlice]
  · simp [WeakSolution.gradientL2Slice, ht]

/-- The prescribed initial `L²` class for the zero problem is zero. -/
theorem zeroWeakSolution_initialVelocityL2_eq_zero {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    (zeroWeakSolution (n := n) viscosity hviscosity T hT).initialVelocityL2 = 0 := by
  unfold WeakSolution.initialVelocityL2
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
    (zeroWeakSolution (n := n) viscosity hviscosity T hT).initialVelocity_memLp] with x hx
  rw [hx]
  simp [zeroProblem, IncompressibleFlow.zeroInitialValueData]

/-- The zero-data pressure-free weak interface exists on every requested positive finite slab. -/
theorem exists_zero_weakSolution_on {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    ∃ sol : WeakSolution (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroWeakSolution (n := n) viscosity hviscosity T hT, rfl⟩

/-- The zero-data pressure-retaining weak interface exists on every positive finite slab. -/
theorem exists_zero_pressureWeakSolution_on {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    ∃ sol : PressureWeakSolution (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroPressureWeakSolution (n := n) viscosity hviscosity T hT, rfl⟩

end NavierStokes
