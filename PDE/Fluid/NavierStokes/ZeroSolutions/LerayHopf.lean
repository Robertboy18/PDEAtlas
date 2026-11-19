/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.LerayHopf
public import PDE.Fluid.NavierStokes.ZeroSolutions.Weak

/-!
# Zero Leray-Hopf Navier-Stokes solutions

The zero velocity is a pressure-free Leray-Hopf solution of the zero-data problem on every slab
`[0, T]` with `T > 0` (`zeroLerayHopfSolution`), and with zero pressure it is a
pressure-representative one (`zeroPressureRepresentativeLerayHopfSolution`).
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- Zero forcing does no work against any velocity field. -/
theorem forceWork_zeroProblem {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) :
    forceWork (zeroProblem n viscosity hviscosity) u t = 0 := by
  simp [forceWork]

/-- The zero weak solution is a pressure-free Leray-Hopf solution on every positive finite slab. -/
def zeroLerayHopfSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) : LerayHopfSolution (zeroProblem n viscosity hviscosity) where
  toWeakSolution := zeroWeakSolution (n := n) viscosity hviscosity T hT
  velocity_memLp_top := by
    rw [zeroWeakSolution_velocityL2Slice_eq_zero (n := n) viscosity hviscosity T hT]
    exact MemLp.zero
  gradient_memLp_two := by
    rw [zeroWeakSolution_gradientL2Slice_eq_zero (n := n) viscosity hviscosity T hT]
    exact MemLp.zero
  velocityWeakL2Slice_continuousOn := by
    have hz :
        (zeroWeakSolution (n := n) viscosity hviscosity T hT).velocityWeakL2Slice = 0 := by
      funext t
      simp [WeakSolution.velocityWeakL2Slice,
        zeroWeakSolution_velocityL2Slice_eq_zero (n := n) viscosity hviscosity T hT]
    rw [hz]
    exact continuousOn_const
  velocityL2Slice_zero_eq_initial := by
    rw [congrFun (zeroWeakSolution_velocityL2Slice_eq_zero
      (n := n) viscosity hviscosity T hT) 0]
    exact (zeroWeakSolution_initialVelocityL2_eq_zero (n := n) viscosity hviscosity T hT).symm
  forceWorkTimeIntegrableOn := by
    change IntegrableOn
      (fun s ↦ ∫ x : ℝ^n,
        forcePowerDensity (zeroProblem n viscosity hviscosity)
          (zeroWeakSolution (n := n) viscosity hviscosity T hT).u s x)
      (Set.Icc 0 T)
    have hzero (s : ℝ) :
        forcePowerDensity (zeroProblem n viscosity hviscosity)
            (zeroWeakSolution (n := n) viscosity hviscosity T hT).u s = 0 := by
      funext x
      exact forcePowerDensity_zeroProblem viscosity hviscosity _ s x
    have hslice :
        (fun s ↦ ∫ x : ℝ^n,
          forcePowerDensity (zeroProblem n viscosity hviscosity)
            (zeroWeakSolution (n := n) viscosity hviscosity T hT).u s x) = 0 := by
      funext s
      rw [hzero s]
      simp
    rw [hslice]
    exact integrableOn_zero
  energy_inequality := by
    intro t ht
    change kineticEnergy (n := n) (fun _ : ℝ^(n + 1) ↦ 0) t +
        viscosity * ∫ s in Set.Icc 0 t,
          weakGradientDissipation (n := n) (fun _ : ℝ^(n + 1) ↦ 0) s ≤
      initialKineticEnergy (zeroProblem n viscosity hviscosity) +
        forceWork (zeroProblem n viscosity hviscosity) (fun _ : ℝ^(n + 1) ↦ 0) t
    simp [kineticEnergy_zero, weakGradientDissipation_zero,
      initialKineticEnergy_zeroProblem, forceWork_zeroVelocity]

/-- The zero pressure representative refines the zero pressure-free Leray-Hopf solution. -/
def zeroPressureRepresentativeLerayHopfSolution {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity) (T : ℝ) (hT : 0 < T) :
    PressureRepresentativeLerayHopfSolution (zeroProblem n viscosity hviscosity) where
  toPressureWeakSolution := zeroPressureWeakSolution (n := n) viscosity hviscosity T hT
  velocity_memLp_top :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).velocity_memLp_top
  gradient_memLp_two :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).gradient_memLp_two
  velocityWeakL2Slice_continuousOn :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).velocityWeakL2Slice_continuousOn
  velocityL2Slice_zero_eq_initial :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).velocityL2Slice_zero_eq_initial
  forceWorkTimeIntegrableOn :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).forceWorkTimeIntegrableOn
  energy_inequality :=
    (zeroLerayHopfSolution (n := n) viscosity hviscosity T hT).energy_inequality

/-- A zero-data pressure-free Leray-Hopf solution exists on every positive finite slab. -/
theorem exists_zero_lerayHopfSolution_on {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) :
    ∃ sol : LerayHopfSolution (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroLerayHopfSolution (n := n) viscosity hviscosity T hT, rfl⟩

/-- A zero pressure-representative Leray-Hopf solution exists on every positive finite slab. -/
theorem exists_zero_pressureRepresentativeLerayHopfSolution_on {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity) (T : ℝ) (hT : 0 < T) :
    ∃ sol : PressureRepresentativeLerayHopfSolution
        (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroPressureRepresentativeLerayHopfSolution (n := n) viscosity hviscosity T hT, rfl⟩

end NavierStokes
