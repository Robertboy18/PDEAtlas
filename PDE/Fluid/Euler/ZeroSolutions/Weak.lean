/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.WeakSolutions

/-!
# The zero weak Euler solution

The zero velocity and pressure form a weak Euler solution with zero data on every closed slab
`[0, T]` with `T > 0` (`zeroWeakSolution`).
-/

@[expose] public section

open PDE (partialDeriv)

namespace Euler

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- Zero velocity and pressure solve the zero-data weak Euler problem on every positive finite
time slab `[0,T]`. -/
def zeroWeakSolution {n : ℕ} (T : ℝ) (hT : 0 < T) :
    WeakSolution (IncompressibleFlow.zeroInitialValueData n) where
  u := fun _ ↦ 0
  p := fun _ ↦ 0
  T := ⟨T, hT⟩
  initialVelocity_memLp := by
    simp [IncompressibleFlow.zeroInitialValueData]
  velocity_memLp_at := by
    intro t ht
    have hz : IncompressibleFlow.velocitySlice
        (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) t = 0 := by
      funext x
      rfl
    rw [hz]
    exact MemLp.zero
  pressure_memLp_at := by
    intro t ht
    simp
  force_memLp_at := by
    intro t ht
    simp [IncompressibleFlow.zeroInitialValueData]
  weak_momentum_integrable_on := by
    intro φ hφ
    have hpoint : ∀ t x,
        weakMomentumIntegrand (IncompressibleFlow.zeroInitialValueData n)
          (fun _ ↦ 0) (fun _ ↦ 0) φ t x = 0 := by
      intro t x
      simp [weakMomentumIntegrand, IncompressibleFlow.inviscidWeakMomentumIntegrand,
        IncompressibleFlow.zeroInitialValueData]
    have hslice :
        weakMomentumSlice (IncompressibleFlow.zeroInitialValueData n)
          (fun _ ↦ 0) (fun _ ↦ 0) φ = 0 := by
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
        weakMomentumSlice (IncompressibleFlow.zeroInitialValueData n)
          (fun _ ↦ 0) (fun _ ↦ 0) φ = 0 := by
      funext t
      simp [weakMomentumSlice, weakMomentumIntegrand,
        IncompressibleFlow.inviscidWeakMomentumIntegrand,
        IncompressibleFlow.zeroInitialValueData, partialDeriv]
    rw [hslice]
    simp [IncompressibleFlow.initialVelocityTestPairing,
      IncompressibleFlow.initialVelocityTestPairingDensity,
      IncompressibleFlow.zeroInitialValueData]
  distributionallyDivergenceFree_at := by
    intro t ht ψ hψsmooth hψcompact
    exact IncompressibleFlow.distributionallyDivergenceFree_zero n
      ψ hψsmooth hψcompact

/-- The zero-data weak Euler interface is inhabited on every positive finite time slab. -/
theorem exists_zero_weakSolution_on {n : ℕ} (T : ℝ) (hT : 0 < T) :
    ∃ sol : WeakSolution (IncompressibleFlow.zeroInitialValueData n), (sol.T : ℝ) = T :=
  ⟨zeroWeakSolution (n := n) T hT, rfl⟩

end Euler
