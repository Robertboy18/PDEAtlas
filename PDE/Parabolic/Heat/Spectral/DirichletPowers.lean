/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletBasis
public import PDE.Parabolic.Heat.Spectral.HilbertPowers

/-!
# Zero-boundary weak heat series on bounded domains

The Poisson inverse maps the next weighted Hilbert series to an energy-space
representative of the current one. Continuity of this inverse justifies summation
in `H¹₀` and time differentiation there. Thus arbitrary `L²` data yield a
zero-boundary weak heat solution at every positive time, with no boundary
smoothness.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace Filter
open scoped Sobolev Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} (S : DirichletHeatSpectrum n Ω)
  (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)

/-- The energy representative of the `m`th eigenvalue-weighted heat series. -/
def energyPower (m : ℕ) (f : DerivLp n 2 Ω) (t : ℝ) : H¹₀(Ω) :=
  dirichletSolveCLM hn hbounded
    (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + 1) f t)

/-- Weighted heat sums converge in the zero-boundary energy norm. -/
theorem hasSum_energyPower (m : ℕ)
    (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasSum (fun i ↦ (S.eigenvalue i ^ m * Real.exp (-S.eigenvalue i * t) *
      S.basis.repr f i) • S.eigenfunction i) (S.energyPower hn hbounded m f t) := by
  have hopen : IsOpen Ω := (S.poisson_eigenfunction 0).1
  have h := (dirichletSolveCLM hn hbounded).hasSum
    (hasSum_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + 1) f ht)
  apply h.congr_fun
  intro i
  symm
  have hcoeff : S.eigenvalue i ^ (m + 1) * Real.exp (-S.eigenvalue i * t) *
      S.basis.repr f i =
      (S.eigenvalue i ^ m * Real.exp (-S.eigenvalue i * t) * S.basis.repr f i) *
        S.eigenvalue i := by rw [pow_succ]; ring
  rw [hcoeff, mul_smul, map_smul, S.dirichletSolve_eigenvalue_smul hn hopen hbounded]

/-- The energy representative has exactly the weighted Hilbert sum as its base. -/
theorem energyPower_base (m : ℕ)
    (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    baseCoordCLM (S.energyPower hn hbounded m f t) =
      spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f t := by
  have h := baseCoordCLM.hasSum (S.hasSum_energyPower hn hbounded m f ht)
  simp only [map_smul, S.base_eigenfunction] at h
  exact h.unique (hasSum_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg m f ht)

/-- The weighted energy representatives satisfy the distributional Poisson equations. -/
theorem energyPower_isWeakPoissonSolution (m : ℕ)
    (f : DerivLp n 2 Ω) (t : ℝ) :
    IsWeakPoissonSolution
      (spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + 1) f t)
      (S.energyPower hn hbounded m f t) :=
  dirichletSolve.isWeakPoissonSolution (S.poisson_eigenfunction 0).1 hn hbounded _

/-- Time differentiation also holds in `H¹₀`, with minus the next weighted series. -/
theorem hasDerivAt_energyPower (m : ℕ) (f : DerivLp n 2 Ω) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (S.energyPower hn hbounded m f)
      (-S.energyPower hn hbounded (m + 1) f t) t := by
  have h := (dirichletSolveCLM hn hbounded).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spectralHeatPower S.basis S.eigenvalue S.eigenvalue_nonneg (m + 1) f ht)
  rw [map_neg] at h
  exact h

end HeatEquation.DirichletHeatSpectrum
