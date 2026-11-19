/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
public import PDE.Spaces.Sobolev.Evolution.Classical.Data.Slices
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Smooth wave data with nonzero drift and a sign-changing potential

On the unit interval in one-dimensional Euclidean space, take `A = 1`,
`b = 1`, and `c(x) = x`. The function `exp(t) * (1 - x²)` has nonzero
initial position and velocity and forcing `exp(t) * (3 - x - x² - x³)`.
The equation is `u_tt - u_xx + u_x + x u = f`. The forcing is nonzero on the lateral
boundary and the initial data are not flat there.
-/

@[expose] public noncomputable section

namespace PDE.Examples.SmoothWave.Manufactured

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open scoped ContDiff

/-- The spatial interval is the one-dimensional Euclidean unit ball. -/
def domain : Set (ℝ^1) := Boundary.Atlas.UnitBall.domain 1

/-- The open cylinder between time zero and one. -/
def cylinder : Set (SpaceTime 1) := splitSpaceTime ⁻¹' (domain ×ˢ Ioo 0 1)

/-- The initial profile `1 - x²`, which vanishes at `±1` with nonzero slope. -/
def profile (x : ℝ^1) : ℝ := 1 - x 0 ^ 2

/-- The wave `exp(t)(1 - x²)`, equal to all of its time derivatives. -/
def wave (z : SpaceTime 1) : ℝ := Real.exp (z 0) * (1 - z 1 ^ 2)

/-- The forcing `exp(t)(3 - x - x² - x³)`. -/
def forcing (z : SpaceTime 1) : ℝ := Real.exp (z 0) * (3 - z 1 - z 1 ^ 2 - z 1 ^ 3)

/-- The spatial domain is open. -/
theorem domain_open : IsOpen domain := Metric.isOpen_ball

/-- The spatial domain is bounded. -/
theorem domain_bounded : Bornology.IsBounded domain := Metric.isBounded_ball

/-- The cylinder is bounded. -/
theorem cylinder_bounded : Bornology.IsBounded cylinder := by
  change Bornology.IsBounded ((spaceTimeContinuousLinearEquiv 1).toHomeomorph ⁻¹'
    (domain ×ˢ Ioo 0 1))
  exact (spaceTimeContinuousLinearEquiv 1).antilipschitzWith.isBounded_preimage
    (domain_bounded.prod (Metric.isBounded_Ioo 0 1))

/-- The domain has smooth graph boundary at every finite order. -/
theorem domain_graph (k : ℕ) : Boundary.HasContDiffGraphBoundary k domain :=
  Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 k

/-- A smooth function on `ℝ^d` is `C^k` up to the boundary of every bounded domain. -/
theorem regular_of_contDiff {d : ℕ} {D : Set (ℝ^d)} (hD : Bornology.IsBounded D)
    {v : ℝ^d → ℝ} (hv : ContDiff ℝ ∞ v) (k : ℕ) : ContDiffUpToBoundary k v D :=
  contDiffUpToBoundary_of_contDiffOn isOpen_univ
    ((hv.of_le (by simp)).contDiffOn)
    hD.isCompact_closure (subset_univ _)

/-- The profile is `C^k` up to the boundary for every `k`. -/
theorem profile_regular (k : ℕ) : ContDiffUpToBoundary k profile domain := by
  apply regular_of_contDiff domain_bounded ?_ k
  unfold profile
  cas

/-- The wave is smooth. -/
theorem wave_contDiff : ContDiff ℝ ∞ wave := by
  unfold wave
  cas

/-- The wave is `C^k` up to the boundary of the cylinder for every `k`. -/
theorem wave_regular (k : ℕ) : ContDiffUpToBoundary k wave cylinder :=
  regular_of_contDiff cylinder_bounded wave_contDiff k

/-- The forcing is globally smooth. -/
theorem forcing_contDiff : ContDiff ℝ ∞ forcing := by
  unfold forcing
  cas

/-- The forcing is `C^k` up to the boundary of the cylinder for every `k`. -/
theorem forcing_regular (k : ℕ) : ContDiffUpToBoundary k forcing cylinder :=
  regular_of_contDiff cylinder_bounded forcing_contDiff k

/-- The coefficients `A = 1`, `b = 1` and `c(x) = x`. -/
def coefficients : SmoothFullCoefficients 1 domain where
  principal := fun _ _ _ ↦ 1
  drift := fun _ _ ↦ 1
  potential := fun x ↦ x 0
  principal_smooth := fun _ _ _ ↦ ContDiffUpToBoundary.const 1
  drift_smooth := fun _ _ ↦ ContDiffUpToBoundary.const 1
  potential_smooth := fun k ↦ regular_of_contDiff domain_bounded
    (EuclideanSpace.proj (0 : Fin 1)).contDiff k

/-- The principal matrix is symmetric. -/
theorem coefficients_symmetric :
    ∀ x ∈ domain, ∀ i j, coefficients.principal x i j = coefficients.principal x j i :=
  fun _ _ _ _ ↦ rfl

/-- The principal part is elliptic with constant `1`. -/
theorem coefficients_elliptic :
    ∀ x ∈ domain, MatrixEllipticLowerBound (coefficients.principal x) 1 := by
  intro x hx ξ
  simp [coefficients, principalEnergy, dotProduct]

/-- `∂ₜ wave = wave`. -/
theorem partial_time_wave (z : SpaceTime 1) : (∂[(0 : Fin 2)] wave) z = wave z := by
  unfold wave
  cas

/-- The spatial operator applied to the wave at time `t` is `exp(t)(2 - x - x³)`. -/
theorem classicalLoad_wave (t : ℝ) (x : ℝ^1) :
    coefficients.classicalLoad (fun y ↦ wave (timeSpaceCons t y)) x =
      Real.exp t * (2 - x 0 - x 0 ^ 3) := by
  unfold SmoothFullCoefficients.classicalLoad coefficients wave
  simp only [Fintype.sum_unique, Fin.default_eq_zero]
  change -((∂[0] (fun y : ℝ^1 ↦
    1 * (∂[0] ((fun z : ℝ^1 ↦ Real.exp t * (1 - z 0 ^ 2)) : ℝ^1 → ℝ)) y)) x) +
    1 * (∂[0] ((fun y : ℝ^1 ↦ Real.exp t * (1 - y 0 ^ 2)) : ℝ^1 → ℝ)) x +
    x 0 * (Real.exp t * (1 - x 0 ^ 2)) = _
  have hfirst : ∂[0] ((fun y : ℝ^1 ↦ Real.exp t * (1 - y 0 ^ 2)) : ℝ^1 → ℝ) =
      fun y ↦ -2 * Real.exp t * y 0 := by
    funext y
    cas
  rw [hfirst]
  have hsecond : (∂[0] ((fun y : ℝ^1 ↦ 1 * (-2 * Real.exp t * y 0)) : ℝ^1 → ℝ)) x =
      -2 * Real.exp t := by
    cas
  rw [hsecond]
  cas

/-- The wave solves the equation with forcing `forcing`. -/
theorem equation (t : ℝ) (x : ℝ^1) :
    wave (timeSpaceCons t x) +
      coefficients.classicalLoad (fun y ↦ wave (timeSpaceCons t y)) x =
        forcing (timeSpaceCons t x) := by
  rw [classicalLoad_wave]
  change Real.exp t * (1 - x 0 ^ 2) + Real.exp t * (2 - x 0 - x 0 ^ 3) =
    Real.exp t * (3 - x 0 - x 0 ^ 2 - x 0 ^ 3)
  cas

end PDE.Examples.SmoothWave.Manufactured
