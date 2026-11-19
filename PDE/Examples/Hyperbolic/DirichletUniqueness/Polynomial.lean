/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.Dirichlet.Uniqueness
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A forced polynomial determined by its cylinder data

On the interval, `x² + 2t² + tx` has forcing `2`, initial displacement `x²`,
initial velocity `x`, and nonzero time-dependent lateral values. The uniqueness theorem
`eq_on_closedCylinder_of_initial_eq` shows that every classical solution with these data
equals this polynomial on the closed cylinder (`polynomial_unique`).
-/

@[expose] public noncomputable section

namespace WaveEquation.Examples.DirichletUniqueness

open PDE.Common Set SobolevSpace
open Boundary.Atlas.UnitBall

/-- A nonstationary wave with nonzero forcing and nonzero initial velocity. -/
def polynomial (p : ℝ^2) : ℝ := p 1 ^ 2 + 2 * p 0 ^ 2 + p 0 * p 1

/-- The polynomial is `C^k` for every `k`. -/
theorem contDiff_polynomial (k : ℕ) : ContDiff ℝ k polynomial := by
  unfold polynomial
  fun_prop

/-- The wave operator of the polynomial is `4 - 2 = 2`. -/
theorem polynomial_waveOperator (p : ℝ^2) : waveOperator polynomial p = 2 := by
  have hdt : ∂[0] polynomial = fun q ↦ 4 * q 0 + q 1 := by
    funext q
    unfold polynomial
    cas
  have hdx : ∂[1] polynomial = fun q ↦ 2 * q 1 + q 0 := by
    funext q
    unfold polynomial
    cas
  have ht : (∂[0] (∂[0] polynomial)) p = 4 := by
    rw [hdt]
    cas
  have hx : (∂[1] (∂[1] polynomial)) p = 2 := by
    rw [hdx]
    cas
  simp only [waveOperator, Fin.sum_univ_one, Fin.succ_zero_eq_one, ht, hx]
  norm_num

/-- The initial velocity of the polynomial is `x`. -/
theorem polynomial_initial_velocity (x : ℝ^1) :
    derivWithin (fun s ↦ polynomial (timeSpaceCons s x)) (Ici 0) 0 = x 0 := by
  have hd : HasDerivAt (fun s ↦ polynomial (timeSpaceCons s x)) (x 0) 0 := by
    change HasDerivAt (fun s ↦ x 0 ^ 2 + 2 * s ^ 2 + s * x 0) (x 0) 0
    cas
  exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0 (by simp))

/-- Every classical solution of `□u = 2` on the cylinder over the interval with the initial
and lateral data of `polynomial` equals `polynomial` on the closed cylinder. -/
theorem polynomial_unique {T : ℝ} (hT : 0 < T) {u : ℝ^2 → ℝ}
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder (domain 1) (Ioo 0 T)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder (domain 1) (Ioo 0 T))))
    (hPDE : ∀ x ∈ domain 1, ∀ t ∈ Ioo 0 T, waveOperator u (timeSpaceCons t x) = 2)
    (hb : ∀ x ∈ frontier (domain 1), ∀ t ∈ Icc 0 T,
      u (timeSpaceCons t x) = polynomial (timeSpaceCons t x))
    (hpos : ∀ x ∈ domain 1, u (timeSpaceCons 0 x) = x 0 ^ 2)
    (hvel : ∀ x ∈ domain 1,
      derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici 0) 0 = x 0) :
    ∀ x ∈ closure (domain 1), ∀ t ∈ Icc 0 T,
      u (timeSpaceCons t x) = polynomial (timeSpaceCons t x) := by
  apply eq_on_closedCylinder_of_initial_eq (f := fun _ ↦ 2)
    (isOpen_domain 1) Metric.isBounded_ball
    ((hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl) hT hu
    (ContDiffUpToBoundary.of_contDiff (contDiff_polynomial 2)
      (isBounded_spaceTimeCylinder Metric.isBounded_ball (Metric.isBounded_Ioo 0 T)))
    hc (contDiff_polynomial 2).continuous.continuousOn _ _ hb _ _
  · apply nonhomogeneousWaveEquation.of_residual
    intro p hp
    change p 0 ∈ Ioo 0 T ∧ spatialPartCLM 1 p ∈ domain 1 at hp
    simpa only [timeSpaceCons_spatialPartCLM] using hPDE _ hp.2 _ hp.1
  · exact nonhomogeneousWaveEquation.of_residual (fun p _ ↦ polynomial_waveOperator p)
  · intro x hx
    change u (timeSpaceCons 0 x) = x 0 ^ 2 + 2 * 0 ^ 2 + 0 * x 0
    simpa using hpos x hx
  · intro x hx
    rw [hvel x hx, polynomial_initial_velocity]

/-- At the two interval endpoints the data are unequal and time dependent. -/
theorem polynomial_lateral_values (t : ℝ) :
    polynomial (timeSpaceCons t (EuclideanSpace.single 0 (-1) : ℝ^1)) = 1 + 2 * t ^ 2 - t ∧
    polynomial (timeSpaceCons t (EuclideanSpace.single 0 1 : ℝ^1)) = 1 + 2 * t ^ 2 + t := by
  constructor
  · change (-1 : ℝ) ^ 2 + 2 * t ^ 2 + t * (-1) = _
    cas
  · change (1 : ℝ) ^ 2 + 2 * t ^ 2 + t * 1 = _
    cas

end WaveEquation.Examples.DirichletUniqueness
