/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.ThreeTermEstimate
public import PDE.Analysis.Evolution.Integrated.GardingSolution
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Three-term data estimate for weak Gårding solutions

The prefix energy inequality controls the pivot and energy norms. The equation
identifies the weak derivative with the residual, giving its dual norm bound.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution.GardingWeakSolutionOn

/-- The weak solution satisfies the same three-term data-only estimate as its
Galerkin approximations. -/
theorem three_term_bound
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {a b theta gamma : ℝ}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))} {uInit : H}
    (U : GardingWeakSolutionOn T B ell uInit a b theta gamma)
    (hab : a ≤ b) (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB) :
    ∀ t ∈ Icc a b,
      ‖U.evolution.representative t‖ + ‖U.state‖ + ‖U.derivative‖ ≤
        gardingThreeTermConstant theta gamma (b - a) MB 1 * (‖uInit‖ + ‖ell‖) := by
  have hw : ContinuousOn U.evolution.representative (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.evolution.continuousOn
  have hp := norm_sq_le_exp_of_garding_energy_bound hw (Lp.memLp ell)
    htheta hgamma hab U.properties.energy
  have hv := integral_norm_sq_le_of_garding_energy_bound hw (Lp.memLp ell)
    htheta hgamma hab U.properties.energy
  have hfNorm : (∫ t in a..b, ‖ell t‖ ^ 2) = ‖ell‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, Lp.norm_sq_eq_integral_norm_sq]
  have huNorm : (∫ t in a..b, ‖U.state t‖ ^ 2) = ‖U.state‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, Lp.norm_sq_eq_integral_norm_sq]
  rw [hfNorm] at hp hv
  rw [huNorm] at hv
  have hg := U.properties.weakDerivative.norm_le_of_integrated_solution
    hB MB hbound U.properties.solution
  have hgs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hg
  have hgv := mul_le_mul_of_nonneg_left hv (sq_nonneg (MB : ℝ))
  intro t ht
  apply three_term_le_of_garding_squared_bounds htheta hgamma (sub_nonneg.mpr hab)
    (norm_nonneg _) (norm_nonneg _) ?_ hv ?_
  · exact (hp t ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
        (by positivity))) (by positivity))
  · nlinarith [sq_nonneg (‖ell‖ - (MB : ℝ) * ‖U.state‖)]

end PDE.Analysis.Evolution.GardingWeakSolutionOn
