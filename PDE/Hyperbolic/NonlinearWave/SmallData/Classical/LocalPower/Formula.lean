/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Operator
public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Identifying the normalized integral with the classical Duhamel solution

An ordinary linear change of time identifies the normalized cone integral
with the three-dimensional retarded potential. The identification
uses the original source at every nonnegative time in the integral.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common
open PDE (partialDeriv laplacian)
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower

/-- Integration on the unit-interval subtype is the usual oriented integral
from zero to one. -/
theorem integral_unitInterval (g : ℝ → ℝ) :
    (∫ s : I, g s) = ∫ s in (0 : ℝ)..1, g s := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

/-- The Duhamel solution equals the normalized cone integral. -/
theorem oddDuhamelSolution_zero_eq_normalized (F : ℝ^4 → ℝ) (x : ℝ^3) {t : ℝ} (ht : 0 ≤ t) :
    oddDuhamelSolution 0 F (timeSpaceCons t x) = t ^ 2 * ∫ s : I,
      (1 - (s : ℝ)) * ((∫ ω : Direction, F (timeSpaceCons (t * (s : ℝ)) (x + t • ((1 - (s : ℝ)) •
      (ω : ℝ^3)))) ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  rw [oddDuhamelSolution_eq_integral 0 F x ht]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  let g : ℝ → ℝ := fun s ↦ (t - s) * unitSphereAverage 3 (fun y ↦ F (timeSpaceCons s y)) x (t - s)
  have hscale : t * (∫ s in (0 : ℝ)..1, g (t * s)) = ∫ s in (0 : ℝ)..t, g s := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left g t (a := 0) (b := 1)
  let a : ℝ → ℝ := fun s ↦ (1 - s) * ((∫ ω : Direction, F (timeSpaceCons (t * s)
      (x + t • ((1 - s) • (ω : ℝ^3)))) ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)
  change (∫ s in (0 : ℝ)..t, g s) = t ^ 2 * ∫ s : I, a s
  rw [← hscale, integral_unitInterval a, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  have hr : t - t * s = t * (1 - s) := by cas
  simp only [g, a, hr, unitSphereAverage, smul_smul]
  cas

/-- The free Kirchhoff field also satisfies the homogeneous equation on the
initial hyperplane, where its acceleration and its spatial slice vanish. -/
theorem waveOperator_kirchhoffPotential_initial {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 2 h) (x : ℝ^3) :
    waveOperator (kirchhoffPotential h) (timeSpaceCons 0 x) = 0 := by
  rw [waveOperator, secondPartialDeriv_kirchhoffPotential_initial hh,
    ← laplacian_timeSlice _ _ _ (contDiff_kirchhoffPotential hh)]
  simp only [kirchhoffPotential_timeSpaceCons, zero_mul, PDE.laplacian_const, sub_zero]

/-- The free Kirchhoff field solves the equation up to and including its
ordinary initial slice. -/
theorem waveOperator_kirchhoffPotential_nonneg {h : ℝ^3 → ℝ}
    (hh : ContDiff ℝ 2 h) {p : ℝ^4} (hp : 0 ≤ p 0) :
    waveOperator (kirchhoffPotential h) p = 0 := by
  rcases hp.eq_or_lt with hzero | hpos
  · have he := waveOperator_kirchhoffPotential_initial hh (spatialPartCLM 3 p)
    conv_lhs at he => rw [hzero, timeSpaceCons_spatialPartCLM]
    exact he
  · exact waveOperator_kirchhoffPotential hh hpos

end WaveEquation.SmallData.Classical.LocalPower
