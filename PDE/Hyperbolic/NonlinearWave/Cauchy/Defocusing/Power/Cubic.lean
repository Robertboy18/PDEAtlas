/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Equations
import CAS.ExactTactic

/-!
# The physical cubic specialization of the real-power wave

At exponent three the real-power source is the ordinary cube, and its physical
potential is one quarter of the fourth-power integral. These identities connect
the general energy construction to the polynomial higher Sobolev evolution.

`cubicNonlinearity` names this exponent-three case. Global existence, uniqueness and energy
conservation for `u_tt - Δu + u³ = 0` on `ℝ³` are the general theorems of
`Defocusing.General.Nonlinearity` applied to it.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

/-- The real-power source at exponent three is the ordinary cube almost everywhere. -/
theorem source_three_ae (q : H¹(ℝ^3)) :
    source (p := 3) (by norm_num) le_rfl q =ᵐ[domainMeasure 3 univ]
      fun x ↦ ((energyTriple 3).inclusion q x) ^ 3 := by
  filter_upwards [source_ae (p := 3) (by norm_num) le_rfl q] with x hx
  rw [hx]
  unfold Real.signedPower
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, sq_abs]
  cas

/-- At exponent three the signed-power potential is the usual quartic density. -/
theorem signedPowerPotential_three (a : ℝ) :
    Real.signedPowerPotential 3 a = (1 / 4 : ℝ) * a ^ 4 := by
  unfold Real.signedPowerPotential
  rw [show (3 : ℝ) + 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    (show Even 4 by decide).pow_abs]
  cas

/-- The quartic density is integrable for every H¹(ℝ³) function: `integrable_potential` at
exponent three. -/
theorem integrable_pow_four (u : H¹(ℝ^3)) :
    Integrable (fun x ↦ ((energyTriple 3).inclusion u x) ^ 4) (volume : Measure (ℝ^3)) := by
  have h := (integrable_potential (p := 3) (by norm_num) le_rfl u).const_mul 4
  simpa only [signedPowerPotential_three, ← mul_assoc, show (4 : ℝ) * (1 / 4) = 1 by
    norm_num, one_mul, domainMeasure, Measure.restrict_univ] using h

/-- The potential at exponent three is one quarter of the spatial fourth-power integral. -/
theorem potential_three_eq_integral (u : H¹(ℝ^3)) :
    potential 3 u = (1 / 4 : ℝ) * ∫ x : ℝ^3, ((energyTriple 3).inclusion u x) ^ 4 := by
  simp only [potential, signedPowerPotential_three, integral_const_mul,
    domainMeasure, Measure.restrict_univ]

/-- The L² pairing of the cubic source is the integral of the pointwise cube: `inner_source` at
exponent three. -/
theorem inner_source_three (q w : H¹(ℝ^3)) :
    ⟪source (p := 3) (by norm_num) le_rfl q, (energyTriple 3).inclusion w⟫_ℝ = ∫ x : ℝ^3,
      ((energyTriple 3).inclusion q x) ^ 3 * (energyTriple 3).inclusion w x := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, sq_abs, ← pow_succ] using
    inner_source (p := 3) (by norm_num) le_rfl q w

/-- The general cubic energy is kinetic plus weak-gradient plus quartic potential energy. -/
theorem energy_three_eq_integral (z : H¹(ℝ^3) × DerivLp 3 2 univ) :
    (nonlinearity (p := 3) (by norm_num) le_rfl).energy z =
      (1 / 2 : ℝ) * ((∑ i : Fin 3, ‖z.1.val (singleDerivIndex 3 i)‖ ^ 2) + ‖z.2‖ ^ 2) +
        (1 / 4 : ℝ) * ∫ x : ℝ^3, ((energyTriple 3).inclusion z.1 x) ^ 4 := by
  rw [energy_eq_physicalEnergy]
  simp only [physicalEnergy, show (3 : ℝ) + 1 = (4 : ℕ) by norm_num,
    Real.rpow_natCast, (show Even 4 by decide).pow_abs]
  ring

/-- The dual acceleration pairs with the cube and the weak spatial gradients. -/
theorem acceleration_three_apply (q w : H¹(ℝ^3)) :
    (nonlinearity (p := 3) (by norm_num) le_rfl).acceleration q w =
      -(∫ x : ℝ^3, ((energyTriple 3).inclusion q x) ^ 3 *
        (energyTriple 3).inclusion w x) -
      ∑ i : Fin 3, ⟪q.val (singleDerivIndex 3 i), w.val (singleDerivIndex 3 i)⟫_ℝ := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, sq_abs,
    ← pow_succ] using acceleration_apply (p := 3) (by norm_num) le_rfl q w

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- The cubic defocusing nonlinearity `u ↦ u³` on `H¹(ℝ³)`, with potential `¼ ∫ u⁴`: the
real-power nonlinearity of exponent three. -/
abbrev cubicNonlinearity : General.Nonlinearity 3 :=
  Power.nonlinearity (p := 3) (by norm_num) le_rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
