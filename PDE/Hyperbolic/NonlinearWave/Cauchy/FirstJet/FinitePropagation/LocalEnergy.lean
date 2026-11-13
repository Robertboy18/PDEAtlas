/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedDensity

/-!
# Comparing spatial and weighted energy

An undamped region has energy bounded by the global weighted form. If the
initial energy vanishes on the larger region, its weighted energy is exactly
the exterior damping factor times the total initial energy.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The natural energy density is integrable for every energy state. -/
theorem integrable_energyDensity (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    Integrable (energyDensity z) (domainMeasure n univ) :=
  ((Lp.memLp z.2).integrable_sq.add (Lp.memLp (wkpBaseCoordinateCLM z.1)).integrable_sq).add
      (integrable_finsetSum _ fun i _ ↦
        (Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) z.1)).integrable_sq)

/-- A nonnegative weight equal to one on a set bounds the energy in that set. -/
theorem setIntegral_energyDensity_le_weightedEnergyForm (z : H¹(ℝ^n) × DerivLp n 2 univ)
    (a : DerivLp n ∞ univ) (ha : ∀ᵐ x ∂domainMeasure n univ, 0 ≤ a x) {S : Set (ℝ^n)}
    (hone : ∀ᵐ x ∂(domainMeasure n univ).restrict S, a x = 1) :
    (∫ x in S, energyDensity z x ∂domainMeasure n univ) ≤ weightedEnergyForm a z z := by
  rw [weightedEnergyForm_eq_integral]
  calc
    (∫ x in S, energyDensity z x ∂domainMeasure n univ) =
        ∫ x in S, a x * energyDensity z x ∂domainMeasure n univ := by
      apply integral_congr_ae
      filter_upwards [hone] with x hx
      rw [hx, one_mul]
    _ ≤ ∫ x, a x * energyDensity z x ∂domainMeasure n univ :=
      setIntegral_le_integral (integrable_weighted_energyDensity a z)
        (ha.mono fun x hx ↦ mul_nonneg hx (energyDensity_nonneg z x))

/-- If the energy vanishes in a region and the weight is constant outside,
the weighted energy is that constant times the total energy. -/
theorem weightedEnergyForm_eq_mul_integral_of_vanishing (z : H¹(ℝ^n) × DerivLp n 2 univ)
    (a : DerivLp n ∞ univ) {S : Set (ℝ^n)} (hS : MeasurableSet S) {c : ℝ}
    (hz : ∀ᵐ x ∂(domainMeasure n univ).restrict S, energyDensity z x = 0)
    (ha : ∀ᵐ x ∂domainMeasure n univ, x ∉ S → a x = c) :
    weightedEnergyForm a z z = c * ∫ x, energyDensity z x ∂domainMeasure n univ := by
  rw [weightedEnergyForm_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hS).mp hz, ha] with x hx ha
  by_cases h : x ∈ S
  · rw [hx h, mul_zero, mul_zero]
  · rw [ha h]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
