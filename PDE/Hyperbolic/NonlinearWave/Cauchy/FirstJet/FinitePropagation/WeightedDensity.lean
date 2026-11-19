/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedEnergy

/-!
# Spatial density of the first-jet wave energy

The weighted quadratic form is the integral of the squared displacement,
velocity and spatial derivatives. In particular, all integrals used in the
local energy argument are integrable; none relies on a totalized integral.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- The sum of the squares of all natural energy coordinates. -/
def energyDensity (z : H¹(ℝ^n) × DerivLp n 2 univ) (y : ℝ^n) : ℝ :=
  (z.2 y) ^ 2 + (wkpBaseCoordinateCLM z.1 y) ^ 2 +
    ∑ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) z.1 y) ^ 2

/-- The energy density is nonnegative for every chosen representative. -/
theorem energyDensity_nonneg (z : H¹(ℝ^n) × DerivLp n 2 univ) (y : ℝ^n) :
    0 ≤ energyDensity z y :=
  add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Products of two energy coordinates are integrable against bounded weights. -/
theorem integrable_weighted_mul (a : DerivLp n ∞ univ) (b c : DerivLp n 2 univ) :
    Integrable (fun y ↦ a y * b y * c y) (domainMeasure n univ) :=
  ((Lp.memLp a).mul (r := 2) (Lp.memLp b)).integrable_mul (Lp.memLp c)

/-- Weighted L² pairing is the integral of the three real representatives. -/
theorem weighted_pair_eq_integral (a : DerivLp n ∞ univ) (b c : DerivLp n 2 univ) :
    ⟪a • b, c⟫_ℝ = ∫ y, a y * b y * c y ∂domainMeasure n univ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := 2) a b] with y hy
  simp only [hy, smul_eq_mul, Pi.mul_apply, Real.inner_apply]

/-- The spatial energy density is integrable against every bounded weight. -/
theorem integrable_weighted_energyDensity (a : DerivLp n ∞ univ) (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    Integrable (fun y ↦ a y * energyDensity z y) (domainMeasure n univ) := by
  simp only [energyDensity, mul_add, Finset.mul_sum, pow_two, ← mul_assoc]
  exact ((integrable_weighted_mul a z.2 z.2).add
    (integrable_weighted_mul a (wkpBaseCoordinateCLM z.1) (wkpBaseCoordinateCLM z.1))).add
      (integrable_finsetSum _ fun i _ ↦ integrable_weighted_mul a
        (wkpCoordinateCLM (singleDerivIndex n i) z.1) (wkpCoordinateCLM (singleDerivIndex n i) z.1))

/-- The localized quadratic form is the spatial energy integral. -/
theorem weightedEnergyForm_eq_integral (a : DerivLp n ∞ univ) (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    weightedEnergyForm a z z = ∫ y, a y * energyDensity z y ∂domainMeasure n univ := by
  have hv := integrable_weighted_mul a z.2 z.2
  have hu := integrable_weighted_mul a (wkpBaseCoordinateCLM z.1) (wkpBaseCoordinateCLM z.1)
  have hg (i : Fin n) := integrable_weighted_mul a (wkpCoordinateCLM (singleDerivIndex n i) z.1)
    (wkpCoordinateCLM (singleDerivIndex n i) z.1)
  simp only [weightedEnergyForm_apply, weighted_pair_eq_integral, energyDensity,
    mul_add, Finset.mul_sum, pow_two, ← mul_assoc]
  rw [← integral_add hv hu, ← integral_finsetSum _ fun i _ ↦ hg i]
  exact (integral_add (hv.add hu) (integrable_finsetSum _ fun i _ ↦ hg i)).symm

/-- The Euclidean spatial gradient and product-norm first jet are controlled
pointwise almost everywhere by the natural energy density. -/
theorem firstJet_norm_sq_le_energyDensity_ae (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∀ᵐ y ∂domainMeasure n univ, ‖firstJetCLM z y‖ ^ 2 ≤ energyDensity z y := by
  filter_upwards [firstJetCLM_apply_ae z, wkpGradientCLM_apply_ae z.1] with y hj hd
  have hg : ‖∇ z.1 y‖ ^ 2 =
      ∑ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) z.1 y) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun r : ℝ ↦ r ^ 2) (hd i)
  rw [hj, Prod.norm_def, Prod.norm_def]
  change max ‖∇ z.1 y‖ (max ‖z.2 y‖ ‖wkpBaseCoordinateCLM z.1 y‖) ^ 2 ≤ _
  rcases le_total ‖∇ z.1 y‖ (max ‖z.2 y‖ ‖wkpBaseCoordinateCLM z.1 y‖) with h | h
  · rw [max_eq_right h]
    rcases le_total ‖z.2 y‖ ‖wkpBaseCoordinateCLM z.1 y‖ with h | h
    · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]
      unfold energyDensity
      linarith [sq_nonneg (z.2 y), Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) ↦ sq_nonneg (wkpCoordinateCLM (singleDerivIndex n i) z.1 y))]
    · rw [max_eq_left h, Real.norm_eq_abs, sq_abs]
      unfold energyDensity
      linarith [sq_nonneg (wkpBaseCoordinateCLM z.1 y), Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) ↦ sq_nonneg (wkpCoordinateCLM (singleDerivIndex n i) z.1 y))]
  · rw [max_eq_left h, hg]
    unfold energyDensity
    linarith [sq_nonneg (z.2 y), sq_nonneg (wkpBaseCoordinateCLM z.1 y)]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
