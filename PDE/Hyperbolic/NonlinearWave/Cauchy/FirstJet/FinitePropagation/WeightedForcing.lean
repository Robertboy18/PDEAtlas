/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedEstimates
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.PositiveQuadraticIntegral

/-!
# Localized seminorm bounds for wave forcing

The full first-jet source is Lipschitz in each nonnegative weighted energy.
Forcing supported outside a region acquires the square root of the exterior
weight. These estimates keep the boundary commutator separate from the
nonlinear source in the local weak uniqueness argument.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

/-- A nonnegative quadratic energy defines a seminorm satisfying the triangle inequality. -/
theorem sqrt_bilinear_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x) (x y : E) :
    Real.sqrt (B (x + y) (x + y)) ≤ Real.sqrt (B x x) + Real.sqrt (B y y) := by
  have hcs := (le_abs_self (B x y)).trans (abs_bilinear_le_sqrt_mul_sqrt B hB hpos x y)
  have he : B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
    simp only [map_add, add_apply, hB y x]
    ring
  apply (Real.sqrt_le_iff).mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [he]
  nlinarith only [Real.sq_sqrt (hpos x), Real.sq_sqrt (hpos y), hcs]

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- A pure acceleration contributes only its weighted spatial L² norm. -/
theorem weightedEnergyForm_zero_pair (a : DerivLp n ∞ univ) (r : DerivLp n 2 univ) :
    weightedEnergyForm a (0, r) (0, r) = ⟪a • r, r⟫_ℝ := by
  simp only [weightedEnergyForm_apply, map_zero, inner_zero_right, Finset.sum_const_zero, add_zero]

/-- A pointwise forcing bound integrates to a bound in the same weighted energy. -/
theorem weightedEnergyForm_zero_pair_le (a : DerivLp n ∞ univ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ a y)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (r : DerivLp n 2 univ) {K : ℝ}
    (hr : ∀ᵐ y ∂domainMeasure n univ, (r y) ^ 2 ≤ K * energyDensity z y) :
    weightedEnergyForm a (0, r) (0, r) ≤ K * weightedEnergyForm a z z := by
  rw [weightedEnergyForm_zero_pair, weighted_pair_eq_integral,
    weightedEnergyForm_eq_integral, ← integral_const_mul]
  apply integral_mono_ae (integrable_weighted_mul a r r)
    ((integrable_weighted_energyDensity a z).const_mul K)
  filter_upwards [ha, hr] with y hy hr
  nlinarith only [mul_le_mul_of_nonneg_left hr hy]

/-- The mass-canceling source has a pointwise difference bound at energy regularity. -/
theorem source_sub_sq_le_energyDensity_ae (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∀ᵐ y ∂domainMeasure n univ, ((source hf hf0 z - source hf hf0 w) y) ^ 2 ≤
      (2 + 2 * (L : ℝ) ^ 2) * energyDensity (z - w) y := by
  have hs : source hf hf0 z - source hf hf0 w =
      wkpBaseCoordinateCLM (z - w).1 - (reaction hf hf0 z - reaction hf hf0 w) := by
    change wkpBaseCoordinateCLM z.1 - reaction hf hf0 z -
      (wkpBaseCoordinateCLM w.1 - reaction hf hf0 w) =
        wkpBaseCoordinateCLM (z.1 - w.1) - (reaction hf hf0 z - reaction hf hf0 w)
    rw [map_sub]
    abel
  rw [hs]
  filter_upwards [reaction_sub_sq_le_energyDensity_ae hf hf0 z w,
    Lp.coeFn_sub (wkpBaseCoordinateCLM (z - w).1)
      (reaction hf hf0 z - reaction hf hf0 w)] with y hr hy
  simp only [Pi.sub_apply] at hy
  rw [hy]
  have hq : (wkpBaseCoordinateCLM (z - w).1 y) ^ 2 ≤ energyDensity (z - w) y := by
    unfold energyDensity
    linarith [sq_nonneg ((z - w).2 y), Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦
        sq_nonneg (wkpCoordinateCLM (singleDerivIndex n i) (z - w).1 y))]
  nlinarith only [hq, hr, sq_nonneg (wkpBaseCoordinateCLM (z - w).1 y +
    (reaction hf hf0 z - reaction hf hf0 w) y)]

/-- The nonlinear source is Lipschitz for every nonnegative spatial energy weight. -/
theorem sqrt_weightedEnergyForm_source_sub_le (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (a : DerivLp n ∞ univ) (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ a y)
    (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    Real.sqrt (weightedEnergyForm a (0, source hf hf0 z - source hf hf0 w)
      (0, source hf hf0 z - source hf hf0 w)) ≤
      Real.sqrt (2 + 2 * (L : ℝ) ^ 2) * Real.sqrt (weightedEnergyForm a (z - w) (z - w)) := by
  have h := Real.sqrt_le_sqrt (weightedEnergyForm_zero_pair_le a ha (z - w)
    (source hf hf0 z - source hf hf0 w) (source_sub_sq_le_energyDensity_ae hf hf0 z w))
  rwa [Real.sqrt_mul (by positivity : 0 ≤ 2 + 2 * (L : ℝ) ^ 2)] at h

/-- A force vanishing in the interior sees only the constant exterior weight. -/
theorem sqrt_weightedEnergyForm_zero_pair_of_vanishing (a : DerivLp n ∞ univ)
    (r : DerivLp n 2 univ) {S : Set (ℝ^n)} (hS : MeasurableSet S) {c : ℝ} (hc : 0 ≤ c)
    (hr : ∀ᵐ y ∂(domainMeasure n univ).restrict S, r y = 0)
    (ha : ∀ᵐ y ∂domainMeasure n univ, y ∉ S → a y = c) :
    Real.sqrt (weightedEnergyForm a (0, r) (0, r)) = Real.sqrt c * ‖r‖ := by
  have he : weightedEnergyForm a (0, r) (0, r) = c * ‖r‖ ^ 2 := by
    rw [weightedEnergyForm_zero_pair, weighted_pair_eq_integral,
      Lp.norm_sq_eq_integral_sq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' hS).mp hr, ha] with y hyr hya
    by_cases hy : y ∈ S
    · rw [hyr hy]
      ring
    · rw [hya hy]
      ring
  rw [he, Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg r)]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
