/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Spatial integrating factors for two diagonal equations

The other invariant varies along a characteristic while its own invariant stays
fixed. Integrating in that other coordinate gives a weight with a bound depending
only on the invariant rectangle. The denominator is the signed speed difference,
for either characteristic family.

The integral starts at the initial other coordinate. By additivity of interval
integrals, this is the difference of the two primitives based at zero.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace PDE.Hyperbolic.Quasilinear.Diagonal

variable {B : Fin 2 → (Fin 2 → ℝ) → ℝ}

/-- The mixed derivative divided by the signed difference of transport speeds. -/
def transverseRatio (B : Fin 2 → (Fin 2 → ℝ) → ℝ) (i : Fin 2) (z : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ (B i) z (Pi.single i.rev 1) / (B i z - B i.rev z)

/-- The spatial integrating factor, normalized at the initial state. -/
def spatialWeight (B : Fin 2 → (Fin 2 → ℝ) → ℝ) (i : Fin 2)
    (z : Fin 2 → ℝ) (q : ℝ) : ℝ :=
  Real.exp (∫ r in z i.rev..q, transverseRatio B i (Function.update z i.rev r))

/-- A nonvanishing speed gap makes the transverse ratio continuous. -/
theorem continuous_transverseRatio (hB : ∀ i, ContDiff ℝ 1 (B i)) (hgap : ∀ i z, B i z ≠ B i.rev z)
    (i : Fin 2) :
    Continuous (transverseRatio B i) :=
  ((hB i).continuous_fderiv (by simp) |>.clm_apply continuous_const).div
    ((hB i).continuous.sub (hB i.rev).continuous) (fun z ↦ sub_ne_zero.mpr (hgap i z))

/-- The spatial weight solves the scalar equation determined by the transverse ratio. -/
theorem hasDerivAt_spatialWeight (hB : ∀ i, ContDiff ℝ 1 (B i)) (hgap : ∀ i z, B i z ≠ B i.rev z)
    (i : Fin 2) (z : Fin 2 → ℝ) (q : ℝ) :
    HasDerivAt (spatialWeight B i z)
      (transverseRatio B i (Function.update z i.rev q) * spatialWeight B i z q) q := by
  have hc : Continuous (fun r ↦ transverseRatio B i (Function.update z i.rev r)) :=
    (continuous_transverseRatio hB hgap i).comp (continuous_const.update i.rev continuous_id)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (z i.rev) q)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun r ↦ spatialWeight B i z r) _ q
  simpa only [spatialWeight, mul_comm] using hd.exp

/-- The spatial weight is continuous along the varying invariant coordinate. -/
theorem continuous_spatialWeight (hB : ∀ i, ContDiff ℝ 1 (B i)) (hgap : ∀ i z, B i z ≠ B i.rev z)
    (i : Fin 2) (z : Fin 2 → ℝ) :
    Continuous (spatialWeight B i z) :=
  continuous_iff_continuousAt.mpr fun q ↦ (hasDerivAt_spatialWeight hB hgap i z q).continuousAt

/-- Exponentiation makes the spatial weight strictly positive. -/
theorem spatialWeight_pos (i : Fin 2) (z : Fin 2 → ℝ) (q : ℝ) :
    0 < spatialWeight B i z q :=
  Real.exp_pos _

/-- At the initial transverse coordinate the weight is one. -/
@[simp]
theorem spatialWeight_initial (i : Fin 2) (z : Fin 2 → ℝ) :
    spatialWeight B i z (z i.rev) = 1 := by
  simp [spatialWeight]

/-- A bound on the ratio over a state cube bounds the entire spatial weight.
No derivative of a solution occurs in this estimate. -/
theorem spatialWeight_le_exp {R Q : ℝ} (hQ : 0 ≤ Q) (i : Fin 2) {z : Fin 2 → ℝ} {q : ℝ}
    (hz : z ∈ Icc (fun _ ↦ -R) (fun _ ↦ R)) (hq : q ∈ Icc (-R) R)
    (hbound : ∀ w ∈ Icc (fun _ : Fin 2 ↦ -R) (fun _ ↦ R), ‖transverseRatio B i w‖ ≤ Q) :
    spatialWeight B i z q ≤ Real.exp (2 * Q * R) := by
  have hnorm : ‖∫ r in z i.rev..q,
      transverseRatio B i (Function.update z i.rev r)‖ ≤ Q * |q - z i.rev| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hrange : r ∈ Icc (-R) R :=
      uIcc_subset_Icc ⟨hz.1 i.rev, hz.2 i.rev⟩ hq (uIoc_subset_uIcc hr)
    apply hbound
    constructor <;> intro j <;> by_cases hj : j = i.rev
    · simpa [hj] using hrange.1
    · simpa [Function.update_of_ne hj] using hz.1 j
    · simpa [hj] using hrange.2
    · simpa [Function.update_of_ne hj] using hz.2 j
  have hdist : |q - z i.rev| ≤ 2 * R :=
    abs_le.mpr ⟨by linarith [hz.2 i.rev, hq.1], by linarith [hz.1 i.rev, hq.2]⟩
  apply Real.exp_le_exp.mpr
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hdist hQ).trans_eq (by ring))

end PDE.Hyperbolic.Quasilinear.Diagonal
