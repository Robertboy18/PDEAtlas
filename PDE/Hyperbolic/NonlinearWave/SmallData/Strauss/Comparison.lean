/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.PowerSource
public import PDE.Hyperbolic.Models.Wave.Duhamel.Kirchhoff

/-!
# Positive Kirchhoff comparison for the superquadratic wave

Nonnegative forcing puts a classical wave above the full free wave with the
same Cauchy data. The free wave may change sign; nonnegativity of the data is
only needed when we also want the free velocity potential to be nonnegative.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common

namespace WaveEquation.SmallData

/-- The velocity potential preserves nonnegativity at forward times. -/
theorem kirchhoffPotential_nonneg {h : ℝ^3 → ℝ} (hh : ∀ x, 0 ≤ h x) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    0 ≤ kirchhoffPotential h (timeSpaceCons t x) := by
  rw [kirchhoffPotential_timeSpaceCons]
  exact mul_nonneg ht (div_nonneg (integral_nonneg fun _ ↦ hh _) unitSphereArea_pos.le)

/-- The three-dimensional retarded potential preserves nonnegativity of a forward source. -/
theorem oddDuhamelSolution_zero_nonneg {f : ℝ^4 → ℝ}
    (hf : ∀ s, 0 ≤ s → ∀ y : ℝ^3, 0 ≤ f (timeSpaceCons s y)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    0 ≤ oddDuhamelSolution 0 f (timeSpaceCons t x) := by
  rw [oddDuhamelSolution_eq_integral 0 f x ht]
  norm_num only [Nat.mul_zero, zero_add, Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul]
  refine intervalIntegral.integral_nonneg ht fun s hs ↦ ?_
  rw [oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  exact mul_nonneg (sub_nonneg.mpr hs.2)
    (div_nonneg (integral_nonneg fun _ ↦ hf s hs.1 _) unitSphereArea_pos.le)

/-- Uniqueness identifies a classical forced wave with its free and retarded potentials. -/
theorem eq_kirchhoffPotential_add_duhamel {u f : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    u (timeSpaceCons t x) = kirchhoffPotential h (timeSpaceCons t x) +
      oddDuhamelSolution 0 f (timeSpaceCons t x) := by
  simpa only [kirchhoffFormula_zero_displacement hh.continuous] using
    eq_kirchhoffFormula_add_duhamel hu hf.contDiffOn contDiff_const hh hwave hzero hinitial ht x

/-- A superquadratic semilinear wave with zero displacement dominates its free wave. -/
theorem kirchhoffPotential_le_semilinear {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {p : ℝ} (hu : ContDiff ℝ 2 u)
    (hh : ContDiff ℝ 2 h) (hp : 2 < p)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    kirchhoffPotential h (timeSpaceCons t x) ≤ u (timeSpaceCons t x) := by
  rw [eq_kirchhoffPotential_add_duhamel hu ((contDiff_two_abs_rpow hp.le).comp hu)
    hh hwave hzero hinitial ht x]
  exact le_add_of_nonneg_right (oddDuhamelSolution_zero_nonneg
    (fun _ _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _) ht x)

/-- The full free wave, with signed displacement and velocity, lies below a wave
with nonnegative forcing. -/
theorem kirchhoffFormula_le_of_nonneg_source {u f : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x)
    (hfpos : ∀ s, 0 ≤ s → ∀ y : ℝ^3, 0 ≤ f (timeSpaceCons s y)) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) ≤ u (timeSpaceCons t x) := by
  rw [eq_kirchhoffFormula_add_duhamel hu hf.contDiffOn hg hh hwave hposition hinitial ht x]
  exact le_add_of_nonneg_right (oddDuhamelSolution_zero_nonneg hfpos ht x)

end WaveEquation.SmallData
