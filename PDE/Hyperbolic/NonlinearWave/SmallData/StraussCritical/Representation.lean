/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.SphericalReduction
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution

/-!
# The characteristic formula for the spherical reduction

Uniqueness identifies the reduced forced wave with the one-dimensional
d'Alembert and retarded formulas. The odd source allows the inner integral to
start at the absolute value of its lower endpoint, making positivity visible.
-/

@[expose] public noncomputable section

open PDE (SatisfiesPDEProblem)
open MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- An odd integrand has the same integral after reflecting a negative lower endpoint. -/
theorem integral_odd_abs_lower {f : ℝ → ℝ} (hf : Continuous f) (ho : Function.Odd f) (a b : ℝ) :
    (∫ r in a..b, f r) = ∫ r in |a|..b, f r := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have hzero : (∫ r in a..-a, f r) = 0 := by
      have he := intervalIntegral.integral_comp_neg (f := f) (a := a) (b := -a)
      have heq : (fun x ↦ f (-x)) = fun x ↦ -f x := funext ho
      rw [heq, intervalIntegral.integral_neg] at he
      simp only [neg_neg] at he
      linarith
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable a (-a)) (hf.intervalIntegrable (-a) b)
    rw [hzero, zero_add] at he
    exact he.symm

/-- The one-dimensional retarded formula with its two ordinary integrals exposed. -/
theorem dAlembertDuhamelSolution_eq_double_integral (f : ℝ^2 → ℝ) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    dAlembertDuhamelSolution f (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      ∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) * ∫ ρ in (r - (t - s))..(r + (t - s)),
      f (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) ρ)) := by
  unfold dAlembertDuhamelSolution retardedWave retardedIntegral
  simp only [splitSpaceTime, PDE.time, spatialPart_timeSpaceCons, joinSpaceTime,
    dAlembertSolution1D, dAlembertFormula, timeSpaceCons_zero,
    timeSpaceCons_single_one, zero_add, mul_zero]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  simp only [max_eq_right hs.1]

/-- A forced classical one-dimensional wave with zero displacement has the
free-plus-retarded representation. -/
theorem eq_dAlembert_add_duhamel {v f : ℝ^2 → ℝ} {h : ℝ^1 → ℝ} (hv : ContDiff ℝ 2 v)
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 (fun r ↦ h (EuclideanSpace.single (0 : Fin 1) r)))
    (hwave : ∀ z, 0 < z 0 → waveOperator v z = f z) (hzero : ∀ x : ℝ^1, v (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^1, (∂[0] v) (timeSpaceCons 0 x) = h x) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    v (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      dAlembertSolution1D (fun _ ↦ 0) h
        (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) +
      dAlembertDuhamelSolution f
        (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) := by
  have hsol : SatisfiesPDEProblem
      (forcedWaveResidualAssignedCauchyDataProblem f (fun _ ↦ 0) h) v := by
    apply forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial hwave
    · intro z hz
      have he := hzero (spatialPartCLM 1 z)
      rw [← hz, timeSpaceCons_spatialPartCLM] at he
      simpa only [hz] using he
    · intro z hz
      have he := hinitial (spatialPartCLM 1 z)
      rw [← hz, timeSpaceCons_spatialPartCLM] at he
      simpa only [hz] using he
  have hd := contDiff_two_dAlembertDuhamelSolution hf.contDiffOn
  have hsub : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (fun _ ↦ 0) h)
      (fun z ↦ v z - dAlembertDuhamelSolution f z) := by
    simpa only [sub_self, sub_zero, waveResidualAssignedCauchyDataProblem] using
      forcedWaveResidualAssignedCauchyDataProblem_sub hsol
        (dAlembertDuhamelSolution_satisfiesResidualAssignedCauchyData hf.contDiffOn) hv hd
  exact sub_eq_iff_eq_add.mp (eq_dAlembertSolution1D_of_satisfiesResidualAssignedCauchyData
      (hv.sub hd) contDiff_const hh hsub ht (EuclideanSpace.single (0 : Fin 1) r))

/-- The velocity trace of the reduced profile is the reduced initial velocity. -/
theorem partialDeriv_radiusMean_initial {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (x : ℝ^1) :
    (∂[0] (radiusMean u)) (timeSpaceCons 0 x) = x 0 * unitSphereAverage 3 h 0 (x 0) := by
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ x 0
    ((contDiff_radiusMean hu).differentiable (by norm_num)).differentiableAt]
  have he : (fun s ↦ radiusMean u (timeSpaceCons s x)) =
      fun s ↦ (x 0) * waveSphericalMean u 0 s (x 0) := by
    funext s
    simp only [radiusMean, timeSpaceCons_zero,
      show (1 : Fin 2) = (0 : Fin 1).succ from rfl, timeSpaceCons_succ]
  rw [he, deriv_const_mul_field,
    (hasDerivAt_waveSphericalMean_time u 0 0 (x 0) (hu.of_le (by norm_num))).deriv]
  simp only [hinitial]

/-- The three-dimensional forced wave gives the positive-radius characteristic
formula, with no radial symmetry assumption on the wave or its data. -/
theorem radiusMean_eq_characteristic_integrals {u f : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    radiusMean u (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      (1 / 2 : ℝ) * (∫ ρ in |r - t|..(r + t), ρ * unitSphereAverage 3 h 0 ρ) +
      ∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) *
        ∫ ρ in |r - (t - s)|..(r + (t - s)),
          ρ * waveSphericalMean f 0 s ρ := by
  let h₁ := fun x : ℝ^1 ↦ x 0 * unitSphereAverage 3 h 0 (x 0)
  have hh₁ : ContDiff ℝ 1 (fun r ↦ h₁ (EuclideanSpace.single (0 : Fin 1) r)) := by
    have hm : ContDiff ℝ 1 (unitSphereAverage 3 h 0) :=
      (contDiff_unitSphereAverage hh).comp (contDiff_const.prodMk contDiff_id)
    simpa only [h₁, PiLp.single_apply, ↓reduceIte, id_eq] using contDiff_id.mul hm
  have hsol := eq_dAlembert_add_duhamel (contDiff_radiusMean hu) (contDiff_radiusMean hf)
    hh₁ (h := h₁) ?_ ?_ (partialDeriv_radiusMean_initial hu hinitial) ht r
  · rw [hsol, dAlembertDuhamelSolution_eq_double_integral _ ht]
    have ho : Function.Odd (fun ρ ↦ ρ * unitSphereAverage 3 h 0 ρ) := by
      intro ρ
      simp only [unitSphereAverage_neg_radius, neg_mul]
    have hc : Continuous (fun ρ ↦ ρ * unitSphereAverage 3 h 0 ρ) := (contDiff_id.mul
        ((contDiff_unitSphereAverage hh).comp (contDiff_const.prodMk contDiff_id))).continuous
    simp only [dAlembertSolution1D, dAlembertFormula, timeSpaceCons_zero,
      timeSpaceCons_single_one, h₁, PiLp.single_apply, ↓reduceIte, zero_add, mul_zero, radiusMean]
    rw [integral_odd_abs_lower hc ho]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    congr 1
    have hm : Continuous (fun ρ ↦ waveSphericalMean f 0 s ρ) := ((contDiff_unitSphereAverage
        (hf.comp (contDiff_timeSpaceCons_spatial 3 s))).comp
          (contDiff_const.prodMk contDiff_id)).continuous
    exact integral_odd_abs_lower (continuous_id.fun_mul hm)
      (fun ρ ↦ by
        simp only [id_eq, waveSphericalMean, unitSphereAverage_neg_radius, neg_mul]) _ _
  · intro z hz
    have he : timeSpaceCons (z 0) (EuclideanSpace.single (0 : Fin 1) (z 1)) = z := by
      ext i
      fin_cases i
      · exact timeSpaceCons_zero _ _
      · exact timeSpaceCons_single_one _ _
    rw [← he]
    exact waveOperator_radiusMean hu hf.continuous (hwave (z 0) hz) (z 1)
  · intro x
    simp only [radiusMean, waveSphericalMean, timeSpaceCons_zero, hzero,
      unitSphereAverage, integral_zero, zero_div, mul_zero]

end WaveEquation.SmallData
