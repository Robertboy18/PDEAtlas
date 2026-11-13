/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution

/-!
# Kirchhoff and Duhamel representation

Subtracting the retarded source integral leaves a homogeneous wave with the
original Cauchy data. Uniqueness identifies it with Kirchhoff's formula. The
source only needs its forward derivatives; its negative-time values are unused.
-/

@[expose] public noncomputable section

open PDE (SatisfiesPDEProblem)
open PDE.Analysis PDE.Common

namespace WaveEquation

/-- A classical forced wave is the sum of its free wave and retarded source integral. -/
theorem eq_kirchhoffFormula_add_duhamel {u f : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : ContDiffOn ℝ 2 f {p | 0 ≤ p 0}) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    u (timeSpaceCons t x) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) +
      oddDuhamelSolution 0 f (timeSpaceCons t x) := by
  have hsolu : SatisfiesPDEProblem (forcedWaveResidualAssignedCauchyDataProblem f g h) u := by
    refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
    · intro z hz
      simpa only [timeSpaceCons_spatialPartCLM] using hwave (z 0) hz (spatialPartCLM 3 z)
    · intro z hz
      have he := hposition (spatialPartCLM 3 z)
      rw [← hz, timeSpaceCons_spatialPartCLM] at he
      simpa only [hz] using he
    · intro z hz
      have he := hinitial (spatialPartCLM 3 z)
      rw [← hz, timeSpaceCons_spatialPartCLM] at he
      simpa only [hz] using he
  have hd := contDiff_two_oddDuhamelSolution 0 hf
  have hsolsub : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h)
      (fun z ↦ u z - oddDuhamelSolution 0 f z) := by
    simpa only [sub_self, sub_zero, waveResidualAssignedCauchyDataProblem] using
      forcedWaveResidualAssignedCauchyDataProblem_sub hsolu
        (oddDuhamelSolution_satisfiesResidualAssignedCauchyData 0 hf) hu hd
  have he := eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData
    (hu.sub hd) (contDiff_two_kirchhoffFormula hg hh) hsolsub
      (kirchhoffFormula_satisfiesResidualAssignedCauchyData hg hh) ht x
  exact sub_eq_iff_eq_add.mp he

end WaveEquation
