/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
public import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative

/-!
# Forward energy and smooth representatives

The differential within the closed forward half-space determines the
initial energy. Any smooth extension has the same energy density there,
regardless of the original field's values at negative times.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- Semilinear energy density using the forward differential. At initial
time this depends only on the field on the closed forward half-space. -/
def forwardSemilinearWaveEnergyDensity (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) * ((forwardDifferential u t x (EuclideanSpace.single 0 1)) ^ 2 +
    ‖(WithLp.toLp 2 (fun i : Fin n ↦ forwardDifferential u t x
      (EuclideanSpace.single i.succ 1)) : ℝ^n)‖ ^ 2) +
    V (u (timeSpaceCons (max 0 t) x))

/-- Global forward energy, including the right differential at initial time. -/
def forwardSemilinearWaveEnergy (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∫ x, forwardSemilinearWaveEnergyDensity V u t x

/-- A smooth representative has exactly the differential within the forward
half-space, including at the initial boundary. -/
theorem forwardDifferential_eq_fderiv_of_extension {u U : ℝ^(n + 1) → ℝ} (hU : ContDiff ℝ 2 U)
    (heq : EqOn U u {p | 0 ≤ p 0}) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n) :
    forwardDifferential u t x = fderiv ℝ U (timeSpaceCons t x) := by
  unfold forwardDifferential
  rw [max_eq_right ht, ← fderivWithin_congr' heq (show 0 ≤ (timeSpaceCons t x) 0 by
    simpa only [mem_ofPred_eq, timeSpaceCons_zero] using ht)]
  exact (hU.differentiable (by norm_num) _).fderivWithin
    (uniqueDiffOn_forward_halfSpace _ (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using ht))

/-- Forward energy density agrees pointwise with that of a smooth representative. -/
theorem forwardSemilinearWaveEnergyDensity_eq_of_extension (V : ℝ → ℝ) {u U : ℝ^(n + 1) → ℝ}
    (hU : ContDiff ℝ 2 U) (heq : EqOn U u {p | 0 ≤ p 0}) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n) :
    forwardSemilinearWaveEnergyDensity V u t x = semilinearWaveSpatialEnergyDensity V U t x := by
  unfold forwardSemilinearWaveEnergyDensity semilinearWaveSpatialEnergyDensity
    semilinearWaveEnergyDensity classicalWaveEnergyDensity classicalWaveSpatialGradient
  rw [forwardDifferential_eq_fderiv_of_extension hU heq ht x, max_eq_right ht,
    ← heq (show 0 ≤ (timeSpaceCons t x) 0 by
      simpa only [timeSpaceCons_zero] using ht)]
  rfl

/-- Forward energy agrees with ambient energy of every smooth representative. -/
theorem forwardSemilinearWaveEnergy_eq_of_extension (V : ℝ → ℝ) {u U : ℝ^(n + 1) → ℝ}
    (hU : ContDiff ℝ 2 U) (heq : EqOn U u {p | 0 ≤ p 0}) {t : ℝ} (ht : 0 ≤ t) :
    forwardSemilinearWaveEnergy V u t = semilinearWaveSpatialEnergy V U t :=
  integral_congr_ae (Filter.Eventually.of_forall
    (forwardSemilinearWaveEnergyDensity_eq_of_extension V hU heq ht))

end WaveEquation
