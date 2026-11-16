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
regardless of the original field's values at negative times. The density is
jointly continuous through initial time for a field of class `C¹` on the closed
half-space, and at positive times it is the energy density of the equation.
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

/-- For a continuous potential and a field of class `C¹` on the closed forward half-space, the
forward energy density is jointly continuous in time and space, through initial time. -/
theorem continuous_forwardSemilinearWaveEnergyDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) :
    Continuous (Function.uncurry (forwardSemilinearWaveEnergyDensity V u)) := by
  have hD := continuous_forwardDifferential hu
  have heq : Function.uncurry (forwardSemilinearWaveEnergyDensity V u) = fun p : ℝ × ℝ^n ↦
      (1 / 2 : ℝ) * ((forwardDifferential u p.1 p.2 (EuclideanSpace.single 0 1)) ^ 2 +
        ∑ i : Fin n, (forwardDifferential u p.1 p.2 (EuclideanSpace.single i.succ 1)) ^ 2) +
          V (u (timeSpaceCons (max 0 p.1) p.2)) := by
    funext p
    simp only [Function.uncurry, forwardSemilinearWaveEnergyDensity,
      EuclideanSpace.real_norm_sq_eq]
  rw [heq]
  apply Continuous.add
  · apply continuous_const.mul
    apply Continuous.add
    · exact (hD.clm_apply continuous_const).pow 2
    · exact continuous_finsetSum _ (fun _ _ ↦ (hD.clm_apply continuous_const).pow 2)
  · apply hV.comp
    apply hu.continuousOn.comp_continuous
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        ((continuous_const.max continuous_fst).prodMk continuous_snd))
    exact fun p ↦ le_max_left 0 p.1

/-- At positive times the forward density of any field is the energy density of the equation. -/
theorem forwardSemilinearWaveEnergyDensity_eq {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ}
    (ht : 0 < t) (x : ℝ^n) :
    forwardSemilinearWaveEnergyDensity V u t x = semilinearWaveSpatialEnergyDensity V u t x := by
  simp only [forwardSemilinearWaveEnergyDensity, forwardDifferential_eq_fderiv u ht x,
    max_eq_right ht.le, semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, classicalWaveSpatialGradient, PDE.partialDeriv]

end WaveEquation
