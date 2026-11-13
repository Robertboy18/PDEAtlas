/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic
import Mathlib.MeasureTheory.Function.L2Space
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Estimates for the quadratic mass of semilinear waves

Negative semilinear energy makes the spatial quadratic mass strictly positive.
The quadratic momentum also obeys the fixed-time Cauchy-Schwarz estimate

`P(t)² ≤ 2 I(t) ∫ uₜ(t, x)² dx`.

Together with the differentiation formulas, these estimates provide the
analytic input for the negative-energy virial argument. Here `I(t) = ½ ∫ u²` and `P = I'`, so
the momentum bound is the Cauchy-Schwarz inequality `(∫ u uₜ)² ≤ ∫ u² ∫ uₜ²`; it is the step
that turns the virial lower bound on `P'` into the concavity inequality of Levine's method. In
the proof of Evans, §12.5.1, Theorem 1, it is the first inequality of (6), and the positivity of
`I` is the remark in step 2 that negative energy forces `g ≢ 0`.

## Main results

* `waveSpatialQuadraticMass_pos_of_spatialEnergy_neg`: negative semilinear energy forces
  `I(t) > 0`, since a vanishing field has nonnegative energy.
* `waveSpatialQuadraticMomentum_sq_le`: `P(t)² ≤ 2 I(t) ∫ uₜ(t, x)² dx`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, equation (6) and step 2.
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, proof of Theorem I,
  equation (II-3) and the definition of `S²`, p. 6.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

namespace WaveEquation

variable {n : ℕ}

/-- Negative semilinear energy forces the spatial quadratic mass to be
strictly positive when `V(0) = 0`.

If the mass vanished, continuity would make the entire spatial slice zero.
Its spatial gradient and potential energy would then vanish pointwise, leaving
only the nonnegative kinetic density and contradicting negative energy. -/
theorem waveSpatialQuadraticMass_pos_of_spatialEnergy_neg {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hVzero : V 0 = 0) (t : ℝ)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t < 0) :
    0 < waveSpatialQuadraticMass (n := n) u t := by
  have hv : Continuous fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hu x).continuousAt.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  refine (integral_nonneg fun x ↦ mul_nonneg (by norm_num) (sq_nonneg _)).lt_of_ne fun hzero ↦
    henergyNeg.not_ge ?_
  have hdensity : (fun x : ℝ^n ↦ (1 / 2 : ℝ) * u (PDE.Common.timeSpaceCons t x) ^ 2) = 0 :=
    ((continuous_const.mul (hv.pow 2)).ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg
        (f := fun x : ℝ^n ↦ (1 / 2 : ℝ) * u (PDE.Common.timeSpaceCons t x) ^ 2)
        (fun x ↦ mul_nonneg (by norm_num) (sq_nonneg _)) (by
          simpa only [pow_two, Pi.mul_apply] using ((hv.mul hv).integrable_of_hasCompactSupport
            (μ := volume) hcompact.mul_right).const_mul (1 / 2 : ℝ))).mp hzero.symm)
  have hvalue : (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x)) = 0 :=
    funext fun x ↦ by simpa using congrFun hdensity x
  unfold semilinearWaveSpatialEnergy
  refine integral_nonneg fun x ↦ ?_
  have hgradient : classicalWaveSpatialGradient u (PDE.Common.timeSpaceCons t x) = 0 := by
    ext i
    rw [classicalWaveSpatialGradient_apply, ← PDE.partialDeriv_timeSpaceCons_spatial i u t x
      ((hu x).differentiableAt one_ne_zero), hvalue]
    exact PDE.partialDeriv_const 0
  rw [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity, classicalWaveEnergyDensity,
    show u (PDE.Common.timeSpaceCons t x) = 0 from congrFun hvalue x, hgradient, hVzero]
  positivity

/-- Cauchy-Schwarz bounds the square of the quadratic momentum by the
quadratic mass times the kinetic integral:

`P(t)² ≤ 2 I(t) ∫ uₜ²`.

Compact support supplies square-integrability of `u`; square-integrability of
the time derivative remains an explicit hypothesis. -/
theorem waveSpatialQuadraticMomentum_sq_le {u : ℝ^(n + 1) → ℝ} (t : ℝ)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 1 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)))
    (htimeSqIntegrable :
      Integrable (fun x : ℝ^n ↦ ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2)) :
    waveSpatialQuadraticMomentum (n := n) u t ^ 2 ≤
      2 * waveSpatialQuadraticMass (n := n) u t *
        ∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
  let value : ℝ^n → ℝ := fun x ↦ u (PDE.Common.timeSpaceCons t x)
  let timeDerivative : ℝ^n → ℝ := fun x ↦ (∂[0] u) (PDE.Common.timeSpaceCons t x)
  have hv : Continuous value := continuous_iff_continuousAt.mpr fun x ↦ (hu x).continuousAt.comp
    (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have hd : Continuous timeDerivative := continuous_iff_continuousAt.mpr fun x ↦
    (PDE.contDiffAt_partialDeriv 0 (hu x) 0).continuousAt.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous.continuousAt
  have hvLp : MemLp value (ENNReal.ofReal 2) volume := by
    simpa using (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).2 (by
      simpa only [pow_two] using (hv.mul hv).integrable_of_hasCompactSupport
        (f := fun x ↦ value x * value x) (μ := volume) hcompact.mul_right)
  have hdLp : MemLp timeDerivative (ENNReal.ofReal 2) volume := by
    simpa using (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).2 htimeSqIntegrable
  have hcs : (∫ x : ℝ^n, |value x * timeDerivative x|) ≤
      Real.sqrt (∫ x : ℝ^n, value x ^ 2) * Real.sqrt (∫ x : ℝ^n, timeDerivative x ^ 2) := by
    simpa [Real.norm_eq_abs, abs_mul, sq_abs, Real.sqrt_eq_rpow] using
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hvLp hdLp
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
    (abs_integral_le_integral_abs.trans hcs)
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg (value x)),
    Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg (timeDerivative x))] at hsq
  have hmass : waveSpatialQuadraticMass (n := n) u t = (1 / 2 : ℝ) * ∫ x : ℝ^n, value x ^ 2 :=
    integral_const_mul _ _
  simp only [waveSpatialQuadraticMomentum, waveSpatialQuadraticMomentumDensity, value,
    timeDerivative] at hsq ⊢
  rw [hmass]
  nlinarith

end WaveEquation
