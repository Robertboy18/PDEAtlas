/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Basic
import PDE.Analysis.Calculus.MovingBall
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.Classical.MovingBallTransport

/-!
# Transport of semilinear cone energy

We differentiate the semilinear energy on a shrinking ball. The
Reynolds derivative is the integral of the local energy-balance residual plus
the lateral boundary flux. On a classical solution, the residual vanishes and
only the boundary term remains.

This is the differentiated form of the energy-on-cones argument for finite
propagation speed (Evans, §2.4.3(b), Theorem 6, for the linear wave equation, and §12.1.2,
Theorem 2, for semilinear waves): the energy in the ball `B(c, T - t)`, which shrinks at unit
speed, has derivative equal to the lateral flux through the sphere `∂B(c, T - t)`, as in (4) of
§12.1.2. We compute only the derivative; the sign of the flux is proved in
`FinitePropagation.Basic` and the vanishing theorems in `FinitePropagation.QuadraticLowerBound`.

## Main results

* `hasDerivAt_semilinearBackwardConeEnergy`: the exact Reynolds transport
  identity for the cone energy of any `C²` field, valid without the equation.
* `hasDerivAt_semilinearBackwardConeEnergy_of_solution`: for a solution of
  `u_tt - Δu + V'(u) = 0` on the slice, only the boundary flux remains.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3(b), Theorem 6 and its proof; §12.1.2, proof of
  Theorem 2, equation (4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis Set
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- The semilinear volume residual is the integral of the classical residual
and the potential-energy time derivative. -/
private theorem ballIntegral_semilinearWaveEnergyBalanceResidual_eq_add
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (c : ℝ^n)
    (t r : ℝ) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyBalanceResidual V u (PDE.Common.timeSpaceCons t x))
        c r =
      ballIntegral n (fun x ↦ classicalWaveEnergyBalanceResidual u (PDE.Common.timeSpaceCons t x))
          c r +
        ballIntegral n (fun x ↦ (∂[0] (fun p ↦ V (u p))) (PDE.Common.timeSpaceCons t x)) c r := by
  have hspace := (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hball {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball c r) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      Metric.ball_subset_closedBall
  unfold ballIntegral semilinearWaveEnergyBalanceResidual
  exact integral_add
    (hball ((contDiff_classicalWaveEnergyBalanceResidual (m := 0) hu).continuous.comp hspace))
    (hball ((PDE.contDiff_partialDeriv_of_succ (m := 0) (i := 0)
      (hV.comp (hu.of_le (by norm_num)))).continuous.comp hspace))

/-- Exact Reynolds derivative of the semilinear energy on a shrinking ball.

The derivative is the integral of the local energy-balance residual plus the
lateral boundary contribution. -/
theorem hasDerivAt_semilinearBackwardConeEnergy [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T) :
    HasDerivAt (semilinearBackwardConeEnergy (n := n) V u c T)
      (ballIntegral n
          (fun x ↦ semilinearWaveEnergyBalanceResidual (n := n) V u
            (PDE.Common.timeSpaceCons (n := n) t x)) c (T - t) +
        sphereIntegral n (semilinearWaveConeBoundaryFlux (n := n) V u c t) c (T - t)) t := by
  have hW : ContDiff ℝ 1 fun p ↦ V (u p) := hV.comp (hu.of_le (by norm_num))
  have htime : ballIntegral n (fun x ↦ fderiv ℝ (Function.uncurry fun s x ↦
      V (u (PDE.Common.timeSpaceCons s x))) (t, x) ((1 : ℝ), (0 : ℝ^n))) c (T - t) =
        ballIntegral n (fun x ↦ (∂[0] fun p ↦ V (u p)) (PDE.Common.timeSpaceCons t x)) c (T - t) :=
    setIntegral_congr_fun measurableSet_ball fun x _ ↦
      PDE.fderiv_timeSpaceCons_time _ t x (hW.differentiable one_ne_zero).differentiableAt
  refine ((hasDerivAt_backwardConeEnergy hu c T ht).add (hasDerivAt_ballIntegral_shrinking
    (fun s x ↦ V (u (PDE.Common.timeSpaceCons s x)))
    (hW.comp (PDE.Common.contDiff_timeSpaceCons_uncurry n)) c T (sub_pos.mpr ht))).congr_deriv ?_
  rw [htime, ballIntegral_semilinearWaveEnergyBalanceResidual_eq_add hV hu c t (T - t),
    sphereIntegral_semilinearWaveConeBoundaryFlux_eq_sub hV hu c t (sub_pos.mpr ht)]
  ring

/-- For a semilinear wave, the shrinking-cone energy derivative consists
only of the lateral boundary contribution. -/
theorem hasDerivAt_semilinearBackwardConeEnergy_of_solution [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T)
    (hwave : ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0) :
    HasDerivAt (semilinearBackwardConeEnergy (n := n) V u c T)
      (sphereIntegral n (semilinearWaveConeBoundaryFlux (n := n) V u c t) c (T - t)) t := by
  refine (hasDerivAt_semilinearBackwardConeEnergy hV hu c T ht).congr_deriv ?_
  rw [ballIntegral, setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦
    semilinearWaveEnergyBalanceResidual_eq_zero hV hu.contDiffAt (hwave x hx), zero_add]

end WaveEquation
