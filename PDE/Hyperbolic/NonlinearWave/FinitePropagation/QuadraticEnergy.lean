/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.EnergyGrowth

/-!
# Quadratic energy on shrinking cones

Adding the displacement square to the classical wave energy lets us control
lower-order terms. If the local balance residual is bounded by `C` times this
augmented density, the energy grows at most exponentially. The boundary flux
has the favorable sign because the ball shrinks at the wave speed.

The estimate is independent of the particular equation. Scalar reactions and
reactions depending on the first derivatives use the same transport argument.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A pointwise residual bound controls the derivative of the quadratic cone energy. -/
theorem deriv_quadraticConeEnergy_le [Fact (0 < n)] {w : ℝ^(n + 1) → ℝ} (hw : ContDiff ℝ 2 w)
    (c : ℝ^n) (T : ℝ) {t C : ℝ} (ht : t < T)
    (hbound : ∀ x ∈ Metric.ball c (T - t), semilinearWaveEnergyBalanceResidual
      (fun z : ℝ ↦ z ^ 2 / 2) w (timeSpaceCons t x) ≤
      C * semilinearWaveEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) w (timeSpaceCons t x)) :
    deriv (semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) w c T) t ≤
      C * semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) w c T t :=
  deriv_semilinearBackwardConeEnergy_le (by fun_prop) hw c T ht
    (fun _ _ ↦ by positivity) hbound

/-- The quadratic energy on a backward cone grows at most at the prescribed exponential rate. -/
theorem quadraticConeEnergy_le_exp [Fact (0 < n)] {w : ℝ^(n + 1) → ℝ} (hw : ContDiff ℝ 2 w)
    (c : ℝ^n) {a T C : ℝ}
    (hbound : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveEnergyBalanceResidual
      (fun z : ℝ ↦ z ^ 2 / 2) w (timeSpaceCons t x) ≤
      C * semilinearWaveEnergyDensity (fun z : ℝ ↦ z ^ 2 / 2) w (timeSpaceCons t x))
    {t : ℝ} (ht : t ∈ Ico a T) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) w c T t ≤
      semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) w c T a * Real.exp (C * (t - a)) :=
  semilinearBackwardConeEnergy_le_exp (by fun_prop) hw c
    (fun _ _ _ _ ↦ by positivity) hbound ht

end WaveEquation
