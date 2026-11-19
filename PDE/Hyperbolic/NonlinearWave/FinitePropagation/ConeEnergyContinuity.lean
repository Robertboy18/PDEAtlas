/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Basic
public import PDE.Analysis.Integration.Cone.Continuity

/-!
# Cone energy at the vertex

Rescaling to the fixed unit ball proves continuity of shrinking-cone energy
through the terminal vertex. This justifies the upper endpoint of the integration in time that
gives the flux identity (3) of Evans, §12.1.2, Theorem 2(i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i) and its proof, equations (3)-(4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- Rescaling to a fixed compact ball exhibits the vanishing volume at the
cone vertex, including in one spatial dimension. -/
theorem semilinearBackwardConeEnergy_eq_scaled_integral [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : Continuous V) (hu : ContDiff ℝ 1 u) (c : ℝ^n) (T : ℝ) {t : ℝ}
    (ht : t ≤ T) :
    semilinearBackwardConeEnergy V u c T t = (T - t) ^ n * ∫ x in Metric.closedBall (0 : ℝ^n) 1,
      semilinearWaveEnergyDensity V u (timeSpaceCons t (c + (T - t) • x)) := by
  rw [semilinearBackwardConeEnergy_eq_ballIntegral hV hu]
  exact ballIntegral_shrinking_eq_scaled_integral _ c T ht

/-- Smooth cone energy is continuous through both the initial rim and vertex.
The fixed-ball formula supplies endpoint domination directly. -/
theorem continuousOn_semilinearBackwardConeEnergy [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) (T : ℝ) :
    ContinuousOn (semilinearBackwardConeEnergy V u c T) (Iic T) := by
  apply (continuousOn_ballIntegral_shrinking
    (contDiff_semilinearWaveEnergyDensity (m := 1) hV hu).continuous c T).congr
  exact fun t _ ↦ semilinearBackwardConeEnergy_eq_ballIntegral hV.continuous
    (hu.of_le (by norm_num)) c T t

end WaveEquation
