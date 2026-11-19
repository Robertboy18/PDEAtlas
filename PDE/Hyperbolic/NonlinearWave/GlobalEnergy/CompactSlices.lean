/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SupportPropagation
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlab

/-!
# Conservation from separately compact spatial slices

For a C² potential, hence a C¹ reaction, Baire category supplies one local
common support region, and finite propagation transports it across each finite slab.
The resulting compact support justifies spatial integration and continuity at
the initial time. No uniform-support hypothesis is imposed on the solution.
This is the energy conservation of Evans, §12.1.1, Theorem 1, for a `C²` potential.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common

namespace WaveEquation

variable {n : ℕ}

/-- Global energy conservation for a C² potential under separate compact spatial slices.
The equation is required only at positive times, and compact support only at
nonnegative times. Local common support and endpoint integration are derived. -/
theorem semilinearWaveSpatialEnergy_eq_of_compact_slices [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 2 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    semilinearWaveSpatialEnergy V u t = semilinearWaveSpatialEnergy V u 0 := by
  have hf : ContDiff ℝ 1 (deriv V) := hV.deriv'
  have hpde (s : ℝ) (hs' : 0 ≤ s) (x : ℝ^n) :=
    semilinearWaveOperator_eq_zero_of_nonneg hf.continuous hu hwave hs' x
  obtain ⟨R, _, hR⟩ := exists_uniform_support_on_Icc_of_compact_slices hf.locallyLipschitz hu
    (fun s hs' x ↦ add_eq_zero_iff_eq_neg.mp (hpde s hs' x)) hs
    (show 0 ≤ t + 1 by linarith)
  apply semilinearWaveSpatialEnergy_eq_of_compact_support_on_Icc
    (K := Metric.closedBall (0 : ℝ^n) R) (T := t + 1)
    (hV.of_le (by norm_num)) hVzero hu (isCompact_closedBall _ _) (by linarith)
    (fun s hs' x hx ↦ hR s hs' x (by simpa only [Metric.mem_closedBall, dist_zero_right,
      not_le] using hx)) (fun s hs' x ↦ hwave s hs'.1 x)
  exact ⟨ht, by linarith⟩

end WaveEquation
