/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Planar logarithmic potentials with noncompact data

In two dimensions the fundamental solution `Φ(x) = -(2π)⁻¹ log ‖x‖` grows at
infinity, so the Newtonian (logarithmic) potential `Φ * f` of a source `f`
need not converge even when `f ∈ L¹`. A logarithmic moment condition is
enough: if `f` is integrable and `log (1 + ‖y‖) f(y)` is integrable
as well, then `∫ Φ(x - y) f(y) dy` converges absolutely at every field point
`x`. We prove that integrability statement for continuous sources.

The equation `-Δ(Φ * f) = f` for compactly supported `C²` sources is proved in
`PDE.Elliptic.Classical.Poisson`.

## Main results

* `integrable_fundamentalSolution_mul_of_integrable_log_weight`: for
  continuous `f` with `f` and `log (1 + ‖·‖) f` integrable, the integrand
  `y ↦ Φ(x - y) f(y)` is integrable on `ℝ^2` for every `x`.

## Implementation notes

The proof splits the plane at the closed ball of radius `‖x‖ + 1`. Inside,
local integrability of `Φ` (from `LocalIntegrability`) combined with
continuity of `f` suffices. Outside, `‖x - y‖ > 1`, and the elementary bound
`log ‖x - y‖ ≤ (1 + log (1 + ‖x‖)) (1 + log (1 + ‖y‖))` dominates the
integrand by a constant multiple of `(1 + log (1 + ‖y‖)) |f(y)|`.
-/

@[expose] public section

noncomputable section

namespace PotentialTheory

open MeasureTheory Set

/-- The planar logarithmic potential is integrable at every field point for a
continuous source with finite mass and finite logarithmic moment.

Continuity controls the locally integrable logarithmic pole. On the tail
`‖y‖ > ‖x‖ + 1`, the estimate
`|log ‖x - y‖| ≤ (1 + log (1 + ‖x‖)) (1 + log (1 + ‖y‖))`
reduces the tail to the two stated `L¹` hypotheses. -/
theorem integrable_fundamentalSolution_mul_of_integrable_log_weight
    (f : ℝ^2 → ℝ) (hfcontinuous : Continuous f)
    (hf : Integrable f)
    (hflog : Integrable (fun y : ℝ^2 ↦ Real.log (1 + ‖y‖) * f y))
    (x : ℝ^2) :
    Integrable (fun y : ℝ^2 ↦ fundamentalSolution 2 (x - y) * f y) := by
  let Φ : ℝ^2 → ℝ := fundamentalSolution 2
  have hloc : LocallyIntegrable (fun y ↦ Φ (x - y) * f y) volume := by
    have hmap : Measure.map (Homeomorph.subLeft x) volume = volume := by
      simpa using (volume.measurePreserving_sub_left x).map_eq
    have hΦmap : LocallyIntegrable Φ (Measure.map (Homeomorph.subLeft x) volume) := by
      rw [hmap]
      exact locallyIntegrable_fundamentalSolution 2
    simpa [Φ, Function.comp_def] using
      ((locallyIntegrable_map_homeomorph _).mp hΦmap).mul_continuous hfcontinuous
  let K : Set (ℝ^2) := Metric.closedBall 0 (‖x‖ + 1)
  let c : ℝ := -(1 / (2 * Real.pi))
  let C : ℝ := ‖c‖ * (1 + Real.log (1 + ‖x‖))
  have hlogx : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  have hC : 0 ≤ C := by positivity
  rw [← integrableOn_univ, ← union_compl_self K, integrableOn_union]
  refine ⟨hloc.integrableOn_isCompact (isCompact_closedBall 0 (‖x‖ + 1)),
    Integrable.mono ((hf.add hflog).const_mul C).integrableOn hloc.aestronglyMeasurable.restrict
      ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with y hy
  have hdist : 1 < ‖x - y‖ := by
    have : ‖x‖ + 1 < ‖y‖ := by simpa [K, Metric.mem_closedBall, not_le] using hy
    linarith [norm_sub_norm_le y x, norm_sub_rev y x]
  have hlogy : 0 ≤ Real.log (1 + ‖y‖) := Real.log_nonneg (by linarith [norm_nonneg y])
  have hlog : Real.log ‖x - y‖ ≤ Real.log (1 + ‖x‖) + Real.log (1 + ‖y‖) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith)
      (by nlinarith [norm_sub_le x y, norm_nonneg x, norm_nonneg y])
  have hkernel : ‖Φ (x - y)‖ = ‖c‖ * Real.log ‖x - y‖ := by
    simp [Φ, fundamentalSolution, norm_ne_zero_iff.mp (by linarith : ‖x - y‖ ≠ 0), c, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hdist.le)]
  have hL : 0 ≤ 1 + Real.log (1 + ‖y‖) := by linarith
  dsimp only [Pi.add_apply]
  calc ‖Φ (x - y) * f y‖ = ‖c‖ * Real.log ‖x - y‖ * ‖f y‖ := by rw [norm_mul, hkernel]
    _ ≤ ‖c‖ * ((1 + Real.log (1 + ‖x‖)) * (1 + Real.log (1 + ‖y‖))) * ‖f y‖ := by
        gcongr
        nlinarith [mul_nonneg hlogx hlogy]
    _ = ‖C * (f y + Real.log (1 + ‖y‖) * f y)‖ := by
        rw [← one_add_mul, norm_mul, Real.norm_of_nonneg hC, norm_mul, Real.norm_of_nonneg hL]
        ring

end PotentialTheory
