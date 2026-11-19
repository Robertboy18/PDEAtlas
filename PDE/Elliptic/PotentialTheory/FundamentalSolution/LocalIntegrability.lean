/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local integrability of the fundamental solution

The one-dimensional kernel is continuous. In dimension two, the logarithmic singularity is
bounded on the unit ball by `‖x‖⁻¹`. In higher dimensions, the kernel is a constant multiple of
`‖x‖⁻⁽ⁿ⁻²⁾`. Both singular bounds are locally integrable by Mathlib's power-integrability
estimates. Evans needs the same local integrability in step 2 of his proof of §2.2.1, Theorem 1,
where his estimate (12) bounds the integral of `|Φ|` over a small ball.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), the estimate (12) in step 2 of the proof of
  Theorem 1, p. 24.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PotentialTheory

open MeasureTheory Filter Topology
open PDE.Analysis

/-- The fundamental solution is locally integrable in every dimension (in dimension zero it is the
zero function). -/
theorem locallyIntegrable_fundamentalSolution (n : ℕ) :
    LocallyIntegrable (fundamentalSolution n) volume := by
  classical
  have h_meas : AEStronglyMeasurable (fundamentalSolution n) (volume : Measure (ℝ^n)) :=
    (measurable_of_continuousOn_compl_singleton (0 : ℝ^n) fun x hx ↦
      (contDiffAt_fundamentalSolution n x (by simpa using hx)).continuousAt.continuousWithinAt
      ).aestronglyMeasurable
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : fundamentalSolution 0 = 0 := by
      funext x
      simp [fundamentalSolution, Subsingleton.elim x 0]
    rw [h0]
    exact locallyIntegrable_zero
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
  · rw [show (fundamentalSolution 1 : ℝ^1 → ℝ) = fun x ↦ -‖x‖ / 2 from
      funext fundamentalSolution_one]
    exact (continuous_norm.neg.div_const 2).locallyIntegrable
  · have h_ball : IntegrableOn (fundamentalSolution 2) (Metric.ball 0 1) := by
      refine integrableOn_ball_of_norm_le_rpow (C := 1 / (2 * Real.pi)) (α := 1)
        (by norm_num [finrank_euclideanSpace_fin]) (by norm_num [finrank_euclideanSpace_fin]) ?_
        h_meas
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hxlt : ‖x‖ < 1 := by simpa using hx
      rw [fundamentalSolution_two, Real.rpow_neg_one, norm_mul, norm_neg,
        Real.norm_of_nonneg (by positivity), Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos (norm_nonneg x) hxlt.le), ← Real.log_inv]
      gcongr
      exact Real.log_le_self (inv_nonneg.mpr (norm_nonneg x))
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 (by norm_num), h_ball⟩
    · exact (contDiffAt_fundamentalSolution 2 x hx).continuousAt.integrableAtFilter
        ⟨Set.univ, Filter.univ_mem, by simpa using h_meas⟩
        ((volume : Measure (ℝ^2)).finiteAt_nhds x)
  · have hA : 0 < ((n : ℝ) - 2) * n * unitBallVolume n := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast h3
      exact mul_pos (mul_pos (by linarith) (by linarith)) (unitBallVolume_pos n)
    refine locallyIntegrable_of_norm_le_rpow (C := 1 / (((n : ℝ) - 2) * n * unitBallVolume n))
      (α := ((n - 2 : ℕ) : ℝ)) (by rw [finrank_euclideanSpace_fin]; omega)
      (by rw [finrank_euclideanSpace_fin]; exact_mod_cast (show n - 2 < n by omega))
      (.of_forall fun x ↦ ?_) h_meas
    rw [fundamentalSolution_of_three_le h3, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast,
      Real.norm_of_nonneg (div_nonneg zero_le_one (mul_nonneg hA.le (by positivity)))]
    simp only [one_div, mul_inv, le_refl]

end PotentialTheory
