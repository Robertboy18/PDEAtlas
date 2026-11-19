/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational

/-!
# Uniform bounds for minimizing velocities

For a `K`-Lipschitz datum, comparison with the zero velocity bounds every minimizing
velocity using an affine lower bound for `L` of slope `K + 1`. The resulting radius
depends only on `L` and `K`, not on space, positive time, or the size of the datum.

The comparison with the zero velocity is the bound (29) of Evans, §3.3.2(b), Lemma 2,
`u ≤ tL(0) + g`, for the Hopf–Lax formula (21) with a Lipschitz datum as in (20).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), equations (20)-(21), Lemma 2 and
  its proof, equation (29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An affine lower bound of slope `K + 1` bounds any velocity whose cost is no
larger than the stationary competitor. In particular it bounds every minimizer. -/
theorem norm_velocity_le_of_cost_le_zero {L g : E → ℝ} {K : NNReal} (hg : LipschitzWith K g) {B : ℝ}
    (hB : ∀ q, ((K : ℝ) + 1) * ‖q‖ - B ≤ L q) {t : ℝ} (ht : 0 < t) {x q : E}
    (hq : cost L g t x q ≤ cost L g t x 0) :
    ‖q‖ ≤ L 0 + B := by
  have hlower := cost_lower hg hB ht.le x q
  simp only [add_sub_cancel_left, one_mul] at hlower
  have hc := hlower.trans hq
  simp only [cost, smul_zero, sub_zero] at hc
  have hmul : t * ‖q‖ ≤ t * (L 0 + B) := by nlinarith
  exact (mul_le_mul_iff_right₀ ht).mp hmul

/-- Superlinearity confines all velocities beating the stationary competitor to
one ball, uniformly over all `K`-Lipschitz data and all positive times. -/
theorem exists_velocity_bound {L : E → ℝ} (hL : Superlinear L) (K : NNReal) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (g : E → ℝ), LipschitzWith K g → ∀ (t : ℝ), 0 < t → ∀ x q, cost L g t x q ≤ cost L g t x 0 →
        ‖q‖ ≤ R := by
  obtain ⟨B, hB⟩ := hL ((K : ℝ) + 1)
  refine ⟨max 0 (L 0 + B), le_max_left _ _, fun g hg t ht x q hq ↦ ?_⟩
  exact (norm_velocity_le_of_cost_le_zero hg hB ht hq).trans (le_max_right _ _)

/-- Every attained Hopf–Lax minimizer satisfies a uniform velocity bound.
The datum may be unbounded. -/
theorem exists_minimizing_velocity_bound {L : E → ℝ} (hL : Superlinear L) (K : NNReal) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (g : E → ℝ), LipschitzWith K g → ∀ (t : ℝ), 0 < t → ∀ x q, value L g t x = cost L g t x q →
        ‖q‖ ≤ R := by
  obtain ⟨R, hR, hbound⟩ := exists_velocity_bound hL K
  refine ⟨R, hR, fun g hg t ht x q hq ↦ ?_⟩
  apply hbound g hg t ht x q
  rw [← hq]
  exact value_le_cost hL hg ht.le x 0

end HamiltonJacobi.HopfLax
