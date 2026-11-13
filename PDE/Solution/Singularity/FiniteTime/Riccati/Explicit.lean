/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.Norm.Trajectory
public import Mathlib.Analysis.Calculus.Deriv.Basic
import CAS.ExactTactic

/-!
# Explicit Riccati trajectories and finite-time blow-up

We verify the explicit solution of `y' = a y²`, its derivative away from the pole, and its
inverse-distance blow-up rate. The algebraic horizon is a zero of the denominator; it is a
future blow-up time only when the coefficient and the initial value are positive.

The scalar equation is the autonomous comparison model behind many blow-up arguments; for
`a = 1` it is the ODE `u̇ = u²` of Evans, §9.4.1, p. 547. The coefficient and initial time are
arbitrary, and the conclusion is also stated for norms.

## Main results

* `solution`, `horizon`: the formula `y(t) = y₀ / (1 - a y₀ (t - t₀))` and its pole
  `t₀ + 1 / (a y₀)`.
* `hasDerivAt_solution`, `deriv_solution_of_lt_horizon`: `y' = a y²` wherever the denominator
  is nonzero, in particular before a future horizon.
* `solution_eq_one_div_mul_horizon_sub`, `solution_pos_of_lt_horizon`: the form
  `y(t) = 1 / (a (t* - t))`, and positivity before the horizon when `a, y₀ > 0`.
* `tendsto_solution_nhdsLT_horizon_atTop`, `solution_norm_blows_up_at`: `y(t) → +∞` as
  `t ↑ t*`, stated both as a scalar limit and as `NormBlowsUpAt`.

## Implementation notes

Real division is total, so `solution` is defined even at the pole. The ODE identity holds
wherever the denominator is nonzero, on either side of the pole. The branch after the
pole is not a continuation through it. The future blow-up results use `0 < a`, `0 < y₀`,
and `t < horizon` to select the branch containing the initial time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, p. 547.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Real Filter Topology

namespace PDE.Solution.Singularity.FiniteTime.Riccati

variable (a y₀ t₀ t : ℝ)

/-- Candidate solution to the simplified Riccati equation `y' = a·y²` with initial condition
`y(t₀) = y₀`.

It is defined everywhere, including at the pole, where real division returns `0`. The theorems
below assume that the denominator is nonzero or that `t` lies before the horizon. -/
noncomputable def solution (a y₀ t₀ : ℝ) : ℝ → ℝ :=
  fun t ↦ y₀ / (1 - a * y₀ * (t - t₀))

/-- The distinguished horizon `t₀ + (a * y₀)⁻¹` of the explicit Riccati formula.

When `a * y₀ ≠ 0`, this is the unique zero of the denominator. It is a future pole only when
`a * y₀ > 0`. If `a * y₀ = 0`, then `1 / 0 = 0` makes the horizon equal to `t₀`, and there is
no pole. -/
noncomputable def horizon (a y₀ t₀ : ℝ) : ℝ :=
  t₀ + 1 / (a * y₀)

/-- A positive coefficient and positive initial value place the Riccati horizon strictly after
the initial time. -/
theorem initial_time_lt_horizon {a y₀ t₀ : ℝ} (ha : 0 < a) (hy₀ : 0 < y₀) :
    t₀ < horizon a y₀ t₀ := by
  rw [horizon]
  exact lt_add_of_pos_right t₀ (one_div_pos.mpr (mul_pos ha hy₀))

/-- The explicit Riccati formula takes the prescribed value `y₀` at the initial time `t₀`. -/
@[simp]
theorem solution_initial : solution a y₀ t₀ t₀ = y₀ := by
  simp [solution, sub_self, mul_zero, div_one]

/-- Away from the pole, the explicit candidate has derivative `a * solution²`. -/
theorem hasDerivAt_solution (h : 1 - a * y₀ * (t - t₀) ≠ 0) :
    HasDerivAt (solution a y₀ t₀) (a * solution a y₀ t₀ t ^ 2) t := by
  cas

/-- Away from the pole, the candidate satisfies the ODE `solution' = a * solution²`. -/
theorem deriv_solution (h : 1 - a * y₀ * (t - t₀) ≠ 0) :
    deriv (fun t ↦ solution a y₀ t₀ t) t = a * solution a y₀ t₀ t ^ 2 :=
  (hasDerivAt_solution a y₀ t₀ t h).deriv

/-- Factor the solution denominator through displacement from the Riccati horizon. -/
theorem solution_denominator_eq {a y₀ t₀ : ℝ} (h : a * y₀ ≠ 0) (t : ℝ) :
    1 - a * y₀ * (t - t₀) = a * y₀ * (horizon a y₀ t₀ - t) := by
  obtain ⟨ha, hy₀⟩ := mul_ne_zero_iff.mp h
  unfold horizon
  cas

/-- Before a future Riccati horizon, the explicit denominator is nonzero. -/
theorem solution_denominator_ne_zero_of_lt_horizon {a y₀ t₀ t : ℝ}
    (ha : 0 < a * y₀) (ht : t < horizon a y₀ t₀) :
    1 - a * y₀ * (t - t₀) ≠ 0 := by
  rw [solution_denominator_eq (ne_of_gt ha) t]
  exact mul_ne_zero (ne_of_gt ha) (ne_of_gt (sub_pos.mpr ht))

/-- Before a future Riccati horizon, the explicit formula satisfies `y' = a y²`. -/
theorem deriv_solution_of_lt_horizon {a y₀ t₀ t : ℝ}
    (ha : 0 < a * y₀) (ht : t < horizon a y₀ t₀) :
    deriv (fun t ↦ solution a y₀ t₀ t) t = a * (solution a y₀ t₀ t)^2 :=
  deriv_solution (a := a) (y₀ := y₀) (t₀ := t₀) (t := t)
    (solution_denominator_ne_zero_of_lt_horizon ha ht)

/-- The explicit solution is the reciprocal of `a` times the displacement from its horizon.

This algebraic identity uses Lean's total division, so it also holds at the horizon, where both
sides are zero; the CAS checks it from the nonvanishing of `a` and `y₀` alone. Its analytic use
below assumes that the horizon is a future pole. -/
theorem solution_eq_one_div_mul_horizon_sub
    {a y₀ t₀ : ℝ} (h : a * y₀ ≠ 0) (t : ℝ) :
    solution a y₀ t₀ t = 1 / (a * (horizon a y₀ t₀ - t)) := by
  obtain ⟨ha, hy₀⟩ := mul_ne_zero_iff.mp h
  unfold solution horizon
  cas

/-- Before its horizon, the explicit solution with positive coefficient and initial value is
strictly positive. -/
theorem solution_pos_of_lt_horizon
    {a y₀ t₀ t : ℝ} (ha : 0 < a) (hy₀ : 0 < y₀)
    (ht : t < horizon a y₀ t₀) :
    0 < solution a y₀ t₀ t := by
  rw [solution_eq_one_div_mul_horizon_sub (mul_pos ha hy₀).ne']
  exact one_div_pos.mpr (mul_pos ha (sub_pos.mpr ht))

/-- As `t` approaches `tStar` from below, `tStar - t` approaches zero from above. -/
theorem tendsto_const_sub_nhdsLT_nhdsGT (tStar : ℝ) :
  Filter.Tendsto (fun t ↦ tStar - t)
    (nhdsWithin tStar (Set.Iio tStar))
    (nhdsWithin 0 (Set.Ioi 0)) := by
  have h_tendsto_nhds :
      Filter.Tendsto (fun t ↦ tStar - t)
        (nhdsWithin tStar (Set.Iio tStar))
        (nhds 0) := by
    have h_cont : ContinuousAt (fun t ↦ tStar - t) tStar := by
      change ContinuousAt ((fun _ : ℝ ↦ tStar) - id) tStar
      exact continuousAt_const.sub continuousAt_id
    have h' : Filter.Tendsto (fun t ↦ tStar - t) (nhds tStar) (nhds 0) := by
      simpa using h_cont.tendsto
    exact h'.mono_left nhdsWithin_le_nhds
  have h_eventually :
      ∀ᶠ t in nhdsWithin tStar (Set.Iio tStar), (tStar - t) ∈ Set.Ioi 0 := by
    refine eventually_nhdsWithin_of_forall ?_
    intro t ht
    have ht' : t < tStar := ht
    exact sub_pos.mpr ht'
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_tendsto_nhds h_eventually

/-- For positive coefficient and initial value, the explicit solution tends to `+∞` as time
approaches its future Riccati horizon from below. -/
theorem tendsto_solution_nhdsLT_horizon_atTop
    {a y₀ t₀ : ℝ} (ha : 0 < a) (hy₀ : 0 < y₀) :
    Filter.Tendsto (fun t ↦ solution a y₀ t₀ t)
      (nhdsWithin (horizon a y₀ t₀) (Set.Iio (horizon a y₀ t₀)))
      Filter.atTop := by
  have ha_y₀ : 0 < a * y₀ := mul_pos ha hy₀
  simp_rw [solution_eq_one_div_mul_horizon_sub (ne_of_gt ha_y₀)]
  have : (fun t ↦ 1 / (a * (horizon a y₀ t₀ - t))) =
         (fun x ↦ 1 / (a * x)) ∘ (fun t ↦ horizon a y₀ t₀ - t) := by
    ext t
    simp [Function.comp]
  rw [this]
  apply Filter.Tendsto.comp
  · have : (fun x ↦ 1 / (a * x)) = (fun x ↦ (1/a) * x⁻¹) := by
      ext x
      cas
    rw [this]
    have h_pos : 0 < 1 / a := one_div_pos.mpr ha
    exact Filter.Tendsto.const_mul_atTop h_pos tendsto_inv_nhdsGT_zero
  · exact tendsto_const_sub_nhdsLT_nhdsGT (horizon a y₀ t₀)

/-- The explicit Riccati trajectory blows up in the general finite-time norm sense.

This restates `tendsto_solution_nhdsLT_horizon_atTop` in terms of `NormBlowsUpAt`, the
predicate used by the continuation and comparison theorems. -/
theorem solution_norm_blows_up_at
    {a y₀ t₀ : ℝ} (ha : 0 < a) (hy₀ : 0 < y₀) :
    NormBlowsUpAt (solution a y₀ t₀) (horizon a y₀ t₀) :=
  NormBlowsUpAt.of_tendsto_atTop <|
    tendsto_solution_nhdsLT_horizon_atTop ha hy₀

end PDE.Solution.Singularity.FiniteTime.Riccati
