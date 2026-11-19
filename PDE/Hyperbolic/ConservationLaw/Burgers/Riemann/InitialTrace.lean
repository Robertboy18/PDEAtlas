/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundaryCutoff
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Rarefaction

/-!
# Initial trace of the Burgers Riemann solution

The weak shock and rarefaction theorems establish the interior conservation
law for positive time. We prove the initial-value component: the
explicit entropy solution converges to its Riemann datum in `L¹_loc(ℝ)` as
`t ↓ 0`.

The profile is bounded by `max |uL| |uR|` and converges pointwise to the datum
at every `x ≠ 0` (on the shock branch it is eventually constant near `(0, x)`;
on the rarefaction branch `x / t` leaves the fan `[uL, uR]` as `t ↓ 0`), so the
strong trace follows from dominated convergence on compact intervals.

## Main results

* `riemannSolution_tendsto_initial_of_ne_zero`: `u(t, x) → u₀(x)` as `t ↓ 0`
  for every `x ≠ 0`, on both branches.
* `riemannSolution_hasInitialTraceLocallyL1`: the convergence holds in
  `L¹_loc(ℝ)`.
* `riemannSolution_isEntropySolutionWithInitialTrace`: the explicit profile is
  an entropy solution of the Burgers Riemann problem with strong initial trace,
  for all states `uL, uR`.
* `riemannSolution_isWeakInitialValueSolution`: the same profile satisfies the
  weak identity for compact spacetime tests that may meet the initial slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.4, Theorem 4; §11.4.3, definition of an entropy
  solution, p. 650.
  <https://doi.org/10.1090/gsm/019>
* S. N. Kružkov, *First order quasilinear equations in several independent variables*,
  Math. USSR-Sb. 10 (1970), 217-243, for generalized solutions of the Cauchy problem in the class of
  bounded measurable functions.
  <https://doi.org/10.1070/SM1970v010n02ABEH002156>
-/

@[expose] public section

namespace BurgersEquation.Riemann

noncomputable section

open PDE.Common PDE.Hyperbolic.ConservationLaw

open Filter MeasureTheory Set
open scoped Topology

private theorem shockProfile_measurable (uL uR : ℝ) :
    Measurable (shockProfile uL uR) := by
  change Measurable (fun p : ℝ^2 ↦ if p 1 < shockSpeed uL uR * p 0 then uL else uR)
  exact Measurable.ite
    (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const measurable_const

private theorem riemannSolution_measurable (uL uR : ℝ) :
    Measurable (riemannSolution uL uR) := by
  by_cases hShock : uR < uL
  · rw [riemannSolution_of_lt hShock]
    exact shockProfile_measurable uL uR
  · unfold riemannSolution
    rw [ite_eq_right hShock]
    exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      ((measurable_riemannData uL uR).comp (by fun_prop)) (measurable_rarefactionProfile uL uR)

private theorem riemannSolution_norm_le (uL uR : ℝ) (p : ℝ^2) :
    ‖riemannSolution uL uR p‖ ≤ max ‖uL‖ ‖uR‖ := by
  by_cases hShock : uR < uL
  · rw [riemannSolution_of_lt hShock]
    by_cases hp : p 1 < shockSpeed uL uR * p 0
    · simp [shockProfile, hp]
    · simp [shockProfile, hp]
  · by_cases ht : p 0 = 0
    · rw [riemannSolution_timeZero_value uL uR ht]
      exact norm_riemannData_le_max uL uR (p 1)
    · rw [riemannSolution_apply_of_not_lt_of_time_ne_zero hShock ht]
      exact norm_rarefactionProfile_le p

/-- At every spatial point other than the jump point, the explicit Burgers
Riemann solution converges from positive times to the Riemann datum. -/
theorem riemannSolution_tendsto_initial_of_ne_zero (uL uR : ℝ) {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun t : ℝ ↦ riemannSolution uL uR !₂[t, x]) (𝓝[>] 0) (𝓝 (riemannData uL uR x)) := by
  have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
  have htPos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  rcases lt_or_gt_of_ne hx with hxNeg | hxPos
  · have hData : riemannData uL uR x = uL := by
      simp [riemannData, hxNeg]
    by_cases hShock : uR < uL
    · have hFront : Tendsto (fun t : ℝ ↦ shockSpeed uL uR * t)
            (𝓝[>] 0) (𝓝 0) := by
          simpa using tendsto_const_nhds.mul ht0
      have hEventually : ∀ᶠ t : ℝ in 𝓝[>] 0, x < shockSpeed uL uR * t :=
        hFront.eventually (Ioi_mem_nhds hxNeg)
      rw [hData]
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [hEventually] with t ht
      rw [riemannSolution_of_lt hShock]
      simp [shockProfile, ht]
    · have hRatio : Tendsto (fun t : ℝ ↦ x * t⁻¹) (𝓝[>] 0) atBot :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hxNeg
      have hEventually : ∀ᶠ t : ℝ in 𝓝[>] 0, x * t⁻¹ < uL := hRatio.eventually_lt_atBot uL
      rw [hData]
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [htPos, hEventually] with t ht hratio
      rw [riemannSolution_apply_of_not_lt_of_time_ne_zero hShock (by simpa using ht.ne')]
      simp [rarefactionProfile, ratio, hratio]
  · have hData : riemannData uL uR x = uR := by
      simp [riemannData, not_lt_of_ge hxPos.le]
    by_cases hShock : uR < uL
    · have hFront : Tendsto (fun t : ℝ ↦ shockSpeed uL uR * t)
            (𝓝[>] 0) (𝓝 0) := by
          simpa using tendsto_const_nhds.mul ht0
      have hEventually : ∀ᶠ t : ℝ in 𝓝[>] 0, shockSpeed uL uR * t < x :=
        hFront.eventually (Iio_mem_nhds hxPos)
      rw [hData]
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [hEventually] with t ht
      rw [riemannSolution_of_lt hShock]
      simp [shockProfile, not_lt_of_ge ht.le]
    · have hRatio : Tendsto (fun t : ℝ ↦ x * t⁻¹) (𝓝[>] 0) atTop :=
        tendsto_inv_nhdsGT_zero.const_mul_atTop hxPos
      have hEventually : ∀ᶠ t : ℝ in 𝓝[>] 0, uR < x * t⁻¹ := hRatio.eventually_gt_atTop uR
      rw [hData]
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [htPos, hEventually] with t ht hratio
      have hnotLeft : ¬x * t⁻¹ < uL := not_lt_of_ge ((le_of_not_gt hShock).trans (le_of_lt hratio))
      rw [riemannSolution_apply_of_not_lt_of_time_ne_zero hShock (by simpa using ht.ne')]
      simp [rarefactionProfile, ratio, hratio, hnotLeft]

private theorem riemannSolution_left_exterior (uL uR : ℝ) {p : ℝ^2}
    (ht : 0 < p 0) (hx : p 1 < -(max ‖uL‖ ‖uR‖ + 1) * p 0) :
    riemannSolution uL uR p = uL := by
  have hL : -(max ‖uL‖ ‖uR‖ + 1) ≤ uL := by
    have h := (neg_le_neg (le_max_left |uL| |uR|)).trans (neg_abs_le uL)
    simp only [Real.norm_eq_abs]
    linarith
  have hR : -(max ‖uL‖ ‖uR‖ + 1) ≤ uR := by
    have h := (neg_le_neg (le_max_right |uL| |uR|)).trans (neg_abs_le uR)
    simp only [Real.norm_eq_abs]
    linarith
  by_cases hShock : uR < uL
  · rw [riemannSolution_of_lt hShock]
    have hfront := hx.trans_le (mul_le_mul_of_nonneg_right
      (hR.trans (shockSpeed_mem_Ioo hShock).1.le) ht.le)
    exact ite_eq_left hfront
  · rw [riemannSolution_apply_of_not_lt_of_time_ne_zero hShock ht.ne']
    apply rarefactionProfile_eq_left
    change p 1 * (p 0)⁻¹ < uL
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ ht).mpr (hx.trans_le (mul_le_mul_of_nonneg_right hL ht.le))

private theorem riemannSolution_right_exterior (uL uR : ℝ) {p : ℝ^2}
    (ht : 0 < p 0) (hx : (max ‖uL‖ ‖uR‖ + 1) * p 0 ≤ p 1) :
    riemannSolution uL uR p = uR := by
  have hL : uL < max ‖uL‖ ‖uR‖ + 1 := by
    have h := (le_abs_self uL).trans (le_max_left |uL| |uR|)
    simp only [Real.norm_eq_abs]
    linarith
  have hR : uR < max ‖uL‖ ‖uR‖ + 1 := by
    have h := (le_abs_self uR).trans (le_max_right |uL| |uR|)
    simp only [Real.norm_eq_abs]
    linarith
  by_cases hShock : uR < uL
  · rw [riemannSolution_of_lt hShock]
    have hfront := (mul_lt_mul_of_pos_right ((shockSpeed_mem_Ioo hShock).2.trans hL) ht).trans_le hx
    exact ite_eq_right (not_lt_of_ge hfront.le)
  · rw [riemannSolution_apply_of_not_lt_of_time_ne_zero hShock ht.ne']
    apply rarefactionProfile_eq_right (le_of_not_gt hShock)
    change uR < p 1 * (p 0)⁻¹
    rw [← div_eq_mul_inv]
    exact (lt_div_iff₀ ht).mpr ((mul_lt_mul_of_pos_right hR ht).trans_le hx)

/-- The explicit entropy solution of the Burgers Riemann problem attains its
initial datum strongly in `L¹_loc(ℝ)` as `t ↓ 0`. The shared finite-propagation
criterion handles the strong trace for both wave branches. -/
theorem riemannSolution_hasInitialTraceLocallyL1 (uL uR : ℝ) :
    PDE.Hyperbolic.ConservationLaw.Scalar.HasInitialTraceLocallyL1
      (riemannSolution uL uR) (riemannData uL uR) :=
  hasInitialTraceLocallyL1_riemannData_of_finitePropagation (riemannSolution_measurable uL uR)
    (fun p _ ↦ riemannSolution_norm_le uL uR p)
    (fun _ ht hx ↦ riemannSolution_left_exterior uL uR ht hx)
    (fun _ ht hx ↦ riemannSolution_right_exterior uL uR ht hx)

/-- The explicit Burgers Riemann profile solves the full entropy initial-value
problem: it is an entropy weak solution for `t > 0` and attains the prescribed
step datum strongly in `L¹_loc` as `t ↓ 0`. -/
theorem riemannSolution_isEntropySolutionWithInitialTrace (uL uR : ℝ) :
    PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropySolutionWithInitialTrace
      flux (riemannData uL uR) (riemannSolution uL uR) := by
  exact ⟨riemannSolution_isEntropyWeakSolution_on_forwardHalfSpace uL uR,
      riemannSolution_hasInitialTraceLocallyL1 uL uR⟩

/-- For every pair of Riemann states, the Burgers entropy profile satisfies
the conservation law tested across the initial boundary, with the prescribed
step datum as its boundary term. -/
theorem riemannSolution_isWeakInitialValueSolution (uL uR : ℝ) :
    PDE.Hyperbolic.ConservationLaw.IsWeakInitialValueSolution
      flux (riemannData uL uR) (riemannSolution uL uR) := by
  have hu := (riemannSolution_isEntropySolutionWithInitialTrace uL uR).toWeak
  apply hu.isWeakInitialValueSolution_of_locallyBounded
  · unfold flux
    fun_prop
  · exact fun K _ ↦ ⟨max ‖uL‖ ‖uR‖, fun p _ _ ↦ riemannSolution_norm_le uL uR p⟩

end

end BurgersEquation.Riemann
