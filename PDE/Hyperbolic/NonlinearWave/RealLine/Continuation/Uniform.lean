/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.BoundedRange
public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.TimeModulus

/-!
# Uniform whole-line continuation of bounded classical waves

For bounded C² displacement with bounded first derivative and bounded C¹ velocity,
a bounded classical solution of a C¹ reaction wave before a positive finite time
extends across that time on one strip covering the whole line. The bound on the
initial displacement derivative is explicit; bounded displacement alone does not
supply it.

A bounded smooth cutoff gives a global auxiliary wave. PDE uniqueness
identifies it before the endpoint. Its uniform time estimate then keeps the cutoff
inactive for one positive time beyond the endpoint, simultaneously at every point.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set
open scoped BoundedContinuousFunction

namespace WaveEquation

/-- A uniform time modulus and a bound on one slice give a single positive time
on which the field remains in a larger value interval throughout the whole line. -/
theorem exists_pos_abs_lt_on_forward_strip_of_time_bound {v : ℝ^2 → ℝ} {T R M : ℝ}
    (hbound : ∀ x : ℝ^1, |v (timeSpaceCons T x)| ≤ R)
    (hmod : ∀ t ∈ Icc T (T + 1), ∀ x : ℝ^1, ‖v (timeSpaceCons t x) - v (timeSpaceCons T x)‖ ≤
      M * (t - T)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t ∈ Icc T (T + δ), ∀ x : ℝ^1, |v (timeSpaceCons t x)| < R + 1 := by
  let N := max M 0 + 1
  have hN : 0 < N := lt_add_of_le_of_pos (le_max_right M 0) zero_lt_one
  let δ := min 1 (1 / (2 * N))
  have hδ : 0 < δ := lt_min zero_lt_one (one_div_pos.mpr (mul_pos two_pos hN))
  have hδN : δ * N ≤ 1 / 2 := by
    apply (le_div_iff₀ hN).mp
    calc
      δ ≤ 1 / (2 * N) := min_le_right _ _
      _ = (1 / 2) / N := by rw [div_div]
  refine ⟨δ, hδ, min_le_left _ _, fun t ht x ↦ ?_⟩
  have ht₁ : t ≤ T + 1 := ht.2.trans (add_le_add_right (min_le_left _ _) T)
  have hnorm := hmod t ⟨ht.1, ht₁⟩ x
  have hsmall : M * (t - T) ≤ 1 / 2 := by
    calc
      M * (t - T) ≤ N * (t - T) := mul_le_mul_of_nonneg_right
          ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one)) (sub_nonneg.mpr ht.1)
      _ ≤ N * δ := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hN.le
      _ ≤ 1 / 2 := by simpa only [mul_comm] using hδN
  have htri := norm_add_le (v (timeSpaceCons t x) - v (timeSpaceCons T x)) (v (timeSpaceCons T x))
  simp only [sub_add_cancel, Real.norm_eq_abs] at htri hnorm
  linarith [hbound x]

/-- A bounded classical solution on `0 ≤ t < T` extends to `0 ≤ t ≤ T + δ`
for one `δ > 0` valid on the entire real line. The extension is jointly C²,
has the same Cauchy data, and is bounded on the extended strip. Only
regularity strictly before `T` is required of the original solution. -/
theorem exists_classical_continuation_of_bounded_range {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ}
    (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) {u : ℝ^2 → ℝ} {T R : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | p 0 < T})
    (huwave : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → waveOperator (n := 1) u p = -f (u p))
    (hposition : ∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0))
    (hvelocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0))
    (hbound : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → |u p| ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ v : ℝ^2 → ℝ, ContDiff ℝ 2 v ∧
      (∀ p : ℝ^2, p 0 ∈ Ico 0 T → v p = u p) ∧
      (∀ x : ℝ^1, v (timeSpaceCons 0 x) = g (x 0)) ∧
      (∀ x : ℝ^1, (∂[0] v) (timeSpaceCons 0 x) = h (x 0)) ∧
      (∀ p : ℝ^2, p 0 ∈ Icc 0 (T + δ) → waveOperator (n := 1) v p = -f (v p)) ∧
      ∃ B : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc 0 (T + δ) → |v p| ≤ B := by
  obtain ⟨F, L, C, hF, hL, hEq, hC⟩ := exists_bounded_lipschitz_contDiff_reaction hf (R + 1)
  let v := nonlinearClassicalSolution hL g h
  have hv : ContDiff ℝ 2 v := contDiff_two_nonlinearClassicalSolution hL hF hg hh
  have heq : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → u p = v p := by
    apply eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz
      hL.locallyLipschitz hu hv.contDiffOn
    · intro p hp
      rw [huwave p hp, hEq (u p) ((hbound p hp).trans (le_add_of_nonneg_right zero_le_one))]
    · exact fun p hp ↦ waveOperator_nonlinearClassicalSolution hL hF hg hh hp.1
    · intro x
      exact (hposition x).trans (nonlinearClassicalSolution_initial_position hL g h x).symm
    · intro x
      exact (hvelocity x).trans (nonlinearClassicalSolution_initial_velocity hL hF hg hh x).symm
  have hvbound (x : ℝ^1) : |v (timeSpaceCons T x)| ≤ R := by
    apply abs_le_at_terminal_of_le_before hv.continuous hT ?_ x
    intro p hp
    rw [← heq p hp]
    exact hbound p hp
  obtain ⟨δ, hδ, _, hnear⟩ := exists_pos_abs_lt_on_forward_strip_of_time_bound hvbound
    (fun t ht x ↦ norm_nonlinearClassicalSolution_time_sub_le hL hF hg hh hD hC hT.le ht.1 ht.2 x)
  refine ⟨δ, hδ, v, hv, fun p hp ↦ (heq p hp).symm,
    nonlinearClassicalSolution_initial_position hL g h,
    nonlinearClassicalSolution_initial_velocity hL hF hg hh, ?_, ?_⟩
  · intro p hp
    rw [waveOperator_nonlinearClassicalSolution hL hF hg hh hp.1]
    apply congrArg Neg.neg
    apply hEq
    change |v p| ≤ R + 1
    by_cases hpt : p 0 < T
    · rw [← heq p ⟨hp.1, hpt⟩]
      exact (hbound p ⟨hp.1, hpt⟩).trans (le_add_of_nonneg_right zero_le_one)
    · simpa only [timeSpaceCons_spatialPart] using
        (hnear (p 0) ⟨le_of_not_gt hpt, hp.2⟩ (spatialPart p)).le
  · obtain ⟨B, hB⟩ := nonlinearClassicalSolution_bounded_on_strip hL g h
      ⟨T + δ, by positivity⟩
    exact ⟨B, fun p hp ↦ by simpa only [Real.norm_eq_abs] using hB p hp⟩

end WaveEquation
