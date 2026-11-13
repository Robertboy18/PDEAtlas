/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Uniqueness
public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Source

/-!
# Continuation of bounded classical waves on compact spatial sets

Let a one-dimensional C¹ reaction wave exist for `0 ≤ t < T`, with bounded C²
initial displacement, bounded C¹ initial velocity, and bounded solution range.
A bounded C¹ cutoff of the reaction has a global classical solution. Uniqueness
identifies it with the given field before `T`, so its continuity supplies the
terminal values without an assumed terminal trace. On each compact spatial set,
it remains inside the cutoff interval for a positive time after `T`.

The extension time may depend on the compact spatial set. This result asserts
neither a uniform extension strip on the whole line nor a maximal-lifespan
alternative. The C¹ source assumption is needed by the classical constructor;
the uniqueness argument itself needs only local Lipschitz regularity.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- Continuity passes a uniform bound on a nonempty half-open strip to its terminal time slice. -/
theorem abs_le_at_terminal_of_le_before {v : ℝ^2 → ℝ} (hv : Continuous v) {T R : ℝ} (hT : 0 < T)
    (hbound : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → |v p| ≤ R) (x : ℝ^1) :
    |v (timeSpaceCons T x)| ≤ R := by
  have hvcont : Continuous (fun q : ℝ × ℝ^1 ↦ v (timeSpaceCons q.1 q.2)) :=
    hv.comp (contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous
  have hc : Continuous (fun t : ℝ ↦ |v (timeSpaceCons t x)|) :=
    (hvcont.comp (continuous_id.prodMk continuous_const)).abs
  have hclosed : IsClosed {t : ℝ | |v (timeSpaceCons t x)| ≤ R} := isClosed_le hc continuous_const
  apply closure_minimal (t := {t : ℝ | |v (timeSpaceCons t x)| ≤ R}) ?_ hclosed
    (show T ∈ closure (Ico 0 T) by rw [closure_Ico hT.ne]; exact ⟨hT.le, le_rfl⟩)
  intro t ht
  exact hbound (timeSpaceCons t x) (by simpa using ht)

private theorem exists_pos_abs_lt_on_forward_cylinder {v : ℝ^2 → ℝ} (hv : Continuous v) {T R : ℝ}
    {K : Set (ℝ^1)} (hK : IsCompact K) (hbound : ∀ x ∈ K, |v (timeSpaceCons T x)| < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc T (T + ε), ∀ x ∈ K, |v (timeSpaceCons t x)| < R := by
  have hvcont : Continuous (fun q : ℝ × ℝ^1 ↦ v (timeSpaceCons q.1 q.2)) :=
    hv.comp (contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous
  have hevent : ∀ᶠ t in 𝓝 T, ∀ x ∈ K, |v (timeSpaceCons t x)| < R :=
    hK.eventually_forall_of_forall_eventually fun x hx ↦
      hvcont.abs.continuousAt.eventually (gt_mem_nhds (hbound x hx))
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε / 2, half_pos hε, fun t ht x hx ↦ ?_⟩
  have htε : dist t T < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  exact hnear htε x hx

/-- A uniformly bounded classical wave before `T > 0` extends past `T` on every
compact spatial set. Regularity is required only on the open half-space `t < T`. The same extension
agrees with the original solution throughout its forward interval and solves the PDE also at `T`. -/
theorem exists_classical_continuation_on_compacts_of_bounded_range {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {u : ℝ^2 → ℝ} {T R : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | p 0 < T})
    (huwave : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → waveOperator (n := 1) u p = -f (u p))
    (hposition : ∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0))
    (hvelocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0))
    (hbound : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → |u p| ≤ R) :
    ∃ v : ℝ^2 → ℝ, ContDiff ℝ 2 v ∧
      (∀ p : ℝ^2, p 0 ∈ Ico 0 T → v p = u p) ∧
      (∀ p : ℝ^2, p 0 ∈ Icc 0 T → waveOperator (n := 1) v p = -f (v p)) ∧
      ∀ K : Set (ℝ^1), IsCompact K → ∃ ε : ℝ, 0 < ε ∧
        ∀ t ∈ Icc T (T + ε), ∀ x ∈ K,
          waveOperator (n := 1) v (timeSpaceCons t x) = -f (v (timeSpaceCons t x)) := by
  obtain ⟨F, L, _, hF, hL, hEq, _⟩ := exists_bounded_lipschitz_contDiff_reaction hf (R + 1)
  let v := nonlinearClassicalSolution hL g h
  have hv : ContDiff ℝ 2 v := contDiff_two_nonlinearClassicalSolution hL hF hg hh
  have hvwave (p : ℝ^2) (hp : 0 ≤ p 0) : waveOperator (n := 1) v p = -F (v p) :=
    waveOperator_nonlinearClassicalSolution hL hF hg hh hp
  have heq : ∀ p : ℝ^2, p 0 ∈ Ico 0 T → u p = v p := by
    apply eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz
      hL.locallyLipschitz hu hv.contDiffOn
    · intro p hp
      rw [huwave p hp, hEq (u p) ((hbound p hp).trans (le_add_of_nonneg_right zero_le_one))]
    · exact fun p hp ↦ hvwave p hp.1
    · intro x
      exact (hposition x).trans (nonlinearClassicalSolution_initial_position hL g h x).symm
    · intro x
      exact (hvelocity x).trans (nonlinearClassicalSolution_initial_velocity hL hF hg hh x).symm
  have hvbound (x : ℝ^1) : |v (timeSpaceCons T x)| ≤ R := by
    apply abs_le_at_terminal_of_le_before hv.continuous hT ?_ x
    intro p hp
    rw [← heq p hp]
    exact hbound p hp
  refine ⟨v, hv, fun p hp ↦ (heq p hp).symm, ?_, ?_⟩
  · intro p hp
    rw [hvwave p hp.1]
    apply congrArg Neg.neg
    apply hEq
    apply le_trans _ (le_add_of_nonneg_right zero_le_one)
    rcases hp.2.lt_or_eq with hlt | he
    · rw [← heq p ⟨hp.1, hlt⟩]
      exact hbound p ⟨hp.1, hlt⟩
    · simpa only [← he, timeSpaceCons_spatialPart] using hvbound (spatialPart p)
  · intro K hK
    obtain ⟨ε, hε, hnear⟩ := exists_pos_abs_lt_on_forward_cylinder hv.continuous hK
      (fun x _ ↦ lt_add_of_le_of_pos (hvbound x) zero_lt_one)
    refine ⟨ε, hε, fun t ht x hx ↦ ?_⟩
    rw [hvwave (timeSpaceCons t x) (by simpa using hT.le.trans ht.1), hEq _ (hnear t ht x hx).le]

end WaveEquation
