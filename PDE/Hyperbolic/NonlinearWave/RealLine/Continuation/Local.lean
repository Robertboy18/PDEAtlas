/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Maximal

/-!
# Local existence in the bounded classical wave class

The uniform time estimate keeps a bounded C¹ cutoff inactive for a positive
initial time. This supplies local classical waves for C¹ reactions and bounded
C²/C¹ data with bounded first displacement derivative.
-/

@[expose] public noncomputable section

open PDE.Common Set
open scoped BoundedContinuousFunction

namespace WaveEquation

/-- C¹ reactions admit a local whole-line classical wave in the bounded-strip
class. The only derivative bound on the data is the first derivative of the
initial displacement. -/
theorem exists_bounded_classicalWaveBefore {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {D : ℝ} (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) :
    ∃ T : ℝ, ∃ u : ℝ^2 → ℝ, IsBoundedClassicalWaveBefore f g h T u := by
  obtain ⟨F, L, C, hF, hL, hEq, hC⟩ := exists_bounded_lipschitz_contDiff_reaction hf (‖g‖ + 1)
  let v := nonlinearClassicalSolution hL g h
  have hv : ContDiff ℝ 2 v := contDiff_two_nonlinearClassicalSolution hL hF hg hh
  have hbound (x : ℝ^1) : |v (timeSpaceCons 0 x)| ≤ ‖g‖ := by
    dsimp [v]
    rw [nonlinearClassicalSolution_initial_position]
    exact g.norm_coe_le_norm (x 0)
  obtain ⟨δ, hδ, _, hnear⟩ := exists_pos_abs_lt_on_forward_strip_of_time_bound hbound
    (fun t ht x ↦ norm_nonlinearClassicalSolution_time_sub_le hL hF hg hh hD hC le_rfl ht.1 ht.2 x)
  obtain ⟨B, hB⟩ := nonlinearClassicalSolution_bounded_on_strip hL g h ⟨δ, hδ.le⟩
  refine ⟨δ, v, hδ, hv.contDiffOn, ?_, nonlinearClassicalSolution_initial_position hL g h,
    nonlinearClassicalSolution_initial_velocity hL hF hg hh, ?_⟩
  · intro p hp
    rw [waveOperator_nonlinearClassicalSolution hL hF hg hh hp.1]
    apply congrArg Neg.neg
    apply hEq
    simpa only [timeSpaceCons_spatialPart] using
      (hnear (p 0) ⟨hp.1, by simpa using hp.2.le⟩ (spatialPart p)).le
  · exact fun S hS ↦ ⟨B, fun p hp ↦ hB p ⟨hp.1, hp.2.trans hS.2.le⟩⟩

end WaveEquation
