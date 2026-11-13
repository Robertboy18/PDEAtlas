/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness
public import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Recovering Hilbert norm bounds from a weaker observation

A continuous linear observation sends a closed Hilbert ball to a norm-closed
convex set. Integrating continuous observations therefore preserves the
original Hilbert norm bound, without presuming strong measurability of a lift.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded Hilbert family whose linear observations converge has a lift
of the limiting observation with the same norm bound. -/
theorem exists_lift_of_tendsto_observation (A : E →L[ℝ] F) {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → E) (f : F) {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hlim : Tendsto (fun i ↦ A (u i)) l (𝓝 f)) :
    ∃ v : E, ‖v‖ ≤ B ∧ A v = f := by
  have hbounded : Bornology.IsBounded (range u) := isBounded_iff_forall_norm_le.mpr
      ⟨B, by rintro _ ⟨i, rfl⟩; exact hbound i⟩
  obtain ⟨w, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter l u hbounded
  refine ⟨(toWeakSpace ℝ E).symm w, ?_, ?_⟩
  · exact WeakCompactness.norm_le_of_tendsto_of_norm_le hweak (.of_forall hbound)
  · have hmap := (WeakSpace.map A).continuous.tendsto w |>.comp hweak
    have hlimit := (toWeakSpaceCLM ℝ F).continuous.continuousAt.tendsto.comp (hlim.mono_left hU)
    exact congrArg (toWeakSpace ℝ F).symm (tendsto_nhds_unique hmap hlimit)

/-- Linear observations of a closed Hilbert ball form a norm-closed set. -/
theorem isClosed_observed_hilbertBall (A : E →L[ℝ] F) (B : ℝ) :
    IsClosed (A '' Metric.closedBall 0 B) := by
  refine IsSeqClosed.isClosed fun f v hf hv ↦ ?_
  have hlift (j : ℕ) : ∃ u : E, ‖u‖ ≤ B ∧ A u = f j := by
    obtain ⟨u, hu, he⟩ := hf j
    exact ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu, he⟩
  choose u hnorm hbase using hlift
  obtain ⟨w, hw, he⟩ := exists_lift_of_tendsto_observation A u v hnorm
    (by simpa only [hbase] using hv)
  exact ⟨w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw, he⟩

/-- A probability average of integrable observations stays in the same
observed Hilbert ball. -/
theorem exists_lift_integral_observation [CompleteSpace F] {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] (A : E →L[ℝ] F) {f : X → F} {B : ℝ}
    (hf : Integrable f μ) (hbound : ∀ᵐ x ∂μ, ∃ u : E, ‖u‖ ≤ B ∧ A u = f x) :
    ∃ v : E, ‖v‖ ≤ B ∧ A v = ∫ x, f x ∂μ := by
  have hm : ∀ᵐ x ∂μ, f x ∈ A '' Metric.closedBall 0 B := by
    filter_upwards [hbound] with x hx
    obtain ⟨u, hu, he⟩ := hx
    exact ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu, he⟩
  have hc : Convex ℝ (A '' Metric.closedBall 0 B) :=
    (convex_closedBall (0 : E) B).linear_image A.toLinearMap
  obtain ⟨v, hv, he⟩ := hc.integral_mem (isClosed_observed_hilbertBall A B) hm hf
  exact ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, he⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
