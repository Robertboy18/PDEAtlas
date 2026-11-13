/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespan
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.Representation

/-!
# The retarded ball formula for integral trajectories

A C¹ integral trajectory has a global C¹ representative on every proper closed
past strip. The retarded field only uses values in that strip. Applying the
continuous-source coarea formula to this representative yields the exact ball
representation, without a pointwise C² wave equation or second derivatives of
the signed power. Translation identifies any H¹ representative of the
centered trace with the source integral used in the subcritical bootstrap.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The integral trajectory satisfies the retarded ball formula at
every nonnegative time in its lifespan, with the exact factor 1/(4π). -/
theorem IsIntegralTrajectoryBefore.eq_retarded_ball {r b L : ℝ} (hr : 0 < r) (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b H L u) {T : ℝ} (hT : T ∈ Ico 0 L)
    (c : ℝ^3) :
    u (T, c) = H (T, c) - (1 / (4 * Real.pi)) * ∫ y in ball c T,
      Real.signedPower r (u (T - ‖y - c‖, y)) / ‖y - c‖ := by
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu.regular hT.2
  let F : ℝ × ℝ^3 → ℝ := fun p ↦ -Real.signedPower r (U p)
  have hF : Continuous F := ((Real.continuous_signedPower hr).comp hU.continuous).neg
  have heq := oddDuhamelSolution_congr_forward (F := F)
    (G := fun p ↦ -Real.signedPower r (u p)) (T, c) hT.1
    (fun s hs y ↦ congrArg (fun a ↦ -Real.signedPower r a) (hUeq (s, y) hs))
  have hf := oddDuhamelSolution_eq_retarded_ball
    (hF.comp (timeSpaceContinuousLinearEquiv 3).continuous) c hT.1
  dsimp only [Function.comp_def] at hf heq
  have hint : (∫ y in ball c T,
      F (timeSpaceContinuousLinearEquiv 3 (backwardConeGraph c T y)) / ‖y - c‖) =
      -(∫ y in ball c T, Real.signedPower r (u (T - ‖y - c‖, y)) / ‖y - c‖) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hyT : ‖y - c‖ < T := by simpa only [mem_ball, dist_eq_norm] using hy
    have ht : T - ‖y - c‖ ∈ Icc 0 T := ⟨(sub_pos.mpr hyT).le, sub_le_self _ (norm_nonneg _)⟩
    simp only [backwardConeGraph, timeSpaceContinuousLinearEquiv_apply,
      time, timeSpaceCons_zero, spatialPart_timeSpaceCons, F, hUeq (T - ‖y - c‖, y) ht, neg_div]
  rw [hu.equation (T, c) hT, ← heq, hf, hint, mul_neg, ← sub_eq_add_neg]

/-- Every retarded cone inside the lifespan has an H¹ displacement
trace. Only the already constructed joint C¹ field is used. -/
theorem IsIntegralTrajectoryBefore.exists_h1_centered_retardedTrace
    {r b L : ℝ} (hb : 0 < b) {H u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b H L u) {T : ℝ} (hTL : T < L) (c : ℝ^3) :
    ∃ U : H¹(ball (0 : ℝ^3) T), baseRepresentative U
      =ᵐ[domainMeasure 3 (ball 0 T)] fun x ↦ u (T - ‖x‖, c + x) := by
  obtain ⟨v, hv, heq⟩ := exists_contDiff_representative_on_initial_band hb hu.regular hTL
  let e := timeSpaceContinuousLinearEquiv 3
  let V : ℝ^4 → ℝ := fun z ↦ v ((e z).1, c + (e z).2)
  have hV : ContDiff ℝ 1 V := hv.comp (e.contDiff.fst.prodMk (contDiff_const.add e.contDiff.snd))
  obtain ⟨U, hU, _⟩ := exists_h1_retardedTrace hV 0 T T
  refine ⟨U, ?_⟩
  filter_upwards [hU, ae_restrict_mem measurableSet_ball] with x hx hxt
  have ht : T - ‖x‖ ∈ Icc 0 T :=
    ⟨(sub_pos.mpr (by simpa only [mem_ball, dist_zero_right] using hxt)).le,
      sub_le_self _ (norm_nonneg _)⟩
  rw [hx]
  simpa only [retardedTrace, Function.comp_apply, backwardConeGraph, sub_zero,
    V, e, timeSpaceContinuousLinearEquiv_apply, time, timeSpaceCons_zero,
    spatialPart_timeSpaceCons] using heq (T - ‖x‖, c + x) ht

/-- The centered representation uses any H¹ representative of the
retarded trace. The H¹ trace is only needed to state the bootstrap interface. -/
theorem IsIntegralTrajectoryBefore.eq_centered_retarded_ball {r b L : ℝ} (hr : 0 < r) (hb : 0 < b)
    {H u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b H L u) {T : ℝ} (hT : T ∈ Ico 0 L)
    (c : ℝ^3) (U : H¹(ball (0 : ℝ^3) T))
    (hbase : baseRepresentative U =ᵐ[domainMeasure 3 (ball 0 T)] fun x ↦ u (T - ‖x‖, c + x)) :
    u (T, c) = H (T, c) - (1 / (4 * Real.pi)) * ∫ x in ball (0 : ℝ^3) T,
      Real.signedPower r (baseRepresentative U x) / ‖x‖ := by
  have he := hu.eq_retarded_ball hr hb hT c
  have hpre : (fun x : ℝ^3 ↦ c + x) ⁻¹' ball c T = ball 0 T := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hm : MeasurePreserving (fun x : ℝ^3 ↦ c + x)
      (volume.restrict (ball 0 T)) (volume.restrict (ball c T)) := by
    have hm := (measurePreserving_add_left (volume : Measure (ℝ^3)) c).restrict_preimage
      (s := ball c T) measurableSet_ball
    rwa [hpre] at hm
  have hint := hm.integral_comp (Homeomorph.addLeft c).measurableEmbedding
    (fun y ↦ Real.signedPower r (u (T - ‖y - c‖, y)) / ‖y - c‖)
  simp only [add_sub_cancel_left] at hint
  have hrep : (∫ x in ball (0 : ℝ^3) T, Real.signedPower r (baseRepresentative U x) / ‖x‖) =
      ∫ x in ball (0 : ℝ^3) T, Real.signedPower r (u (T - ‖x‖, c + x)) / ‖x‖ :=
    integral_congr_ae (hbase.mono fun x hx ↦ by dsimp only; rw [hx])
  rwa [← hint, ← hrep] at he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
