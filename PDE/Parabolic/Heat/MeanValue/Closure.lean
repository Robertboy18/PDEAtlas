/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Parabolic.Heat.MeanValue.Measurability
public import PDE.Parabolic.Heat.MeanValue.Topology
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import CAS.ExactTactic

/-!
# The boundary of a heat ball

The squared spatial radius is a concave function of backward time. Consequently
heat balls are convex, and their boundaries have zero Lebesgue measure. This
permits the mean-value integral to be taken over the closed heat-ball region.
-/

@[expose] public section

open PDE (SpaceTime time)

namespace HeatEquation

open Filter MeasureTheory Set
open PDE.Common
open scoped Topology

variable {n : ℕ}

/-- A form of the squared slice radius that is continuous at zero time lag. -/
theorem heatBallSliceRadiusSq_eq_mul_log {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    heatBallSliceRadiusSq n r τ =
      2 * (n : ℝ) * (Real.log (r ^ 2 / (4 * Real.pi)) * τ - τ * Real.log τ) := by
  by_cases hτ : τ = 0
  · simp [hτ, heatBallSliceRadiusSq]
  · unfold heatBallSliceRadiusSq
    cas using hτ

/-- The squared slice radius extends continuously to the top and bottom tips. -/
theorem continuous_heatBallSliceRadiusSq {r : ℝ} (hr : 0 < r) :
    Continuous (heatBallSliceRadiusSq n r) := by
  change Continuous (fun τ ↦ heatBallSliceRadiusSq n r τ)
  simp_rw [heatBallSliceRadiusSq_eq_mul_log hr]
  exact continuous_const.mul
    ((continuous_const.mul continuous_id).sub Real.continuous_mul_log)

/-- The squared slice radius is concave on nonnegative backward times. -/
theorem concaveOn_heatBallSliceRadiusSq {r : ℝ} (hr : 0 < r) :
    ConcaveOn ℝ (Ici 0) (heatBallSliceRadiusSq n r) := by
  have hlinear :
      ConcaveOn ℝ (Ici 0) (fun τ : ℝ ↦ Real.log (r ^ 2 / (4 * Real.pi)) * τ) := by
    refine ⟨convex_Ici _, ?_⟩
    intro a _ b _ c d _ _ _
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  have hconcave := (hlinear.sub Real.convexOn_mul_log).smul
    (show 0 ≤ 2 * (n : ℝ) by positivity)
  exact hconcave.congr fun τ _ ↦ by
    simp only [smul_eq_mul, Pi.sub_apply, heatBallSliceRadiusSq_eq_mul_log hr]

/-- Heat balls are convex in spacetime. -/
theorem convex_heatBall {x : ℝ^n} {t r : ℝ} (hr : 0 < r) :
    Convex ℝ (heatBall x t r) := by
  rw [convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  have hpτ := timeLag_pos_of_mem_heatBall hr hp
  have hqτ := timeLag_pos_of_mem_heatBall hr hq
  have htime : t - time (a • p + b • q) =
      a * (t - time p) + b * (t - time q) := by
    change t - (a * time p + b * time q) = _
    linear_combination -t * hab
  have hlag : 0 < t - time (a • p + b • q) := by
    rw [htime]
    positivity
  apply (mem_heatBall_iff_norm_sq_lt hr hlag).2
  have hspace : x - spatialPart (a • p + b • q) =
      a • (x - spatialPart p) + b • (x - spatialPart q) := by
    simp only [← spatialPartCLM_eq_spatialPart, map_add, map_smul]
    rw [smul_sub, smul_sub]
    calc
      x - (a • (spatialPartCLM n) p + b • (spatialPartCLM n) q) =
          (a • x + b • x) -
            (a • (spatialPartCLM n) p + b • (spatialPartCLM n) q) := by
        rw [← add_smul, hab, one_smul]
      _ = _ := by abel
  have hnorm := (convexOn_univ_norm (E := ℝ^n)).pow
    (fun y _ ↦ norm_nonneg y) 2
  have hnormBound := hnorm.2 (mem_univ (x - spatialPart p))
    (mem_univ (x - spatialPart q)) ha.le hb.le hab
  have hradiusBound := (concaveOn_heatBallSliceRadiusSq (n := n) hr).2
    hpτ.le hqτ.le ha.le hb.le hab
  simp only [Pi.pow_apply, smul_eq_mul] at hnormBound hradiusBound
  rw [hspace, htime]
  exact hnormBound.trans_lt
    ((add_lt_add
      (mul_lt_mul_of_pos_left ((mem_heatBall_iff_norm_sq_lt hr hpτ).1 hp) ha)
      (mul_lt_mul_of_pos_left ((mem_heatBall_iff_norm_sq_lt hr hqτ).1 hq) hb)).trans_le
      hradiusBound)

/-- The boundary of a positive-radius heat ball has zero Lebesgue measure. -/
theorem volume_frontier_heatBall {x : ℝ^n} {t r : ℝ} (hr : 0 < r) :
    volume (frontier (heatBall x t r)) = 0 :=
  (convex_heatBall hr).addHaar_frontier volume

private theorem continuousAt_shiftedKernel_of_time_lt
    {x : ℝ^n} {t : ℝ} {p : SpaceTime n} (hp : time p < t) :
    ContinuousAt (fun q ↦ shiftedFundamentalSolutionHeat x (spatialPart q) t (time q)) p := by
  have hlag : Continuous (fun q : SpaceTime n ↦ t - time q) :=
    continuous_const.sub (timeCLM n).continuous
  have hspace : Continuous (fun q : SpaceTime n ↦ spatialPart q) :=
    (spatialPartCLM n).continuous.congr (fun q ↦ spatialPartCLM_eq_spatialPart n q)
  have hpositive : 0 < t - time p := sub_pos.mpr hp
  have hformula : ContinuousAt
      (fun q : SpaceTime n ↦
        (4 * Real.pi * (t - time q)) ^ (-(n : ℝ) / 2) *
          Real.exp (-(‖x - spatialPart q‖ ^ 2 / (4 * (t - time q))))) p := by
    apply ContinuousAt.mul
    · exact (continuous_const.mul hlag).continuousAt.rpow_const
        (Or.inl (show 4 * Real.pi * (t - time p) ≠ 0 by positivity))
    · apply ContinuousAt.rexp
      apply ContinuousAt.neg
      exact ((continuous_const.sub hspace).norm.pow 2).continuousAt.div
        (continuous_const.mul hlag).continuousAt
        (show 4 * (t - time p) ≠ 0 by positivity)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hlag.continuousAt.eventually (Ioi_mem_nhds hpositive)] with q hq
  simp only [shiftedFundamentalSolutionHeat, fundamentalSolutionHeat,
    ite_eq_right (not_le.mpr hq)]

private theorem mem_closure_heatBall_of_threshold_le
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r) {p : SpaceTime n}
    (hp : (r ^ n)⁻¹ ≤ shiftedFundamentalSolutionHeat x (spatialPart p) t (time p)) :
    p ∈ closure (heatBall x t r) := by
  have hpast : time p < t := by
    by_contra h
    have hlag : t - time p ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
    simp only [shiftedFundamentalSolutionHeat, fundamentalSolutionHeat, ite_eq_left hlag] at hp
    exact (heatBall_threshold_pos hr).not_ge hp
  let q := timeSpaceCons (time p - t) (spatialPart p - x)
  have hq : time q < 0 := by
    simpa only [q, time, timeSpaceCons_zero] using sub_neg.mpr hpast
  have hk : (r ^ n)⁻¹ ≤
      shiftedFundamentalSolutionHeat 0 (spatialPart q) 0 (time q) := by
    simpa [q, shiftedFundamentalSolutionHeat, time] using hp
  have hmap : Continuous (fun a : ℝ ↦ heatBallParabolicMap x t a q) := by
    exact (timeSpaceContinuousLinearEquiv n).symm.continuous.comp
      ((continuous_const.add ((continuous_pow 2).mul continuous_const)).prodMk
        (continuous_const.add (continuous_id.smul continuous_const)))
  have hone : heatBallParabolicMap x t 1 q = p := by
    simp [heatBallParabolicMap, q, time]
  have : NeBot (𝓝[Ioo (0 : ℝ) 1] 1) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
      exact ⟨zero_le_one, le_rfl⟩)
  apply mem_closure_of_tendsto (b := 𝓝[Ioo (0 : ℝ) 1] 1)
    ((hmap.tendsto' 1 p hone).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [mem_heatBall_iff, shiftedFundamentalSolutionHeat_heatBallParabolicMap x t ha.1 q hq]
  have hfactor : 1 < a ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg ha.1.le, Real.rpow_natCast]
    exact (one_lt_inv₀ (pow_pos ha.1 n)).mpr (pow_lt_one₀ ha.1.le ha.2 hn.ne')
  calc
    (r ^ n)⁻¹ < a ^ (-(n : ℝ)) * (r ^ n)⁻¹ := by
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right hfactor (heatBall_threshold_pos hr)
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos ha.1 _).le

/-- The closed heat-ball region is the weak kernel superlevel with its pole
included. The explicit pole accounts for the zero-time totalization of the kernel. -/
theorem closure_heatBall_eq_insert_pole
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r) :
    closure (heatBall x t r) =
      insert (timeSpaceCons t x)
        {p | (r ^ n)⁻¹ ≤ shiftedFundamentalSolutionHeat x (spatialPart p) t (time p)} := by
  have hlag : Continuous (fun p : SpaceTime n ↦ t - time p) :=
    continuous_const.sub (timeCLM n).continuous
  have hspace : Continuous (fun p : SpaceTime n ↦ spatialPart p) :=
    (spatialPartCLM n).continuous.congr (fun p ↦ spatialPartCLM_eq_spatialPart n p)
  have hnorm : Continuous (fun p : SpaceTime n ↦ ‖x - spatialPart p‖ ^ 2) :=
    (continuous_const.sub hspace).norm.pow 2
  ext p
  constructor
  · intro hp
    by_cases hpast : time p < t
    · right
      have : NeBot (𝓝[heatBall x t r] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
      apply ge_of_tendsto (x := 𝓝[heatBall x t r] p)
        ((continuousAt_shiftedKernel_of_time_lt (x := x) hpast).tendsto.mono_left
          nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact le_of_lt hq
    · left
      have htime : time p ≤ t :=
        (closure_minimal (fun q hq ↦ (time_lt_of_mem_heatBall hr hq).le)
          (isClosed_le (timeCLM n).continuous continuous_const)) hp
      have htimeEq : time p = t := le_antisymm htime (le_of_not_gt hpast)
      have hnormBound :
          ‖x - spatialPart p‖ ^ 2 ≤ heatBallSliceRadiusSq n r (t - time p) :=
        (closure_minimal
          (fun q hq ↦ ((mem_heatBall_iff_norm_sq_lt hr
            (timeLag_pos_of_mem_heatBall hr hq)).1 hq).le)
          (isClosed_le hnorm ((continuous_heatBallSliceRadiusSq hr).comp hlag))) hp
      rw [htimeEq, sub_self, heatBallSliceRadiusSq] at hnormBound
      simp only [mul_zero, zero_mul] at hnormBound
      have hnormZero : ‖x - spatialPart p‖ = 0 := by nlinarith [norm_nonneg (x - spatialPart p)]
      have hspatial : spatialPart p = x := (sub_eq_zero.mp (norm_eq_zero.mp hnormZero)).symm
      calc
        p = timeSpaceCons (time p) (spatialPart p) := (timeSpaceCons_spatialPart p).symm
        _ = timeSpaceCons t x := by rw [htimeEq, hspatial]
  · rintro (rfl | hp)
    · exact pole_mem_closure_heatBall hn
    · exact mem_closure_heatBall_of_threshold_le hn hr hp

end HeatEquation
