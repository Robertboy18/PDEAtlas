/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Geometry
public import PDE.Common.Euclidean.SpaceTime

/-!
# Topology of heat balls

Heat balls are open, bounded, and monotone in the radius, and the pole lies
in their closure.  The openness proof uses the exact spatial-slice inequality on the open past
half-space, where its logarithmic radius is continuous.  Boundedness follows
from the elementary estimate `log z ≤ z`: every spatial slice lies in one
fixed Euclidean ball, while its time coordinate lies in the exact finite
backward interval.

The pole does not belong to a heat ball because the heat kernel is
zero-extended at zero time, but it is approached by points on the backward
time axis and hence belongs to the closure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, definition of the heat ball.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime time)

noncomputable section

namespace HeatEquation

open Filter
open scoped Topology
open PDE.Common

variable {n : ℕ}

/-- Every positive-radius heat ball is open. -/
theorem isOpen_heatBall {x : ℝ^n} {t r : ℝ} (hr : 0 < r) :
    IsOpen (heatBall x t r) := by
  let past : Set (SpaceTime n) := {p | time p < t}
  let gap : SpaceTime n → ℝ := fun p ↦
    heatBallSliceRadiusSq n r (t - time p) - ‖x - spatialPart p‖ ^ 2
  have htime : Continuous fun p : SpaceTime n ↦ time p := (timeCLM n).continuous
  have hspatial : Continuous fun p : SpaceTime n ↦ spatialPart p :=
    (spatialPartCLM n).continuous.congr (spatialPartCLM_eq_spatialPart n)
  have hgap : ContinuousOn gap past := by
    simp only [gap, heatBallSliceRadiusSq]
    fun_prop (disch := intro p hp; have := sub_pos.2 (show time p < t from hp); positivity)
  have hset : heatBall x t r = past ∩ gap ⁻¹' Set.Ioi 0 := by
    ext p
    refine ⟨fun hp ↦ ⟨time_lt_of_mem_heatBall hr hp, sub_pos.2
      ((mem_heatBall_iff_norm_sq_lt hr (timeLag_pos_of_mem_heatBall hr hp)).1 hp)⟩, ?_⟩
    rintro ⟨hpast, hgapPos⟩
    exact (mem_heatBall_iff_norm_sq_lt hr (sub_pos.2 hpast)).2 (sub_pos.1 hgapPos)
  rw [hset]
  exact hgap.isOpen_inter_preimage (isOpen_Iio.preimage htime) isOpen_Ioi

/-- Heat balls are monotone in their positive radius parameter. -/
theorem heatBall_mono {x : ℝ^n} {t r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    heatBall x t r ⊆ heatBall x t R := by
  intro p hp
  rw [mem_heatBall_iff] at hp ⊢
  have hpow : r ^ n ≤ R ^ n :=
    pow_le_pow_left₀ hr.le hrR n
  have hinv : (R ^ n)⁻¹ ≤ (r ^ n)⁻¹ :=
    inv_anti₀ (pow_pos hr n) hpow
  exact hinv.trans_lt hp

/-- Membership of a fixed point is stable under sufficiently small changes
of a positive heat-ball radius. -/
theorem eventually_mem_heatBall_radius {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) {p : SpaceTime n} (hp : p ∈ heatBall x t r) :
    ∀ᶠ R in 𝓝 r, p ∈ heatBall x t R := by
  have hcontinuous :
      ContinuousAt (fun R : ℝ ↦ (R ^ n)⁻¹) r :=
    (continuousAt_id.pow n).inv₀ (pow_ne_zero n hr.ne')
  rw [mem_heatBall_iff] at hp
  simpa only [mem_heatBall_iff] using
    hcontinuous.eventually (Iio_mem_nhds hp)

/-- Every positive-radius heat ball in positive spatial dimension is bounded. -/
theorem isBounded_heatBall (hn : 0 < n) {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) :
    Bornology.IsBounded (heatBall x t r) := by
  let A : ℝ := r ^ 2 / (4 * Real.pi)
  let C : ℝ := 2 * (n : ℝ) * A
  have hsubset : (timeSpaceContinuousLinearEquiv n) '' heatBall x t r ⊆
      Set.Ioo (t - A) t ×ˢ Metric.ball x (Real.sqrt C + 1) := by
    rintro q ⟨p, hp, rfl⟩
    rw [timeSpaceContinuousLinearEquiv_apply]
    refine ⟨by simpa only [A] using time_mem_Ioo_of_mem_heatBall hn hr hp, ?_⟩
    have hlag := timeLag_pos_of_mem_heatBall hr hp
    have hbound : heatBallSliceRadiusSq n r (t - time p) ≤ C := by
      rw [heatBallSliceRadiusSq]
      calc _ ≤ 2 * (n : ℝ) * (t - time p) * (r ^ 2 / (4 * Real.pi * (t - time p))) := by
            gcongr
            exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
        _ = C := by
          dsimp only [C, A]
          field_simp
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact ((Real.lt_sqrt (norm_nonneg _)).2
      (((mem_heatBall_iff_norm_sq_lt hr hlag).1 hp).trans_le hbound)).trans (lt_add_one _)
  have := (timeSpaceContinuousLinearEquiv n).symm.lipschitzWith.isBounded_image
    (((Metric.isBounded_Ioo _ _).prod Metric.isBounded_ball).subset hsubset)
  rwa [ContinuousLinearEquiv.symm_image_image] at this

/-- The closure of a positive-radius heat ball is compact in positive
spatial dimension. -/
theorem isCompact_closure_heatBall (hn : 0 < n) {x : ℝ^n} {t r : ℝ}
    (hr : 0 < r) :
    IsCompact (closure (heatBall x t r)) :=
  (isBounded_heatBall hn hr).isCompact_closure

/-- The pole is approached from the backward time axis and belongs to the
closure of every heat ball in positive spatial dimension. The ball depends on `r` only through
`r ^ n`: if `r ^ n ≤ 0` the whole backward axis lies in it, and otherwise it is the ball of
radius `|r|`. -/
theorem pole_mem_closure_heatBall (hn : 0 < n) {x : ℝ^n} {t r : ℝ} :
    timeSpaceCons t x ∈ closure (heatBall x t r) := by
  have hpath : Continuous (fun τ : ℝ ↦ (timeSpaceContinuousLinearEquiv n).symm (t - τ, x)) := by
    fun_prop
  rcases le_or_gt (r ^ n) 0 with hrn | hrn
  · have hlag : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hq : Tendsto (fun k : ℕ ↦ timeSpaceCons (t - 1 / ((k : ℝ) + 2)) x) atTop
        (𝓝 (timeSpaceCons t x)) := by
      simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply, sub_zero] using
        Tendsto.comp hpath.continuousAt hlag
    refine mem_closure_of_tendsto hq (Eventually.of_forall fun k ↦ ?_)
    have hpos : 0 < 1 / ((k : ℝ) + 2) := by positivity
    refine (inv_nonpos.mpr hrn).trans_lt ?_
    simp only [shiftedFundamentalSolutionHeat, spatialPart_timeSpaceCons, PDE.time_apply,
      timeSpaceCons_zero]
    exact fundamentalSolutionHeat_pos _ _ (by linarith)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [zero_pow hn.ne'] at hrn
  rw [show heatBall x t r = heatBall x t |r| by rw [heatBall, heatBall, pow_abs, abs_of_pos hrn]]
  have hr : 0 < |r| := abs_pos.mpr hr0
  generalize |r| = r at hr
  let A : ℝ := r ^ 2 / (4 * Real.pi)
  let q : ℕ → SpaceTime n := fun k ↦ timeSpaceCons (t - A / ((k : ℝ) + 2)) x
  have hA : 0 < A := by positivity
  have hlagTendsto : Tendsto (fun k : ℕ ↦ A / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hqTendsto : Tendsto q atTop (𝓝 (timeSpaceCons t x)) := by
    simpa only [q, Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply, sub_zero] using
      Tendsto.comp hpath.continuousAt hlagTendsto
  refine mem_closure_of_tendsto hqTendsto (Eventually.of_forall fun k ↦ ?_)
  have hlagPos : 0 < A / ((k : ℝ) + 2) := by positivity
  have hlagUpper : A / ((k : ℝ) + 2) < A := div_lt_self hA (by norm_cast; omega)
  refine (timeSpaceCons_mem_heatBall_iff_norm_sq_lt (n := n) (y := x)
    (s := t - A / ((k : ℝ) + 2)) hr (by linarith)).2 ?_
  simpa using (heatBallSliceRadiusSq_pos_iff hn hr hlagPos).2 (by simpa only [A] using hlagUpper)

end HeatEquation
