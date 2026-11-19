/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PDE.Parabolic.Heat.Kernel.Scaling
public import PDE.Parabolic.Heat.MeanValue.HeatBall
import CAS.ExactTactic

/-!
# Parabolic geometry of heat balls

The affine parabolic map

`(y,s) ↦ (x + r y, t + r² s)`

transports the unit heat ball to `E(x,t;r)` and scales Watson's mean-value
weight by `r⁻²`.  This is the change of variables in Evans's heat-ball
mean-value formula.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3 (rescaling to the unit heat
  ball).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime time)

noncomputable section

namespace HeatEquation

open Filter
open PDE.Common
open scoped Topology

variable {n : ℕ}

/-- Translate by `(x,t)` after parabolically dilating space by `r` and time by `r²`. -/
def heatBallParabolicMap (x : ℝ^n) (t r : ℝ) (p : SpaceTime n) :
    SpaceTime n :=
  timeSpaceCons (t + r ^ 2 * time p) (x + r • spatialPart p)

/-- The squared radius of a spatial heat-ball slice at backward time lag `τ`. -/
def heatBallSliceRadiusSq (n : ℕ) (r τ : ℝ) : ℝ :=
  2 * (n : ℝ) * τ * Real.log (r ^ 2 / (4 * Real.pi * τ))

/-- The radius of a spatial heat-ball slice at backward time lag `τ`. -/
def heatBallSliceRadius (n : ℕ) (r τ : ℝ) : ℝ :=
  Real.sqrt (heatBallSliceRadiusSq n r τ)

/-- The time coordinate of the heat-ball parabolic map. Stated through `time` for the rewrites
below; it is not a simp lemma because `time_apply` already normalises the left-hand side. -/
theorem time_heatBallParabolicMap (x : ℝ^n) (t r : ℝ) (p : SpaceTime n) :
    time (heatBallParabolicMap x t r p) = t + r ^ 2 * time p := by
  simp [heatBallParabolicMap, time]

/-- The spatial part of the parabolic rescaling dilates by `r`, then translates by `x`. -/
@[simp]
theorem spatialPart_heatBallParabolicMap
    (x : ℝ^n) (t r : ℝ) (p : SpaceTime n) :
    spatialPart (heatBallParabolicMap x t r p) =
      x + r • spatialPart p := by
  simp [heatBallParabolicMap]

/-- At a positive backward time lag, heat-ball membership is exactly the
quadratic inequality defining the corresponding spatial slice. -/
theorem timeSpaceCons_mem_heatBall_iff_norm_sq_lt
    {x y : ℝ^n} {t s r : ℝ} (hr : 0 < r)
    (hlag : 0 < t - s) :
    timeSpaceCons s y ∈ heatBall x t r ↔
      ‖x - y‖ ^ 2 < heatBallSliceRadiusSq n r (t - s) := by
  let τ : ℝ := t - s
  let A : ℝ := 4 * Real.pi * τ
  have hτ : 0 < τ := hlag
  have hA : 0 < A := by positivity
  have hrpow : (r ^ n)⁻¹ = Real.exp (Real.log r * (-(n : ℝ))) := by
    rw [← Real.rpow_natCast r n, ← Real.rpow_neg hr.le, Real.rpow_def_of_pos hr]
  have hkernel : A ^ (-(n : ℝ) / 2) * Real.exp (-(‖x - y‖ ^ 2 / (4 * τ))) =
      Real.exp (Real.log A * (-(n : ℝ) / 2) - ‖x - y‖ ^ 2 / (4 * τ)) := by
    rw [Real.rpow_def_of_pos hA, ← Real.exp_add]
    congr 1
  have hradius : heatBallSliceRadiusSq n r τ =
      (Real.log A * (-(n : ℝ) / 2) - Real.log r * (-(n : ℝ))) * (4 * τ) := by
    unfold heatBallSliceRadiusSq
    dsimp only [A]
    cas using hA.ne'
  rw [mem_heatBall_iff]
  simp only [spatialPart_timeSpaceCons]
  rw [shiftedFundamentalSolutionHeat, fundamentalSolutionHeat]
  simp only [time, timeSpaceCons_zero]
  rw [ite_eq_right (not_le.mpr hlag)]
  change (r ^ n)⁻¹ <
    A ^ (-(n : ℝ) / 2) *
      Real.exp (-(‖x - y‖ ^ 2 / (4 * τ))) ↔ _
  rw [hrpow, hkernel, Real.exp_lt_exp]
  change _ ↔ ‖x - y‖ ^ 2 < heatBallSliceRadiusSq n r τ
  rw [hradius, ← div_lt_iff₀ (by positivity : 0 < 4 * τ)]
  constructor <;> intro h <;> linarith

/-- Arbitrary-point form of the spatial-slice inequality. -/
theorem mem_heatBall_iff_norm_sq_lt
    {x : ℝ^n} {t r : ℝ} {p : SpaceTime n} (hr : 0 < r)
    (hlag : 0 < t - time p) :
    p ∈ heatBall x t r ↔
      ‖x - spatialPart p‖ ^ 2 <
        heatBallSliceRadiusSq n r (t - time p) := by
  have hrepr :
      timeSpaceCons (time p) (spatialPart p) = p := by
    exact timeSpaceCons_spatialPart p
  simpa only [hrepr] using
    (timeSpaceCons_mem_heatBall_iff_norm_sq_lt
      (n := n) (x := x) (y := spatialPart p) (t := t)
      (s := time p) (r := r) hr hlag)

/-- In positive spatial dimension, a slice has positive squared radius exactly
for backward lags below `r² / (4π)`. -/
theorem heatBallSliceRadiusSq_pos_iff
    (hn : 0 < n) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) :
    0 < heatBallSliceRadiusSq n r τ ↔
      τ < r ^ 2 / (4 * Real.pi) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hcoefficient : 0 < 2 * (n : ℝ) * τ := by
    positivity
  have hdenominator : 0 < 4 * Real.pi * τ := by
    positivity
  have hfourPi : 0 < 4 * Real.pi := by
    positivity
  have hratioNonneg :
      0 ≤ r ^ 2 / (4 * Real.pi * τ) := by
    positivity
  rw [heatBallSliceRadiusSq,
    mul_pos_iff_of_pos_left hcoefficient,
    Real.log_pos_iff hratioNonneg]
  constructor
  · intro hratio
    apply (lt_div_iff₀ hfourPi).2
    have hproduct := (lt_div_iff₀ hdenominator).1 hratio
    nlinarith
  · intro hτUpper
    apply (lt_div_iff₀ hdenominator).2
    have hproduct := (lt_div_iff₀ hfourPi).1 hτUpper
    nlinarith

/-- Derivative of the squared radius of a spatial heat-ball slice. -/
theorem hasDerivAt_heatBallSliceRadiusSq
    (n : ℕ) {r τ : ℝ} (hr : r ≠ 0) (hτ : τ ≠ 0) :
    HasDerivAt (heatBallSliceRadiusSq n r)
      (2 * (n : ℝ) *
        (Real.log (r ^ 2 / (4 * Real.pi * τ)) - 1)) τ := by
  cas

/-- Reynolds velocity of a positive spatial heat-ball slice.  The form on the
right is chosen so that the lateral boundary term in Watson's flux identity
cancels directly.  The derivative is checked by the CAS; positivity of the
squared radius supplies the domain condition of the square root and the
identity `(√u)² = u` used to reach the stated form. -/
theorem hasDerivAt_heatBallSliceRadius
    (hn : 0 < n) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (hτUpper : τ < r ^ 2 / (4 * Real.pi)) :
    HasDerivAt (heatBallSliceRadius n r)
      (heatBallSliceRadius n r τ / (2 * τ) -
        (n : ℝ) / heatBallSliceRadius n r τ) τ := by
  have hradiusSqPos :
      0 < heatBallSliceRadiusSq n r τ :=
    (heatBallSliceRadiusSq_pos_iff hn hr hτ).2 hτUpper
  unfold heatBallSliceRadiusSq at hradiusSqPos
  cas using hradiusSqPos

/-- The spatial slice radius tends to zero at the heat-ball pole. -/
theorem tendsto_heatBallSliceRadius_nhdsGT_zero (n : ℕ) :
    Tendsto (heatBallSliceRadius n 1) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun τ : ℝ ↦ Real.log τ * τ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hc : 4 * Real.pi ≠ 0 := by positivity
  have hphase :
      Tendsto (fun τ : ℝ ↦ τ * Real.log (1 / (4 * Real.pi * τ))) (𝓝[>] 0) (𝓝 0) := by
    have hbase : Tendsto (fun τ : ℝ ↦ -(τ * Real.log (4 * Real.pi) + Real.log τ * τ))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul_const
        (Real.log (4 * Real.pi))).add hlog).neg
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
    rw [Real.log_div one_ne_zero (mul_ne_zero hc hτ.ne'), Real.log_one, Real.log_mul hc hτ.ne']
    ring
  have hsq : Tendsto (heatBallSliceRadiusSq n 1) (𝓝[>] 0) (𝓝 0) := by
    convert hphase.const_mul (2 * (n : ℝ)) using 1
    · funext τ
      simp only [heatBallSliceRadiusSq, one_pow]
      ring
    · simp
  change Tendsto (fun τ ↦ Real.sqrt (heatBallSliceRadiusSq n 1 τ)) (𝓝[>] 0) (𝓝 0)
  simpa using hsq.sqrt

/-- The spatial slice radius tends to zero at the earliest heat-ball time. -/
theorem tendsto_heatBallSliceRadius_nhdsLT_timeCap (n : ℕ) :
    Tendsto (heatBallSliceRadius n 1)
      (𝓝[<] (1 / (4 * Real.pi))) (𝓝 0) := by
  let T : ℝ := 1 / (4 * Real.pi)
  have hden : 4 * Real.pi * T ≠ 0 := by
    dsimp [T]
    positivity
  have hratio : 1 / (4 * Real.pi * T) ≠ 0 :=
    div_ne_zero one_ne_zero hden
  have hcont : ContinuousAt (heatBallSliceRadiusSq n 1) T := by
    unfold heatBallSliceRadiusSq
    fun_prop (disch := first | exact hden | simpa using hratio)
  have hvalue : heatBallSliceRadiusSq n 1 T = 0 := by
    have hcancel : 4 * Real.pi * T = 1 := by
      dsimp only [T]
      field_simp
    rw [heatBallSliceRadiusSq, one_pow, hcancel]
    simp
  have hsq : Tendsto (heatBallSliceRadiusSq n 1) (𝓝[<] T) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa [hvalue] using hcont.tendsto)
  change Tendsto (fun τ ↦ Real.sqrt (heatBallSliceRadiusSq n 1 τ)) (𝓝[<] (1 / (4 * Real.pi)))
    (𝓝 0)
  simpa [T] using hsq.sqrt

/-- A positive-radius heat ball is confined to the finite backward time
interval of length `r² / (4π)`. -/
theorem time_lower_bound_of_mem_heatBall
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {p : SpaceTime n} (hp : p ∈ heatBall x t r) :
    t - r ^ 2 / (4 * Real.pi) < time p := by
  have hlag : 0 < t - time p :=
    timeLag_pos_of_mem_heatBall hr hp
  have hslice :=
    (mem_heatBall_iff_norm_sq_lt hr hlag).1 hp
  have hradiusPos :
      0 < heatBallSliceRadiusSq n r (t - time p) :=
    lt_of_le_of_lt (sq_nonneg _) hslice
  have hlagUpper :=
    (heatBallSliceRadiusSq_pos_iff hn hr hlag).1 hradiusPos
  linarith

/-- The time coordinate of every heat-ball point lies in Evans's exact
backward time interval. -/
theorem time_mem_Ioo_of_mem_heatBall
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {p : SpaceTime n} (hp : p ∈ heatBall x t r) :
    time p ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t :=
  ⟨time_lower_bound_of_mem_heatBall hn hr hp,
    time_lt_of_mem_heatBall hr hp⟩

/-- At every time in the heat ball's time window, its spatial slice is the
open Euclidean ball with Evans's logarithmic radius. -/
theorem timeSpaceCons_mem_heatBall_iff_mem_ball
    (hn : 0 < n) {x y : ℝ^n} {t s r : ℝ} (hr : 0 < r)
    (hs : s ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t) :
    timeSpaceCons s y ∈ heatBall x t r ↔
      y ∈ Metric.ball x (heatBallSliceRadius n r (t - s)) := by
  have hlag : 0 < t - s := sub_pos.mpr hs.2
  have hlagUpper : t - s < r ^ 2 / (4 * Real.pi) := by
    linarith [hs.1]
  have hradiusPos :
      0 < heatBallSliceRadiusSq n r (t - s) :=
    (heatBallSliceRadiusSq_pos_iff hn hr hlag).2 hlagUpper
  have hradiusNonneg :
      0 ≤ heatBallSliceRadius n r (t - s) := by
    exact Real.sqrt_nonneg _
  have hradiusSq :
      heatBallSliceRadius n r (t - s) ^ 2 =
        heatBallSliceRadiusSq n r (t - s) := by
    rw [heatBallSliceRadius, Real.sq_sqrt hradiusPos.le]
  have hdist : dist y x = ‖x - y‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [timeSpaceCons_mem_heatBall_iff_norm_sq_lt hr hlag,
    Metric.mem_ball, hdist]
  constructor <;> intro h <;>
    nlinarith [norm_nonneg (x - y)]

/-- Set-level description of a heat ball by its exact time window and
Euclidean-ball slices. -/
theorem heatBall_eq_setOf_time_mem_and_spatial_mem_ball
    (hn : 0 < n) (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    heatBall x t r =
      {p |
        time p ∈ Set.Ioo (t - r ^ 2 / (4 * Real.pi)) t ∧
          spatialPart p ∈
            Metric.ball x
              (heatBallSliceRadius n r (t - time p))} := by
  ext p
  have hrepr :
      timeSpaceCons (time p) (spatialPart p) = p := by
    exact timeSpaceCons_spatialPart p
  constructor
  · intro hp
    have htime := time_mem_Ioo_of_mem_heatBall hn hr hp
    refine ⟨htime, ?_⟩
    apply
      (timeSpaceCons_mem_heatBall_iff_mem_ball
        hn hr htime).1
    simpa only [hrepr] using hp
  · rintro ⟨htime, hspace⟩
    have hp :
        timeSpaceCons (time p) (spatialPart p) ∈
          heatBall x t r :=
      (timeSpaceCons_mem_heatBall_iff_mem_ball
        hn hr htime).2 hspace
    simpa only [hrepr] using hp

/-- The shifted kernel transforms by `r⁻ⁿ` under the affine parabolic map. -/
theorem shiftedFundamentalSolutionHeat_heatBallParabolicMap
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) (p : SpaceTime n)
    (hpast : time p < 0) :
    shiftedFundamentalSolutionHeat x
        (spatialPart (heatBallParabolicMap x t r p)) t
        (time (heatBallParabolicMap x t r p)) =
      r ^ (-(n : ℝ)) *
        shiftedFundamentalSolutionHeat 0 (spatialPart p) 0 (time p) := by
  have hscale :=
    fundamentalSolutionHeat_scaling
      (n := n) (-spatialPart p) (-time p) r (neg_pos.mpr hpast) hr
  simpa [shiftedFundamentalSolutionHeat, heatBallParabolicMap, time,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg] using hscale

/-- The affine parabolic map sends membership in the unit heat ball exactly
to membership in the heat ball of radius `r`. -/
theorem heatBallParabolicMap_mem_iff
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) (p : SpaceTime n) :
    heatBallParabolicMap x t r p ∈ heatBall x t r ↔
      p ∈ heatBall (0 : ℝ^n) 0 1 := by
  have hfactor : 0 < r ^ (-(n : ℝ)) :=
    Real.rpow_pos_of_pos hr _
  constructor
  · intro hp
    have hpast : time p < 0 := by
      have htime := time_lt_of_mem_heatBall hr hp
      rw [time_heatBallParabolicMap] at htime
      nlinarith [sq_pos_of_pos hr]
    rw [mem_heatBall_iff,
      shiftedFundamentalSolutionHeat_heatBallParabolicMap x t hr p hpast,
      ← Real.rpow_natCast r n, ← Real.rpow_neg hr.le] at hp
    rw [mem_heatBall_iff]
    have hkernel :
        1 <
          shiftedFundamentalSolutionHeat 0 (spatialPart p) 0 (time p) := by
      nlinarith
    simpa using hkernel
  · intro hp
    have hpast : time p < 0 := by
      simpa using
        (time_lt_of_mem_heatBall (n := n) (x := (0 : ℝ^n))
          (t := 0) (r := 1) zero_lt_one hp)
    rw [mem_heatBall_iff] at hp ⊢
    rw [shiftedFundamentalSolutionHeat_heatBallParabolicMap x t hr p hpast,
      ← Real.rpow_natCast r n, ← Real.rpow_neg hr.le]
    have hkernel :
        1 <
          shiftedFundamentalSolutionHeat 0 (spatialPart p) 0 (time p) := by
      simpa using hp
    nlinarith

/-- Watson's heat-ball weight scales by `r⁻²` under parabolic dilation. -/
theorem heatBallWeight_heatBallParabolicMap
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) (p : SpaceTime n)
    (hpast : time p < 0) :
    heatBallWeight x t (heatBallParabolicMap x t r p) =
      (r ^ 2)⁻¹ * heatBallWeight (0 : ℝ^n) 0 p := by
  have hr0 : r ≠ 0 := hr.ne'
  have htime0 : p (0 : Fin (n + 1)) ≠ 0 := by
    simpa [time] using hpast.ne
  unfold heatBallWeight
  rw [spatialPart_heatBallParabolicMap, time_heatBallParabolicMap]
  have hnorm :
      ‖x - (x + r • spatialPart p)‖ ^ 2 =
        r ^ 2 * ‖(0 : ℝ^n) - spatialPart p‖ ^ 2 := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, pow_two]
    ring
  rw [hnorm]
  field_simp [hr0, htime0]
  ring

end HeatEquation
