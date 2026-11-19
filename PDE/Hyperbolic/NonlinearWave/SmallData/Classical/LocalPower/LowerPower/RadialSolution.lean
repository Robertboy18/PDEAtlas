/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.RadialLift
public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.SegmentClassical
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import CAS.ExactTactic

/-!
# Classical power waves for radial data supported away from the origin

For every `p > 1`, a compactly supported C¹ radial velocity profile vanishing
on an interval about the origin constructs a three-dimensional C²
solution, with ordinary Cauchy traces. In particular this includes `1 < p < 2`.

The proof solves the weighted one-dimensional equation for `w = r u`.
Finite propagation keeps the cutoff region quiet on a uniform positive
time interval. The result is restricted to these radial data: no regularity
claim for arbitrary three-dimensional velocities is made here.
-/

@[expose] public noncomputable section

open Set Filter BoundedContinuousFunction PDE.Common
open scoped Topology

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The radial scaling identity `r^(1-p) |z|^p / r = |z / r|^p`. -/
private theorem radial_power_identity {r : ℝ} (hr : 0 < r) (z p : ℝ) :
    r ^ (1 - p) * |z| ^ p / r = |z / r| ^ p := by
  rw [abs_div, abs_of_pos hr, Real.div_rpow (abs_nonneg z) hr.le, Real.rpow_sub hr, Real.rpow_one]
  have hn : r ^ p ≠ 0 := (Real.rpow_pos_of_pos hr p).ne'
  cas using hr.ne' hn

/-- Radial shell velocities construct a classical three-dimensional focusing
power wave. The field is jointly C², the equation holds for `0 < t < T`,
and its velocity trace is the supplied radial profile. Only C¹ regularity
of that profile is needed; smooth compact profiles are included. -/
theorem exists_classical_abs_rpow_radial_shell {p : ℝ} (hp : 1 < p) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) {c : ℝ} (hc : 0 < c)
    (hg0 : ∀ r : ℝ, |r| ≤ 4 * c → g r = 0) :
    ∃ T : ℝ, 0 < T ∧ T ≤ c ∧ ∃ u : ℝ^4 → ℝ,
      ContDiff ℝ 2 u ∧
      (∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) = |u (timeSpaceCons t x)| ^ p) ∧
      (∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (timeSpaceCons t x)) (g ‖x‖) 0) ∧
      ∀ t ∈ Ico 0 T, ∀ x : ℝ^3, ‖x‖ < 3 * c → u (timeSpaceCons t x) = 0 := by
  let j : ℝ → ℝ := fun r ↦ r * g r
  have hj : ContDiff ℝ 1 j := contDiff_id.mul hg
  have hjc : HasCompactSupport j := hgc.mul_left
  let h : ℝ →ᵇ ℝ := ofCompactSupport j hj.continuous hjc
  let a := radialCoefficient hc hp.le
  have hf : ContDiff ℝ 1 (fun z : ℝ ↦ |z| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun z : ℝ ↦ ‖z‖ ^ p))
  obtain ⟨S, hS, w, hw, heq, hw0, hwt, hprop⟩ :=
    exists_classical_weighted_segment hf (by simp [Real.zero_rpow (by linarith : p ≠ 0)])
      h a hj (contDiff_radialCoefficient hc hp.le)
  let T := min S c
  have hT : 0 < T := lt_min hS hc
  have hTS : T ≤ S := min_le_left _ _
  have hTc : T ≤ c := min_le_right _ _
  let u := radialLift c w
  have hu : ContDiff ℝ 2 u := contDiff_radialLift hc hw
  have hquiet (t : ℝ) (ht : t ∈ Ico 0 T) (x : ℝ^3) (hx : ‖x‖ < 3 * c) :
      u (timeSpaceCons t x) = 0 := by
    have hR0 : 0 < cutoffRadius c ‖x‖ := hc.trans_le (cutoffRadius_bounds hc _).1
    have hR : cutoffRadius c ‖x‖ < 3 * c :=
      (cutoffRadius_bounds hc _).2.trans_lt (max_lt (by linarith) hx)
    have hz : w (timeSpaceCons t
        (EuclideanSpace.single (0 : Fin 1) (cutoffRadius c ‖x‖))) = 0 := by
      refine hprop _ ⟨ht.1, ht.2.trans_le hTS⟩ fun y hy ↦ ?_
      change |y - cutoffRadius c ‖x‖| ≤ t at hy
      have hybound : |y| ≤ 4 * c := by
        rw [abs_le] at hy ⊢
        constructor <;> linarith [ht.2.trans_le hTc]
      change y * g y = 0
      rw [hg0 y hybound, mul_zero]
    dsimp only [u]
    rw [radialLift_timeSpaceCons, hz, zero_div]
  refine ⟨T, hT, hTc, u, hu, ?_, ?_, ?_, hquiet⟩
  · intro t ht x
    by_cases hx : 2 * c < ‖x‖
    · have hr : 0 < ‖x‖ := by linarith
      rw [waveOperator_radialLift hc hw t hx, heq _ ⟨ht.1.le, ht.2.trans_le hTS⟩]
      change cutoffRadius c ‖x‖ ^ (1 - p) * |w _| ^ p / ‖x‖ = _
      dsimp only [u]
      rw [radialLift_timeSpaceCons, cutoffRadius_eq_self hc hx.le]
      exact radial_power_identity hr _ p
    · have hxsmall : ‖x‖ < 3 * c := by linarith [le_of_not_gt hx]
      have htzero : (fun s ↦ u (timeSpaceCons s x)) =ᶠ[𝓝 t] (fun _ ↦ 0) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact hquiet s ⟨hs.1.le, hs.2⟩ x hxsmall
      have hxzero : (fun y : ℝ^3 ↦ u (timeSpaceCons t y)) =ᶠ[𝓝 x]
          (fun _ ↦ 0) := by
        filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hxsmall)] with y hy
        exact hquiet t ⟨ht.1.le, ht.2⟩ y hy
      rw [waveOperator_timeSpaceCons hu, htzero.deriv.deriv_eq,
        EuclideanLaplacian.laplacian_congr_nhds hxzero, hquiet t ⟨ht.1.le, ht.2⟩ x hxsmall]
      simp [Real.zero_rpow (by linarith : p ≠ 0), PDE.laplacian]
  · intro x
    dsimp only [u]
    rw [radialLift_timeSpaceCons, hw0, zero_div]
  · intro x
    have hR0 : 0 < cutoffRadius c ‖x‖ := hc.trans_le (cutoffRadius_bounds hc _).1
    have hd := (hwt (cutoffRadius c ‖x‖)).div_const (cutoffRadius c ‖x‖)
    have hvelocity : h (cutoffRadius c ‖x‖) / cutoffRadius c ‖x‖ = g ‖x‖ := by
      change cutoffRadius c ‖x‖ * g (cutoffRadius c ‖x‖) / cutoffRadius c ‖x‖ = _
      rw [mul_div_cancel_left₀ _ hR0.ne']
      by_cases hx : 2 * c ≤ ‖x‖
      · rw [cutoffRadius_eq_self hc hx]
      · have hxsmall : ‖x‖ ≤ 4 * c := by linarith [lt_of_not_ge hx]
        rw [hg0 _ (by
          rw [abs_of_pos hR0]
          exact (cutoffRadius_bounds hc _).2.trans (max_le (by linarith) hxsmall)),
          hg0 _ (by simpa only [abs_norm] using hxsmall)]
    rw [hvelocity] at hd
    simpa only [u, radialLift_timeSpaceCons] using hd

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
