/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Finite propagation for focusing classical waves

Local Lipschitz uniqueness against the zero solution gives finite propagation
(`IsSolutionBefore.eq_zero_of_norm_gt`). In particular it applies to the focusing source `|u|^p`;
a nonnegative-potential energy theorem would not suffice.

A solution before `T` is `C²` on `{t < T}` and solves the equation on `[0, T)`; at negative times
it is only a regular representative, with no control of its support. For `0 < S < T`,
`IsSolutionBefore.exists_compact_representative` replaces it by `U (t, x) = b (x) w (t, x)`, where
`w` is a `C²` function on the whole space-time that agrees with `u` near `{t ≤ S}` and `b` is a
smooth cutoff equal to one on the ball of radius `R + S`, which contains the support of
`u (t, ·)` for `0 ≤ t ≤ S` by finite propagation. Then `U` is `C²`, its slices lie in one ball at
all times, it agrees with `u` near every point of `(0, S) × ℝ^n`, and it has the Cauchy data of
`u`. Virial and energy arguments, which integrate over space at every time, apply to `U`.
-/

@[expose] public noncomputable section

open PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ} [Fact (0 < n)]

/-- Compact Cauchy support propagates at speed one for a classical
solution of a locally Lipschitz reaction fixing zero. -/
theorem IsSolutionBefore.eq_zero_of_norm_gt {f : ℝ → ℝ} (hf : LocallyLipschitz f) (hf0 : f 0 = 0)
    {g h : ℝ^n → ℝ} {R T : ℝ} {u : ℝ^(n + 1) → ℝ} (hu : IsSolutionBefore f g h T u)
    (hg : ∀ x, R < ‖x‖ → g x = 0) (hh : ∀ x, R < ‖x‖ → h x = 0) {t : ℝ} (ht : t ∈ Ico 0 T) (x : ℝ^n)
    (hx : R + t < ‖x‖) :
    u (timeSpaceCons t x) = 0 := by
  let S := (t + T) / 2
  have htS : t ≤ S := by dsimp [S]; linarith [ht.2]
  have hST : S < T := by dsimp [S]; linarith [ht.2]
  obtain ⟨U, hU, heq⟩ := exists_contDiff_eventuallyEq_before hu.regular hST
  have hbase (y : ℝ^n) (hy : y ∈ Metric.closedBall x t) : R < ‖y‖ := by
    have hy' : ‖y - x‖ ≤ t := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  have hz := eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz
    (v := fun _ ↦ 0) hf hU contDiff_const x (a := 0) (T := t) (fun s hs y _ ↦ ?_) (fun _ _ _ _ ↦ ?_)
    (fun y hy ↦ ?_) (fun y hy ↦ ?_) t ⟨ht.1, le_rfl⟩ x
    (by simp)
  · rw [(heq (timeSpaceCons t x) (by simpa using htS)).eq_of_nhds] at hz
    exact hz
  · have hsS : s ≤ S := hs.2.le.trans htS
    rw [waveOperator_congr_nhds (heq (timeSpaceCons s y) (by simpa using hsS)),
      (heq (timeSpaceCons s y) (by simpa using hsS)).eq_of_nhds]
    exact hu.equation _ (by simpa using And.intro hs.1 (hs.2.trans ht.2))
  · simp [waveOperator, hf0]
  · rw [(heq (timeSpaceCons 0 y) (by simpa using ht.1.trans htS)).eq_of_nhds, hu.position]
    apply hg
    apply hbase
    simpa only [sub_zero] using hy
  · rw [PDE.partialDeriv_congr_nhds 0
      (heq (timeSpaceCons 0 y) (by simpa using ht.1.trans htS)), hu.velocity]
    simp only [PDE.partialDeriv_const]
    apply hh
    apply hbase
    simpa only [sub_zero] using hy

/-- **A representative with compact slices.** Let `u` be a classical solution before `T` of
`u_tt - Δu + f(u) = 0`, with `f` locally Lipschitz and `f 0 = 0`, from data that vanish outside
the ball of radius `R > 0`. For `0 < S < T` there is a `C²` function `U` on the whole space-time
that vanishes for `|x| > R + S + 1` at all times, agrees with `u` near every point of
`(0, S) × ℝ^n`, and has the Cauchy data `g`, `h` at time zero. -/
theorem IsSolutionBefore.exists_compact_representative {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hf0 : f 0 = 0) {g h : ℝ^n → ℝ} {R S T : ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : IsSolutionBefore f g h T u) (hg : ∀ x, R < ‖x‖ → g x = 0)
    (hh : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hS : 0 < S) (hST : S < T) :
    ∃ U : ℝ^(n + 1) → ℝ, ContDiff ℝ 2 U ∧
      (∀ t x, R + S + 1 < ‖x‖ → U (timeSpaceCons t x) = 0) ∧
      (∀ t ∈ Ioo 0 S, ∀ x, U =ᶠ[𝓝 (timeSpaceCons t x)] u) ∧
      (∀ x, U (timeSpaceCons 0 x) = g x) ∧ ∀ x, (∂[0] U) (timeSpaceCons 0 x) = h x := by
  obtain ⟨w, hw, hwu⟩ := exists_contDiff_eventuallyEq_before hu.regular hST
  let b : ContDiffBump (0 : ℝ^n) := ⟨R + S, R + S + 1, add_pos hR hS, by linarith⟩
  let U : ℝ^(n + 1) → ℝ := fun p ↦ b (spatialPartCLM n p) * w p
  have hU : ContDiff ℝ 2 U := (b.contDiff.comp (spatialPartCLM n).contDiff).mul hw
  have hb (x : ℝ^n) (hx : ‖x‖ ≤ R + S) : b x = 1 :=
    b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
  have hcut {a : ℝ^n → ℝ} (ha : ∀ x, R < ‖x‖ → a x = 0) (x : ℝ^n) : b x * a x = a x := by
    by_cases hx : ‖x‖ ≤ R + S
    · rw [hb x hx, one_mul]
    · rw [ha x (by linarith [not_le.mp hx]), mul_zero]
  refine ⟨U, hU, fun t x hx ↦ ?_, fun t ht x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hbx : b x = 0 := b.zero_of_le_dist (by
      rw [dist_zero_right]
      exact hx.le)
    simp only [U, spatialPartCLM_timeSpaceCons, hbx, zero_mul]
  · have hopen : {p : ℝ^(n + 1) | 0 < p 0 ∧ p 0 < S} ∈ 𝓝 (timeSpaceCons t x) :=
      ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
        (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)).mem_nhds
          (by simpa using ht)
    filter_upwards [hwu (timeSpaceCons t x) (by simpa using ht.2.le), hopen] with p hp hpS
    change b (spatialPartCLM n p) * w p = u p
    rw [hp]
    by_cases hx : ‖spatialPartCLM n p‖ ≤ R + S
    · rw [hb _ hx, one_mul]
    · have hzero := hu.eq_zero_of_norm_gt hf hf0 hg hh (t := p 0) ⟨hpS.1.le, hpS.2.trans hST⟩
        (spatialPartCLM n p) (by linarith [not_le.mp hx, hpS.2])
      rw [timeSpaceCons_spatialPartCLM] at hzero
      rw [hzero, mul_zero]
  · change b (spatialPartCLM n (timeSpaceCons 0 x)) * w (timeSpaceCons 0 x) = g x
    rw [spatialPartCLM_timeSpaceCons,
      (hwu (timeSpaceCons 0 x) (by simpa using hS.le)).eq_of_nhds, hu.position, hcut hg]
  · have hd := (PDE.hasDerivAt_timeSpaceCons w 0 x (hw.differentiable (by norm_num) _)).const_mul
      (b x)
    have hd' := PDE.hasDerivAt_timeSpaceCons U 0 x (hU.differentiable (by norm_num) _)
    have heq : (fun s ↦ U (timeSpaceCons s x)) = fun s ↦ b x * w (timeSpaceCons s x) := by
      funext s
      simp only [U, spatialPartCLM_timeSpaceCons]
    rw [heq] at hd'
    rw [hd'.unique hd,
      PDE.partialDeriv_congr_nhds 0 (hwu (timeSpaceCons 0 x) (by simpa using hS.le)), hu.velocity,
      hcut hh]

end WaveEquation.SmallData.Classical
