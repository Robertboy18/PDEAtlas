/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ImplicitFunction.IntegralEquation

/-!
# Smooth local fixed points at a zero parameter

The same local fixed-point branch is smooth when the defining operator is smooth and its state
derivative vanishes at the base parameter.
-/

@[expose] public noncomputable section

section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Analysis

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth fixed-point equation vanishing at zero parameters has one smooth
local solution, with uniform local uniqueness in the unknown. -/
theorem exists_smooth_local_fixed_point_of_zero_parameter {F : P × E → E}
    (hF : ContDiff ℝ ∞ F) (hzero : ∀ w, F (0, w) = 0) :
    ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧
      ∃ ψ : P → E,
        ContDiffOn ℝ ∞ ψ (Metric.ball 0 δ) ∧
        (∀ p ∈ Metric.ball 0 δ, ‖ψ p‖ < r) ∧
        (∀ p ∈ Metric.ball 0 δ, ψ p = F (p, ψ p)) ∧
        (∀ p ∈ Metric.ball 0 δ, ∀ w, ‖w‖ < r → w = F (p, w) → ψ p = w) := by
  obtain ⟨d, r, hd, hr, ψ, hψ, hsmall, heq, hunique⟩ :=
    exists_local_fixed_point_of_zero_parameter (k := 0) (hF.of_le (by simp)) hzero
  have hmem : (0 : P) ∈ Metric.ball 0 d := Metric.mem_ball_self hd
  have hψ0 : ψ 0 = 0 := (heq 0 hmem).trans (hzero _)
  let G : P × E → E := fun z ↦ z.2 - F z
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hF
  have hpartial : (fderiv ℝ G (0, 0)).comp
      (ContinuousLinearMap.inr ℝ P E) = ContinuousLinearMap.id ℝ E := by
    have hdG := (hG.differentiable (by simp) (0, 0)).hasFDerivAt.comp 0
      (ContinuousLinearMap.inr ℝ P E).hasFDerivAt
    have hslice : G ∘ Prod.mk 0 = id := by
      funext w
      simp [G, hzero]
    rw [hslice] at hdG
    exact hdG.unique (hasFDerivAt_id 0)
  have hinv : (fderiv ℝ G (0, 0) ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hnear : ∀ᶠ z in 𝓝 ((0 : P), (0 : E)),
      (fderiv ℝ G z ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible :=
    (((hG.continuous_fderiv (by simp)).clm_comp continuous_const).continuousAt.tendsto)
      hinv.eventually_nhds
  have hmap : Tendsto (fun p ↦ (p, ψ p)) (𝓝 (0 : P)) (𝓝 ((0 : P), (0 : E))) := by
    simpa only [id_eq, hψ0] using
      (continuousAt_id.prodMk (hψ.contDiffAt (Metric.ball_mem_nhds 0 hd)).continuousAt).tendsto
  obtain ⟨δ, hδ, hδnear⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (Metric.ball_mem_nhds (0 : P) hd) (hmap hnear))
  refine ⟨δ, r, hδ, hr, ψ, ?_, fun p hp ↦ hsmall p (hδnear hp).1,
    fun p hp ↦ heq p (hδnear hp).1, fun p hp ↦ hunique p (hδnear hp).1⟩
  intro p hp
  have hψp := hψ.contDiffAt (Metric.isOpen_ball.mem_nhds (hδnear hp).1)
  have hGp : G (p, ψ p) = 0 := sub_eq_zero.mpr (heq p (hδnear hp).1)
  have hi := (hδnear hp).2
  have hGat : ContDiffAt ℝ ∞ G (p, ψ p) := hG.contDiffAt
  have hmap_p : Tendsto (fun q ↦ (q, ψ q)) (𝓝 p) (𝓝 (p, ψ p)) :=
    (continuousAt_id.prodMk hψp.continuousAt).tendsto
  have hsame : ψ =ᶠ[𝓝 p] hGat.implicitFunction (by simp) hi := by
    filter_upwards [hmap_p (hGat.eventually_apply_eq_iff_implicitFunction (by simp) hi),
      Metric.isOpen_ball.mem_nhds (hδnear hp).1] with q hq hqd
    exact (hq.mp ((sub_eq_zero.mpr (heq q hqd)).trans hGp.symm)).symm
  exact ((hGat.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq
    hsame).contDiffWithinAt

end PDE.Analysis

end
