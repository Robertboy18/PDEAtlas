/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Limit
public import PDE.Analysis.Convex.Subdifferential.Graph.Closed

/-!
# Resolvent states and domain membership of the limiting trajectory

The resolvent state satisfies `‖J_λ u_λ(t) - u_λ(t)‖ = λ ‖A_λ u_λ(t)‖ ≤ λ ‖v‖` for
`v ∈ ∂I(x₀)`, so it has the same uniform limit as the Yosida flow `u_λ`.
At each individual time, weak compactness of the bounded subgradients and strong/weak
graph closure place the limiting state in the subdifferential domain.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis.Convex
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal} (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
  (hlsc : LowerSemicontinuous I)

/-- Resolvent states stay within the parameter times an initial subgradient norm
of their Yosida trajectories, at every nonnegative time. -/
theorem norm_resolvent_yosidaFlow_sub_le {lambda : ℝ} (hlambda : 0 < lambda)
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {t : ℝ} (ht : 0 ≤ t) :
    ‖resolvent I hproper hconvex hlsc lambda hlambda
        (yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t) -
      yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t‖ ≤ lambda * ‖v‖ := by
  let x := yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t
  have hid := resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda x
  have heq : resolvent I hproper hconvex hlsc lambda hlambda x - x =
      -(lambda • yosidaApproximation I hproper hconvex hlsc lambda hlambda x) := by
    exact eq_neg_iff_add_eq_zero.2 (by rw [sub_add_eq_add_sub, hid, sub_self])
  change ‖resolvent I hproper hconvex hlsc lambda hlambda x - x‖ ≤ _
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  exact mul_le_mul_of_nonneg_left
    (norm_yosidaFlow_velocity_le hproper hconvex hlsc hlambda hv ht) hlambda.le

/-- The resolvent states have the same finite-interval uniform limit as the
constructed trajectories. -/
theorem tendstoUniformlyOn_resolvent_yosidaFlow
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {u : ℝ → H} {T : ℝ}
    (hu : TendstoUniformlyOn
      (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
        (by positivity) x₀) u atTop (Icc 0 T)) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun t ↦ resolvent I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
        (by positivity) (yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
          (by positivity) x₀ t)) u atTop (Icc 0 T) := by
  have hsmall : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) * ‖v‖) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖v‖
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (by positivity),
    hsmall.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))] with n hn hnsmall
  intro t ht
  refine (dist_triangle _ (yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
    (by positivity) x₀ t) _).trans_lt ?_
  have hb := norm_resolvent_yosidaFlow_sub_le hproper hconvex hlsc
    (by positivity : 0 < 1 / ((n : ℝ) + 1)) hv ht.1
  rw [norm_sub_rev, ← dist_eq_norm] at hb
  linarith [hn t ht]

/-- If the Yosida flows with parameters `1/(n+1)` converge to `u` uniformly on every
`[0, T]`, then `u(t)` lies in the subdifferential domain of `I` for every `t ≥ 0`. -/
theorem mem_subdifferentialDomain_of_yosidaFlow_limit
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {u : ℝ → H}
    (hu : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn
      (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
        (by positivity) x₀) u atTop (Icc 0 T))
    {t : ℝ} (ht : 0 ≤ t) :
    u t ∈ subdifferentialDomain I := by
  let p := fun n : ℕ ↦ yosidaApproximation I hproper hconvex hlsc
    (1 / ((n : ℝ) + 1)) (by positivity)
    (yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1)) (by positivity) x₀ t)
  have hp (n : ℕ) : ‖p n‖ ≤ ‖v‖ :=
    norm_yosidaFlow_velocity_le hproper hconvex hlsc (by positivity) hv ht
  obtain ⟨p₀, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter atTop p
      (isBounded_iff_forall_norm_le.2 ⟨‖v‖, forall_mem_range.2 hp⟩)
  refine ⟨p₀, mem_subdifferential_of_tendsto_strong_weak hproper hconvex hlsc
    (((tendstoUniformlyOn_resolvent_yosidaFlow hproper hconvex hlsc hv (hu t ht)).tendsto_at
      (right_mem_Icc.2 ht)).mono_left hU) hweak ‖v‖ hp ?_⟩
  exact Eventually.of_forall fun n ↦
    yosidaApproximation_mem_subdifferential hproper hconvex hlsc (by positivity) _

end PDE.Analysis.Evolution
