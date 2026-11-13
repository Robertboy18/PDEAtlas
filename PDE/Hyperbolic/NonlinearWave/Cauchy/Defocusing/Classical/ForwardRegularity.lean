/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

/-!
# First derivatives up to the initial slice

A continuous higher Sobolev wave with its right time derivative has a jointly
C¹ representative on the closed forward half-space. For the proof only, its
lower displacement is extended affinely to negative time. This extension
matches the right velocity and imposes no backward PDE.
-/

@[expose] public noncomputable section

open Filter Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

private theorem exists_differentiable_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q v : C(ℝ, E)) (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt q (v t) (Ici 0) t) :
    ∃ Q V : C(ℝ, E), (∀ t, HasDerivAt Q (V t) t) ∧ ∀ t ∈ Ici (0 : ℝ), Q t = q t := by
  let Q : C(ℝ, E) := ⟨fun t ↦ if 0 ≤ t then q t else q 0 + t • v 0,
    q.continuous.if_le (continuous_const.add (continuous_id.smul continuous_const))
      continuous_const continuous_id (fun t ht ↦ by simp [← ht])⟩
  let V : C(ℝ, E) := ⟨fun t ↦ v (max t 0), v.continuous.comp (continuous_id.max continuous_const)⟩
  have hQ (t : ℝ) (ht : 0 ≤ t) : Q t = q t := ite_eq_left ht
  have hQneg (t : ℝ) (ht : t ≤ 0) : Q t = q 0 + t • v 0 := by
    rcases ht.eq_or_lt with rfl | ht
    · simp [Q]
    · exact ite_eq_right ht.not_ge
  have hlinear (t : ℝ) : HasDerivAt (fun s : ℝ ↦ q 0 + s • v 0) (v 0) t := by
    simpa using ((hasDerivAt_id t).smul_const (v 0)).const_add (q 0)
  refine ⟨Q, V, ?_, hQ⟩
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have he : Q =ᶠ[𝓝 t] (fun s : ℝ ↦ q 0 + s • v 0) := by
      filter_upwards [Iio_mem_nhds ht] with s hs using hQneg s hs.le
    simpa only [V, ContinuousMap.coe_mk, max_eq_right ht.le] using
      (hlinear t).congr_of_eventuallyEq he
  · have hr : HasDerivWithinAt Q (v 0) (Ici 0) 0 := (hd 0 le_rfl).congr_of_mem hQ le_rfl
    have hl : HasDerivWithinAt Q (v 0) (Iic 0) 0 :=
      (hlinear 0).hasDerivWithinAt.congr_of_mem hQneg le_rfl
    have h := hr.union hl
    rw [Ici_union_Iic] at h
    simpa only [V, ContinuousMap.coe_mk, max_self] using h.hasDerivAt (by simp)
  · have he : Q =ᶠ[𝓝 t] q := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hQ s hs.le
    simpa only [V, ContinuousMap.coe_mk, max_eq_left ht.le] using
      ((hd t ht.le).hasDerivAt (Ici_mem_nhds ht)).congr_of_eventuallyEq he

/-- Right strong time differentiability gives joint C¹ regularity up to time zero. -/
theorem contDiffOn_one_forward_higherWave {n k : ℕ} (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1) (U t).2 (Ici 0) t) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (U p.1).1 p.2)
    (Ici 0 ×ˢ univ) := by
  obtain ⟨Q, V, hdQ, hQ⟩ := exists_differentiable_extension
    ⟨_, (lowerOrderCLM (Nat.le_succ (k + 1))).continuous.comp U.continuous.fst⟩
    ⟨_, U.continuous.snd⟩ hd
  have hreg := contDiffOn_one_classicalRepresentative hk hv Q isOpen_univ
    (v := fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hv (V p.1) p.2)
    (continuous_classicalRepresentativeCLM hv V.continuous).continuousOn
    (fun t _ y ↦ hasDerivAt_classicalRepresentative_lowerOrder hv hv le_rfl
      (by simpa only [lowerOrderCLM_refl_apply] using hdQ t) y)
  refine (hreg.mono (by intro p _; exact ⟨mem_univ _, mem_univ _⟩)).congr fun p hp ↦ ?_
  rw [hQ p.1 hp.1]
  exact congrArg (fun F : BoundedContinuousFunction (ℝ^n) ℝ ↦ F p.2)
    (classicalRepresentativeCLM_lowerOrderCLM hv hq (Nat.le_succ (k + 1)) (U p.1).1).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
