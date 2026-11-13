/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.ReversibleHigherScale
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.LocalReaction.SmoothData

/-!
# Smooth wave fields from compatible Sobolev trajectories

The same energy wave has higher lifts at every spatial order. Their scale
identities give all time derivatives, and evaluation identifies one jointly
smooth field satisfying the pointwise PDE and both right Cauchy traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- Smooth compact data give a global jointly smooth wave for a globally
Lipschitz smooth scalar reaction in dimensions below four. -/
theorem exists_global_smooth_of_smoothCompact (hn : n < 4) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ q v a : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) q (Ici 0 ×ˢ univ) ∧
      (∀ y, q (0, y) = g y ∧ v (0, y) = h y) ∧
      (∃ Q : C(ℝ, BoundedContinuousFunction (ℝ^n) ℝ),
        ∀ t, 0 ≤ t → (fun y ↦ q (t, y)) = (Q t : ℝ^n → ℝ)) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ y,
        HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Ici 0) t ∧
        HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Ici 0) t ∧
        a (t, y) - Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  obtain ⟨e, he, U, hU0, hU, htime⟩ :=
    exists_smooth_higher_lifts_of_smoothCompact hn hs hf hf0 g h hg hh hgc hhc
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  have hk : (n : ℝ) < 2 * ((3 : ℝ) - 1) := by linarith
  have hq : (n : ℝ) < 2 * ((5 : ℝ) - 1) := by linarith
  have hv : (n : ℝ) < 2 * ((4 : ℝ) - 1) := by linarith
  have he' : IsEnergySolution hf hf0
      (lowerOrderCLM (by norm_num : 1 ≤ 3 + 2) (U 1 0).1,
        wkpBaseCoordinateCLM (U 1 0).2) e := by
    rw [hU 1 0 le_rfl, he.initial]
    exact he
  obtain ⟨q, v, a, _, hzero, hfield⟩ :=
    he'.exists_global_pointwise_smoothReaction hn hk hs hf hf0 hq hv (U 1 0)
  refine ⟨q, v, a, contDiffOn_closed_of_smooth_higher_lifts hn U hU htime
    (fun t ht ↦ (hfield t ht).1), ?_, ?_, fun t ht ↦ (hfield t ht).2.2.2⟩
  · intro y
    have hz := hzero y
    rw [hU0 1] at hz
    exact ⟨hz.1.trans (congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) y),
      hz.2.trans (congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hv hh hhc) y)⟩
  · refine ⟨⟨fun t ↦ classicalRepresentativeCLM hv (U 0 t).1,
      (classicalRepresentativeCLM hv).continuous.comp (U 0).continuous.fst⟩, ?_⟩
    intro t ht
    have heq := (hfield t ht).1
    rw [← hU 0 t ht] at heq
    exact eq_classicalRepresentativeCLM_of_ae_eq hv (U 0 t).1
      (q.continuous.comp (continuous_const.prodMk continuous_id)) heq

/-- Arbitrary smooth scalar reactions fixing zero admit a jointly smooth
local wave for smooth compact data in dimensions below four. -/
theorem exists_smooth_localReaction_of_smoothCompact (hn : n < 4) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) q (Ico 0 T ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Icc 0 T) 0) ∧
      ∀ t ∈ Ioo 0 T, ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + f (q (t, x)) = 0 := by
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  have hq : (n : ℝ) < 2 * ((4 : ℝ) - 1) := by linarith
  let G := mkWkpSpaceOnOfContDiff (k := 4) (p := 2) (Ω := univ) g hg hgc
  let R : ℝ := ‖classicalRepresentativeCLM hq G‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨F, K, hFs, _, hF, hFeq⟩ :=
    hs.exists_lipschitzWith_compactSupport_eqOn_closedBall (by simp) 0 hR
  have hF0 : F 0 = 0 := (hFeq (Metric.mem_closedBall_self hR.le)).trans hf0
  obtain ⟨q, v, a, hqs, hzero, ⟨Q, hrep⟩, hfield⟩ :=
    exists_global_smooth_of_smoothCompact hn hFs hF hF0 g h hg hh hgc hhc
  have hQ0 : Q 0 = classicalRepresentativeCLM hq G :=
    BoundedContinuousFunction.ext fun x ↦ (congrFun (hrep 0 le_rfl) x).symm.trans
      ((hzero x).1.trans (congrFun
        (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x).symm)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp Q.continuous.continuousAt 1 zero_lt_one
  let T := δ / 2
  have hT : 0 < T := half_pos hδ
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ^n) : ‖q (t, x)‖ ≤ R := by
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt (half_lt_self hδ)
    have hdiff : ‖Q t - Q 0‖ ≤ 1 := by
      simpa only [dist_eq_norm] using (hsmall hdist).le
    rw [congrFun (hrep t ht.1) x]
    calc
      ‖Q t x‖ ≤ ‖Q t‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ = ‖(Q t - Q 0) + Q 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖Q t - Q 0‖ + ‖Q 0‖ := norm_add_le _ _
      _ ≤ 1 + ‖Q 0‖ := add_le_add hdiff le_rfl
      _ = R := by rw [hQ0, add_comm]
  refine ⟨T, hT, q, hqs.mono (fun _ hp ↦ ⟨hp.1.1, hp.2⟩), ?_, ?_⟩
  · intro x
    refine ⟨(hzero x).1, ?_⟩
    rw [← (hzero x).2]
    exact (hfield 0 le_rfl x).1.mono Icc_subset_Ici_self
  · intro t ht x
    have hv : HasDerivAt (fun s ↦ v (s, x)) (a (t, x)) t :=
      (hfield t ht.1.le x).2.1.hasDerivAt (Ici_mem_nhds ht.1)
    have hdd : deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t = a (t, x) := by
      apply HasDerivAt.deriv
      apply hv.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      exact ((hfield s hs.le x).1.hasDerivAt (Ici_mem_nhds hs)).deriv
    rw [hdd]
    have he := (hfield t ht.1.le x).2.2
    have heq : F (q (t, x)) = f (q (t, x)) := hFeq (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t ⟨ht.1.le, ht.2.le⟩ x)
    rwa [heq] at he

end PDE.Hyperbolic.NonlinearWave.Cauchy
