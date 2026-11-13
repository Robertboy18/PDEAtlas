/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.SmoothCutoff
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothData

/-!
# Local classical waves for smooth reactions

Smooth compact initial data admit a local classical wave even when the reaction
is not globally Lipschitz. We cut off the reaction outside a ball containing the
initial displacement, construct the cutoff evolution, and use continuity in the
uniform spatial norm to keep it inside that ball for a positive time. The cutoff
then disappears from the differential equation.

The initial velocity is a right time derivative. Joint C² regularity is asserted
at positive times; no backward solution is part of this construction.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- A smooth reaction fixing zero and arbitrary smooth compact Cauchy data give
a local classical wave in every positive dimension. The reaction need
not be globally Lipschitz, and no bound on the unknown solution is an input. -/
theorem exists_classical_localReaction_of_smoothCompact (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 T ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Icc 0 T) 0) ∧
      ∀ t ∈ Ioo 0 T, ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + f (q (t, x)) = 0 := by
  let k := n + 2
  have hk : (n : ℝ) < 2 * ((k : ℝ) - 1) := by
    dsimp [k]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  let G := mkWkpSpaceOnOfContDiff (k := k + 2) (p := 2) (Ω := univ) g hg hgc
  let H := mkWkpSpaceOnOfContDiff (k := k + 1) (p := 2) (Ω := univ) h hh hhc
  let R : ℝ := ‖classicalRepresentativeCLM hq G‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨F, K, hFs, _, hF, hFeq⟩ :=
    hs.exists_lipschitzWith_compactSupport_eqOn_closedBall (by simp) 0 hR
  have hF0 : F 0 = 0 := (hFeq (Metric.mem_closedBall_self hR.le)).trans hf0
  obtain ⟨u, hu⟩ := exists_energySolution hF hF0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) G, wkpBaseCoordinateCLM H)
  obtain ⟨b, hb, U, hU0, hU⟩ := hu.exists_local_higherOrder_smoothReaction hv hFs hF hF0 (G, H)
  obtain ⟨q, v, a, hq₂, hzero, hfield⟩ :=
    hu.exists_pointwise_higherLift_smoothReaction hk hFs hF hF0 hq hv (G, H) U hU0 hU
  let Q : C(ℝ, BoundedContinuousFunction (ℝ^n) ℝ) := ⟨fun t ↦ classicalRepresentativeCLM hq (U t).1,
      (classicalRepresentativeCLM hq).continuous.comp U.continuous.fst⟩
  have hQ0 : Q 0 = classicalRepresentativeCLM hq G := by
    change classicalRepresentativeCLM hq (U 0).1 = _
    rw [hU0]
  have hrep (t : ℝ) (ht : t ∈ Icc 0 b) :
      (fun x ↦ q (t, x)) = (Q t : ℝ^n → ℝ) := by
    have he := (hfield t ht).1
    rw [← hU t ht] at he
    exact eq_classicalRepresentativeCLM_of_ae_eq hq (U t).1
      (q.continuous.comp (continuous_const.prodMk continuous_id)) he
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp Q.continuous.continuousAt 1 zero_lt_one
  let T := min b (δ / 2)
  have hT : 0 < T := lt_min hb (half_pos hδ)
  have hTb : T ≤ b := min_le_left _ _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ^n) : ‖q (t, x)‖ ≤ R := by
    have hdist : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt ((min_le_right b (δ / 2)).trans_lt (half_lt_self hδ))
    have hdiff : ‖Q t - Q 0‖ ≤ 1 := by
      simpa only [dist_eq_norm] using (hsmall hdist).le
    rw [congrFun (hrep t ⟨ht.1, ht.2.trans hTb⟩) x, show R = 1 + ‖Q 0‖ by rw [hQ0, add_comm]]
    linarith [(Q t).norm_coe_le_norm x, norm_le_norm_add_norm_sub' (Q t) (Q 0)]
  refine ⟨T, hT, q, hq₂.mono fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.trans_le hTb⟩, hp.2⟩, ?_, ?_⟩
  · intro x
    have hg' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x
    have hh' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hv hh hhc) x
    refine ⟨(hzero x).1.trans hg', ?_⟩
    rw [← (hzero x).2.trans hh']
    exact ((hfield 0 ⟨le_rfl, hb.le⟩).2.2.2 x).1.mono (Icc_subset_Icc le_rfl hTb)
  · intro t ht x
    have htb : t ∈ Ioo 0 b := ⟨ht.1, ht.2.trans_le hTb⟩
    have hdd := deriv_deriv_eq_of_wave_derivatives
      (fun s hst ↦ ⟨((hfield s hst).2.2.2 x).1, ((hfield s hst).2.2.2 x).2.1⟩) htb
    rw [hdd]
    have he := ((hfield t ⟨htb.1.le, htb.2.le⟩).2.2.2 x).2.2
    have heq : F (q (t, x)) = f (q (t, x)) := hFeq (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t ⟨ht.1.le, ht.2.le⟩ x)
    rwa [heq] at he

end PDE.Hyperbolic.NonlinearWave.Cauchy
