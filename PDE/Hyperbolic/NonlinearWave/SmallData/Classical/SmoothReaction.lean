/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.JetEvolution
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.TraceCalculus
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SmoothData

/-!
# Local classical waves through the initial slice

Smooth compact velocity data with zero displacement give a classical
solution for a smooth globally Lipschitz reaction fixing zero. A short interval
has uniformly small displacement, allowing a reaction cutoff to be removed.
-/

@[expose] public noncomputable section

open PDE PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev Laplacian Topology

namespace WaveEquation.SmallData.Classical

private theorem exists_pos_norm_le_one_on_Icc {E : Type*} [NormedAddCommGroup E] {Q : ℝ → E}
    (hQ : Continuous Q) (hQ0 : Q 0 = 0) {b : ℝ} (hb : 0 < b) :
    ∃ T : ℝ, 0 < T ∧ T ≤ b ∧ ∀ t ∈ Icc 0 T, ‖Q t‖ ≤ 1 := by
  obtain ⟨ε, hε, hsmall⟩ := Metric.continuousAt_iff.mp hQ.continuousAt 1 zero_lt_one
  refine ⟨min b (ε / 2), lt_min hb (half_pos hε), min_le_left _ _, fun t ht ↦ ?_⟩
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt ((min_le_right b (ε / 2)).trans_lt (half_lt_self hε))
  have he := hsmall htε
  simpa only [hQ0, dist_zero_right] using he.le

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- Zero displacement and arbitrary smooth compact velocity yield a
jointly C² local solution, with the PDE and ordinary Cauchy traces at zero.
The constructed displacement stays in `[-1,1]` on a closed positive interval. -/
theorem exists_solutionBefore_smoothReaction_zero
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (h : ℝ^n → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^(n + 1) → ℝ, IsSolutionBefore f (fun _ ↦ 0) h T u ∧ ∀ t ∈ Icc 0 T, ∀ x,
      |u (timeSpaceCons t x)| ≤ 1 := by
  let k := n + 2
  have hk : (n : ℝ) < 2 * ((k : ℝ) - 1) := by
    dsimp [k]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith
  let H := mkWkpSpaceOnOfContDiff (k := k + 2) (p := 2) (Ω := univ) h hh hhc
  obtain ⟨b, hb, V, B, hV0, hQ, hV, hB⟩ := exists_zeroJet_smoothReaction hk hv hq hs hf hf0 H
  let Q : C(ℝ, BoundedContinuousFunction (ℝ^n) ℝ) := ⟨fun t ↦ classicalRepresentativeCLM hq (V t).1,
      (classicalRepresentativeCLM hq).continuous.comp V.continuous.fst⟩
  let u : ℝ^(n + 1) → ℝ := fun p ↦ Q (p 0) (spatialPart p)
  have hut (t : ℝ) (x : ℝ^n) : u (timeSpaceCons t x) = Q t x := by
    simp only [u, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  have hreg : ContDiffOn ℝ 2 u {p | p 0 < b} := by
    apply (contDiffOn_two_higherWave hk hv hq V B isOpen_Iio hQ hV).comp
      (((EuclideanSpace.proj 0).contDiff.prodMk (spatialPartCLM n).contDiff).contDiffOn)
    exact fun p hp ↦ ⟨hp, mem_univ _⟩
  have hfirst (t : ℝ) (ht : t < b) (x : ℝ^n) : HasDerivAt (fun s ↦ u (timeSpaceCons s x))
        (classicalRepresentativeCLM hv (V t).2 x) t := by
    simp only [hut]
    exact hasDerivAt_classicalRepresentative_lowerOrder hv hq (Nat.le_succ (k + 1)) (hQ t ht) x
  have hsecond (t : ℝ) (ht : t < b) (x : ℝ^n) :=
    hasDerivAt_classicalRepresentative_lowerOrder hk hv (Nat.le_succ k) (hV t ht) x
  have hsol : IsSolutionBefore f (fun _ ↦ 0) h b u := by
    refine ⟨hb, hreg, ?_, ?_, ?_⟩
    · intro p hp
      have hw := waveOperator_eq_of_trace_derivatives hreg
        (fun t x ↦ classicalRepresentativeCLM hv (V t).2 x)
        (fun t x ↦ classicalRepresentativeCLM hk (B t) x) hfirst hsecond hp.2 (spatialPart p)
      rw [timeSpaceCons_spatialPart] at hw
      rw [hw, hB (p 0) hp, classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq]
      simp only [hut]
      have hslice : ContDiffAt ℝ 2 (Q (p 0) : ℝ^n → ℝ) (spatialPart p) := by
        have hr := (contDiffAt_of_before hreg hp.2 (spatialPart p)).comp (spatialPart p)
          (contDiff_timeSpaceCons_spatial n (p 0) (m := 2)).contDiffAt
        simpa only [Function.comp_def, hut] using hr
      change Δ (Q (p 0) : ℝ^n → ℝ) (spatialPart p) - f (u p) -
        PDE.laplacian (Q (p 0)) (spatialPart p) = -f (u p)
      rw [← hslice.coordinate_laplacian_eq_laplacian]
      abel
    · intro x
      simp [hut, Q, hV0]
    · intro x
      rw [partialDeriv_eq_of_trace_derivative hreg hb x (hfirst 0 hb x), hV0]
      change classicalRepresentativeCLM hv (lowerOrderCLM (Nat.le_succ (k + 1)) H) x = h x
      rw [classicalRepresentativeCLM_lowerOrderCLM hv hq]
      exact congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hh hhc) x
  have hQ0 : Q 0 = 0 := by simp [Q, hV0]
  obtain ⟨T, hT, hTb, hbound⟩ := exists_pos_norm_le_one_on_Icc Q.continuous hQ0 hb
  refine ⟨T, u, hsol.mono hT hTb, fun t ht x ↦ ?_⟩
  rw [hut, ← Real.norm_eq_abs]
  exact (BoundedContinuousFunction.norm_coe_le_norm (Q t) x).trans (hbound t ht)

end WaveEquation.SmallData.Classical
