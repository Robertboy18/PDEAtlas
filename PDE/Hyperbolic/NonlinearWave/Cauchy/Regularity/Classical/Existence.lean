/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

/-!
# Local classical realization of the constructed energy solution

The explicit saturating reaction admits local higher regularity in every
positive dimension for data above the stated integer Sobolev threshold.
All regularity is derived from the energy evolution.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- Smooth enough data give jointly continuous pointwise displacement, velocity,
and acceleration representing every original energy solution locally in time.
The PDE and time derivatives hold at every spatial point, with within-interval
derivatives at the initial and final times. -/
theorem IsEnergySolution.exists_local_pointwise_saturatingReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution lipschitzWith_saturatingReaction saturatingReaction_zero
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) u) :
    ∃ b : ℝ, 0 < b ∧ ∃ q v a : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 b ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        v (0, y) = classicalRepresentativeCLM hv x.2 y) ∧
      ∀ t ∈ Icc 0 b,
        (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (u t).1 ∧
        (fun y ↦ v (t, y)) =ᵐ[volume] (u t).2 ∧
        ContDiff ℝ 2 (fun y ↦ q (t, y)) ∧
        ∀ y, HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Icc 0 b) t ∧
          HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Icc 0 b) t ∧
          a (t, y) - Δ (fun z ↦ q (t, z)) y + saturatingReaction (q (t, y)) = 0 := by
  obtain ⟨b, hb, U, hU₀, hU⟩ := h.exists_local_higherOrder_saturatingReaction (k := k + 1) hv x
  let q : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).1) hq U.continuous.fst⟩
  let v : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hv (U p.1).2 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).2) hv U.continuous.snd⟩
  let a : C(ℝ × ℝ^n, ℝ) :=
    ⟨fun p ↦ classicalRepresentativeCLM hk (higherSaturatingAcceleration hk (U p.1).1) p.2,
      continuous_classicalRepresentativeCLM
        (u := fun t : ℝ ↦ higherSaturatingAcceleration hk (U t).1) hk
        ((continuous_higherSaturatingAcceleration hk).comp U.continuous.fst)⟩
  have hdt (t : ℝ) (ht : t ∈ Icc 0 b) := h.hasDerivWithinAt_higherOrder hk x U hU₀ hU ht
  refine ⟨b, hb, q, v, a, contDiffOn_two_higherWave hk hv hq U
    ⟨_, (continuous_higherSaturatingAcceleration hk).comp U.continuous.fst⟩ isOpen_Ioo
    (fun t ht ↦ (hdt t ⟨ht.1.le, ht.2.le⟩).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht ↦ (hdt t ⟨ht.1.le, ht.2.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)), ?_, ?_⟩
  · intro y
    change classicalRepresentativeCLM hq (U 0).1 y = _ ∧ classicalRepresentativeCLM hv (U 0).2 y = _
    rw [hU₀]
    exact ⟨rfl, rfl⟩
  · intro t ht
    have hproj := hU t ht
    refine ⟨by rw [← hproj]; exact classicalRepresentativeCLM_ae hq (U t).1,
      by rw [← hproj]; exact classicalRepresentativeCLM_ae hv (U t).2,
      contDiff_classicalRepresentativeCLM hq (by push_cast; linarith) (U t).1, fun y ↦
        ⟨hasDerivWithinAt_classicalRepresentative_lowerOrder hv hq (Nat.le_succ (k + 1))
          (hdt t ht).1 y, hasDerivWithinAt_classicalRepresentative_lowerOrder hk hv
            (Nat.le_succ k) (hdt t ht).2 y, ?_⟩⟩
    change classicalRepresentativeCLM hk (higherSaturatingAcceleration hk (U t).1) y -
      Δ (classicalRepresentativeCLM hq (U t).1 : ℝ^n → ℝ) y +
        saturatingReaction (classicalRepresentativeCLM hq (U t).1 y) = 0
    rw [classicalRepresentative_higherSaturatingAcceleration hk hq]
    abel

end PDE.Hyperbolic.NonlinearWave.Cauchy
