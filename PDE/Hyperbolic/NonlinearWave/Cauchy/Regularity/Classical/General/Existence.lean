/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Pointwise
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

/-!
# General smooth reactions give local classical energy solutions

In every positive dimension, smooth globally Lipschitz reactions fixing zero
admit a local classical realization of every constructed energy solution with
sufficiently regular Sobolev data. Composition continuity and pointwise
regularity are conclusions of the construction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]
variable {f : ℝ → ℝ} {K : ℝ≥0}

/-- An energy trajectory with a constructed higher lift has classical fields
on the entire lift interval. This assembly is used both for local existence
and continuation; time derivatives follow from the integrated energy PDE. -/
theorem IsEnergySolution.exists_pointwise_higherLift_smoothReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) u)
    {b : ℝ} (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hU₀ : U 0 = x) (hU : ∀ t ∈ Icc 0 b,
      (lowerOrderCLM (by omega : 1 ≤ k + 2) (U t).1,
        wkpBaseCoordinateCLM (U t).2) = u t) :
    ∃ q v a : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 b ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        v (0, y) = classicalRepresentativeCLM hv x.2 y) ∧
      ∀ t ∈ Icc 0 b,
        (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (u t).1 ∧
        (fun y ↦ v (t, y)) =ᵐ[volume] (u t).2 ∧
        ContDiff ℝ 2 (fun y ↦ q (t, y)) ∧
        ∀ y, HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Icc 0 b) t ∧
          HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Icc 0 b) t ∧
          a (t, y) - Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  let q : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).1) hq U.continuous.fst⟩
  let v : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hv (U p.1).2 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).2) hv U.continuous.snd⟩
  let a : C(ℝ × ℝ^n, ℝ) :=
    ⟨fun p ↦ classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 (U p.1).1) p.2,
      continuous_classicalRepresentativeCLM
        (u := fun t : ℝ ↦ higherSmoothAcceleration hk hs hf0 (U t).1) hk
        ((continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst)⟩
  have hdt (t : ℝ) (ht : t ∈ Icc 0 b) :=
    h.hasDerivWithinAt_higherOrder_smoothReaction hk hs hf hf0 x U hU₀ hU ht
  refine ⟨q, v, a, contDiffOn_two_higherWave hk hv hq U
    ⟨_, (continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst⟩ isOpen_Ioo
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
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 (U t).1) y -
      Δ (classicalRepresentativeCLM hq (U t).1 : ℝ^n → ℝ) y +
        f (classicalRepresentativeCLM hq (U t).1 y) = 0
    rw [classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq]
    abel

/-- An energy trajectory with a global higher lift has global classical fields: a jointly C²
displacement on positive times, with both time derivatives, the right initial traces and the
pointwise wave equation at every nonnegative time. This is the half-line form of
`IsEnergySolution.exists_pointwise_higherLift_smoothReaction`. -/
theorem IsEnergySolution.exists_global_pointwise_higherLift_smoothReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) e)
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hU₀ : U 0 = x) (hU : ∀ t : ℝ, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ k + 2) (U t).1,
        wkpBaseCoordinateCLM (U t).2) = e t) :
    ∃ q v a : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioi 0 ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        v (0, y) = classicalRepresentativeCLM hv x.2 y) ∧
      ∀ t : ℝ, 0 ≤ t →
        (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (e t).1 ∧
        (fun y ↦ v (t, y)) =ᵐ[volume] (e t).2 ∧
        ContDiff ℝ 2 (fun y ↦ q (t, y)) ∧
        ∀ y, HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Ici 0) t ∧
          HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Ici 0) t ∧
          a (t, y) - Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  let q : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).1) hq U.continuous.fst⟩
  let v : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hv (U p.1).2 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).2) hv U.continuous.snd⟩
  let a : C(ℝ × ℝ^n, ℝ) :=
    ⟨fun p ↦ classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 (U p.1).1) p.2,
      continuous_classicalRepresentativeCLM
        (u := fun t : ℝ ↦ higherSmoothAcceleration hk hs hf0 (U t).1) hk
        ((continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst)⟩
  have hdt (t : ℝ) (ht : 0 ≤ t) :=
    he.hasDerivWithinAt_higherOrder_smoothReaction hk hs hf hf0 x U hU₀
      (b := t + 1) (fun s hst ↦ hU s hst.1) (t := t) ⟨ht, by linarith⟩
  have hnb (t : ℝ) : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith)))
  refine ⟨q, v, a, contDiffOn_two_higherWave hk hv hq U
    ⟨_, (continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst⟩ isOpen_Ioi
    (fun t ht ↦ (hdt t ht.le).1.hasDerivAt (Icc_mem_nhds ht (by linarith)))
    (fun t ht ↦ (hdt t ht.le).2.hasDerivAt (Icc_mem_nhds ht (by linarith))), ?_, ?_⟩
  · intro y
    change classicalRepresentativeCLM hq (U 0).1 y = _ ∧ classicalRepresentativeCLM hv (U 0).2 y = _
    rw [hU₀]
    exact ⟨rfl, rfl⟩
  · intro t ht
    have hproj := hU t ht
    refine ⟨by rw [← hproj]; exact classicalRepresentativeCLM_ae hq (U t).1,
      by rw [← hproj]; exact classicalRepresentativeCLM_ae hv (U t).2,
      contDiff_classicalRepresentativeCLM hq (by push_cast; linarith) (U t).1, fun y ↦ ?_⟩
    refine ⟨(hasDerivWithinAt_classicalRepresentative_lowerOrder hv hq
      (Nat.le_succ (k + 1)) (hdt t ht).1 y).mono_of_mem_nhdsWithin (hnb t),
      (hasDerivWithinAt_classicalRepresentative_lowerOrder hk hv
        (Nat.le_succ k) (hdt t ht).2 y).mono_of_mem_nhdsWithin (hnb t), ?_⟩
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 (U t).1) y -
      Δ (classicalRepresentativeCLM hq (U t).1 : ℝ^n → ℝ) y +
        f (classicalRepresentativeCLM hq (U t).1 y) = 0
    rw [classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq]
    abel

/-- Smooth enough data give jointly continuous pointwise displacement, velocity,
and acceleration representing every original energy solution locally in time.
The PDE and time derivatives hold at every spatial point, with within-interval
derivatives at the initial and final times. -/
theorem IsEnergySolution.exists_local_pointwise_smoothReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
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
          a (t, y) - Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  obtain ⟨b, hb, U, hU₀, hU⟩ :=
    h.exists_local_higherOrder_smoothReaction (k := k + 1) hv hs hf hf0 x
  obtain ⟨q, v, a, hq₂, hzero, hfield⟩ :=
    h.exists_pointwise_higherLift_smoothReaction hk hs hf hf0 hq hv x U hU₀ hU
  exact ⟨b, hb, q, v, a, hq₂, hzero, hfield⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
