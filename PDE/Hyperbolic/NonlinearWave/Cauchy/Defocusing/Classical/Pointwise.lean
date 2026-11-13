/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.GlobalHigher
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.TimeDerivatives
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.ForwardRegularity

/-!
# Global classical correspondence for the three-dimensional defocusing cubic

The derived global higher lift supplies the spatial regularity. The
integrated energy equations supply both strong time derivatives, hence the
pointwise PDE and the right initial traces of its jointly C² representative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

variable {k : ℕ}

/-- The constructed global cubic energy solution from high Sobolev data has
a jointly C² representative, including both right initial traces. -/
theorem exists_global_pointwise_cubic (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (3 : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hv : (3 : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^3) × W^{k + 1,2}(ℝ^3)) :
    ∃ q v a : C(ℝ × ℝ^3, ℝ),
      ContDiffOn ℝ 2 q (Ioi 0 ×ˢ univ) ∧
      ContDiffOn ℝ 1 q (Ici 0 ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        v (0, y) = classicalRepresentativeCLM hv x.2 y) ∧
      ∀ t : ℝ, 0 ≤ t →
        (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative
          (cubicNonlinearity.globalSolution (energyProjectionCLM (k + 1) x) t).1 ∧
        (fun y ↦ v (t, y)) =ᵐ[volume]
          (cubicNonlinearity.globalSolution (energyProjectionCLM (k + 1) x) t).2 ∧
        ContDiff ℝ 2 (fun y ↦ q (t, y)) ∧
        ∀ y, HasDerivWithinAt (fun s ↦ q (s, y)) (v (t, y)) (Ici 0) t ∧
          HasDerivWithinAt (fun s ↦ v (s, y)) (a (t, y)) (Ici 0) t ∧
          a (t, y) - Δ (fun z ↦ q (t, z)) y + q (t, y) ^ 3 = 0 := by
  obtain ⟨U, hU₀, hU⟩ := exists_global_higher_lift hv x
  have he := cubicNonlinearity.globalSolution_isEnergySolution (energyProjectionCLM (k + 1) x)
  let q : C(ℝ × ℝ^3, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).1) hq U.continuous.fst⟩
  let v : C(ℝ × ℝ^3, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hv (U p.1).2 p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ (U t).2) hv U.continuous.snd⟩
  let a : C(ℝ × ℝ^3, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hk
      (higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) (U p.1).1) p.2,
      continuous_classicalRepresentativeCLM (u := fun t : ℝ ↦ higherSmoothAcceleration hk
          (contDiff_id.pow 3) (by simp) (U t).1) hk
        ((continuous_higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp)).comp
          U.continuous.fst)⟩
  have hdt (t : ℝ) (ht : 0 ≤ t) := hasDerivWithinAt_higherOrder_cubic hk x he U hU₀
      (b := t + 1) (fun s hst ↦ hU s hst.1) (t := t) ⟨ht, by linarith⟩
  have hnb (t : ℝ) : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by linarith)))
  refine ⟨q, v, a, ?_, contDiffOn_one_forward_higherWave hk hv hq U fun t ht ↦
    (hdt t ht).1.mono_of_mem_nhdsWithin (hnb t), ?_, ?_⟩
  · exact contDiffOn_two_higherWave hk hv hq U
      ⟨_, (continuous_higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp)).comp
        U.continuous.fst⟩ isOpen_Ioi
      (fun t ht ↦ (hdt t ht.le).1.hasDerivAt (Icc_mem_nhds ht (by linarith)))
      (fun t ht ↦ (hdt t ht.le).2.hasDerivAt (Icc_mem_nhds ht (by linarith)))
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
    change classicalRepresentativeCLM hk
      (higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) (U t).1) y -
      Δ (classicalRepresentativeCLM hq (U t).1 : ℝ^3 → ℝ) y +
        (classicalRepresentativeCLM hq (U t).1 y) ^ 3 = 0
    rw [classicalRepresentative_higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) hq]
    simp only [id_eq]
    abel

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
