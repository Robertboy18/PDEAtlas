/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Composition

/-!
# Continuity of the observed smooth composition

Scalar derivative bounds and the constructed Sobolev embedding control the
composition in the uniform norm.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- The bounded continuous observation of smooth composition is Lipschitz
on each Sobolev norm ball, using only a scalar Lipschitz bound on its range. -/
theorem exists_lipschitzOn_observed_composition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun u : W^{k,2}(ℝ^n) ↦
      classicalRepresentativeCLM hk (higherComposition hk hf hf0 u)) (Metric.closedBall 0 R) := by
  let A := classicalRepresentativeCLM hk
  let B := ‖A‖ * max R 0
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨K, hK⟩ := hf1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-B) B) isCompact_Icc
  refine ⟨K * ‖A‖₊, LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_⟩
  have hvalue (w : W^{k,2}(ℝ^n)) (hw : w ∈ Metric.closedBall 0 R) (x : ℝ^n) :
      A w x ∈ Icc (-B) B := by
    apply abs_le.mp
    have hwR : ‖w‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hw' : ‖w‖ ≤ max R 0 := hwR.trans (le_max_left _ _)
    exact ((A w).norm_coe_le_norm x).trans
      ((A.le_opNorm w).trans (mul_le_mul_of_nonneg_left hw' A.opNorm_nonneg))
  rw [dist_eq_norm]
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x ↦ ?_
  simp only [BoundedContinuousFunction.sub_apply, classicalRepresentative_higherComposition]
  calc
    ‖f (A u x) - f (A v x)‖ ≤ K * ‖A u x - A v x‖ :=
      hK.dist_le_mul _ (hvalue u hu x) _ (hvalue v hv x)
    _ ≤ K * (‖A‖ * ‖u - v‖) := by
      apply mul_le_mul_of_nonneg_left _ K.2
      have he : A u x - A v x = A (u - v) x := by simp
      rw [he]
      exact ((A (u - v)).norm_coe_le_norm x).trans (A.le_opNorm (u - v))
    _ = ↑(K * ‖A‖₊) * dist u v := by
      simp only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm, mul_assoc]

/-- The observed composition is locally Lipschitz in the uniform norm. -/
theorem locallyLipschitz_observed_composition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (fun u : W^{k,2}(ℝ^n) ↦ classicalRepresentativeCLM hk
      (higherComposition hk hf hf0 u)) := by
  intro u
  obtain ⟨K, hK⟩ := exists_lipschitzOn_observed_composition hk hf hf0 (‖u‖ + 1)
  refine ⟨K, Metric.closedBall 0 (‖u‖ + 1), ?_, hK⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy
