/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.HigherJet
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Pointwise

/-!
# Constructing a higher wave curve through the initial slice

The forward energy evolution supplies both strong time derivatives. For zero
displacement, a linear backward jet gives a curve with two ordinary time
derivatives on an open interval containing zero.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev Laplacian

namespace WaveEquation.SmallData.Classical

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- The constructed higher wave has two strong time derivatives across zero,
and its forward acceleration is the Laplacian minus the reaction. -/
theorem exists_zeroJet_smoothReaction (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0) (H : W^{k + 2,2}(ℝ^n)) :
    ∃ b : ℝ, 0 < b ∧
      ∃ V : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)),
      ∃ B : C(ℝ, W^{k,2}(ℝ^n)),
        V 0 = (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) ∧
        (∀ t < b,
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (V s).1)
            (V t).2 t) ∧
        (∀ t < b,
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (V s).2) (B t) t) ∧
        ∀ t ∈ Ico 0 b, B t = higherSmoothAcceleration hk hs hf0 (V t).1 := by
  let x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) := (0, lowerOrderCLM (Nat.le_succ (k + 1)) H)
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2)
  obtain ⟨b, hb, U, hU0, hU⟩ := hu.exists_local_higherOrder_smoothReaction hv hs hf hf0 x
  let A : C(ℝ, W^{k,2}(ℝ^n)) := ⟨fun t ↦ higherSmoothAcceleration hk hs hf0 (U t).1,
      (continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst⟩
  have hA0 : A 0 = 0 := by
    apply classicalRepresentativeCLM_injective hk
    ext y
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 (U 0).1) y = _
    rw [hU0]
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 0) y = _
    rw [classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq]
    simp only [map_zero]
    change Δ (fun _ : ℝ^n ↦ (0 : ℝ)) y - f 0 = 0
    rw [hf0, sub_zero]
    exact congrFun InnerProductSpace.laplacian_const y
  have hd (t : ℝ) (ht : t ∈ Icc 0 b) :=
    hu.hasDerivWithinAt_higherOrder_smoothReaction hk hs hf hf0 x U hU0 hU ht
  obtain ⟨V, B, heq, hQ, hV⟩ := exists_higherZeroJet_extension H U A hU0 hA0 hb
    (fun t ht ↦ (hd t ht).1) (fun t ht ↦ (hd t ht).2)
  refine ⟨b, hb, V, B, (heq 0 le_rfl).1.trans hU0, hQ, hV, fun t ht ↦ ?_⟩
  rw [(heq t ht.1).1, (heq t ht.1).2]
  rfl

end WaveEquation.SmallData.Classical
