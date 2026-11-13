/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.StrongEvolution
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.HigherJet

/-!
# A two-sided zero-displacement jet for a mild prefix

The linear backward jet preserves the entire forward mild curve.
Its acceleration at zero vanishes because both the displacement and the scalar
reaction vanish there. The resulting derivatives are ordinary derivatives across the initial time.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev Laplacian

namespace WaveEquation.SmallData.Classical.NormBlowup

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Extend a zero-displacement mild prefix through zero while retaining
its entire forward state and the acceleration of the original reaction. -/
theorem exists_jet_of_higher_mild (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (H : W^{k + 2,2}(ℝ^n)) {τ : ℝ≥0} (hτ : 0 < τ)
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hf hf0)
      (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) τ V) :
    ∃ U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)),
      ∃ A : C(ℝ, W^{k,2}(ℝ^n)),
        U 0 = (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) ∧
        (∀ t, 0 ≤ t → U t = IccExtend τ.property V t) ∧
        (∀ t < (τ : ℝ),
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1)
            (U t).2 t) ∧
        (∀ t < (τ : ℝ),
          HasDerivAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2) (A t) t) ∧
        ∀ t ∈ Ico 0 (τ : ℝ), A t = higherSmoothAcceleration hk hf hf0 (U t).1 := by
  let W : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  have hW0 : W 0 = (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) := by
    change IccExtend τ.property V 0 = _
    rw [IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩]
    exact hV.initial_value
  let B : C(ℝ, W^{k,2}(ℝ^n)) := ⟨fun t ↦ higherSmoothAcceleration hk hf hf0 (W t).1,
      (continuous_higherSmoothAcceleration hk hf hf0).comp W.continuous.fst⟩
  have hB0 : B 0 = 0 := by
    apply classicalRepresentativeCLM_injective hk
    ext y
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hf hf0 (W 0).1) y = _
    rw [hW0]
    change classicalRepresentativeCLM hk (higherSmoothAcceleration hk hf hf0 0) y = _
    rw [classicalRepresentative_higherSmoothAcceleration hk hf hf0 hq]
    simp only [map_zero]
    change Δ (fun _ : ℝ^n ↦ (0 : ℝ)) y - f 0 = 0
    rw [hf0, sub_zero]
    exact congrFun InnerProductSpace.laplacian_const y
  have hd := hasDerivWithinAt_of_higher_mild hk hv hq hf hf0 V hV
  obtain ⟨U, A, he, hQ, hD⟩ := exists_higherZeroJet_extension H W B hW0 hB0
    (show (0 : ℝ) < τ from hτ) (fun t ht ↦ (hd t ht).1) (fun t ht ↦ (hd t ht).2)
  refine ⟨U, A, (he 0 le_rfl).1.trans hW0, fun t ht ↦ (he t ht).1, hQ, hD, fun t ht ↦ ?_⟩
  rw [(he t ht.1).1, (he t ht.1).2]
  rfl

end WaveEquation.SmallData.Classical.NormBlowup
