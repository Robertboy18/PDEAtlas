/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Cutoff
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Pointwise

/-!
# Strong time derivatives without a global scalar Lipschitz assumption

On each compact mild prefix a scalar cutoff leaves the source unchanged. The
cutoff energy evolution supplies both integrated wave equations, whose injective
Sobolev projections give the strong derivatives. Equality on the scalar range
then removes the cutoff from the acceleration as well.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Every compact higher mild trajectory for a smooth reaction fixing zero
has the displacement and velocity derivatives. -/
theorem hasDerivWithinAt_of_higher_mild (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)} {τ : ℝ≥0}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hf hf0) x τ V) :
    ∀ t ∈ Icc 0 (τ : ℝ),
      HasDerivWithinAt
          (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (IccExtend τ.property V s).1)
          (IccExtend τ.property V t).2 (Icc 0 (τ : ℝ)) t ∧
        HasDerivWithinAt
          (fun s ↦ lowerOrderCLM (Nat.le_succ k) (IccExtend τ.property V s).2)
          (higherSmoothAcceleration hk hf hf0 (IccExtend τ.property V t).1)
          (Icc 0 (τ : ℝ)) t := by
  obtain ⟨g, K, hg, hg0, hLip, he⟩ := exists_cutoff_on_higher_curve hq hf hf0 V
  have hVg := isMildSolutionOn_of_representative_eq hv hq hf hf0 hg hg0 V hV
    (fun t y ↦ (he t y).symm)
  obtain ⟨u, hu⟩ := exists_energySolution hLip hg0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2)
  let U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  have hU0 : U 0 = x := by
    change IccExtend τ.property V 0 = x
    rw [IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩]
    exact hV.initial_value
  have hproj := hu.eq_higherSmooth_mild_projection hv hg hLip hg0 x V hVg
  intro t ht
  have hd := hu.hasDerivWithinAt_higherOrder_smoothReaction hk hg hLip hg0 x U hU0 hproj ht
  have hacc : higherSmoothAcceleration hk hg hg0 (U t).1 =
      higherSmoothAcceleration hk hf hf0 (U t).1 := by
    apply classicalRepresentativeCLM_injective hk
    ext y
    rw [classicalRepresentative_higherSmoothAcceleration hk hg hg0 hq,
      classicalRepresentative_higherSmoothAcceleration hk hf hf0 hq]
    congr 1
    change g (classicalRepresentativeCLM hq (IccExtend τ.property V t).1 y) =
      f (classicalRepresentativeCLM hq (IccExtend τ.property V t).1 y)
    rw [IccExtend_of_mem τ.property V ht]
    exact he ⟨t, ht⟩ y
  exact ⟨hd.1, hacc ▸ hd.2⟩

end WaveEquation.SmallData.Classical.NormBlowup
