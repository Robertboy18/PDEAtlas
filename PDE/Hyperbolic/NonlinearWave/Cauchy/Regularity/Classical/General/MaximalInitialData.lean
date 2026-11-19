/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.MaximalClassical

/-!
# Cauchy traces of the maximal classical field

The canonical field has the prescribed displacement and right time derivative
at zero. Both facts follow from a finite mild trajectory agreeing with the
maximal trajectory near its initial time.
-/

@[expose] public noncomputable section

open Filter PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The maximal classical field starts at the canonical initial displacement. -/
theorem higherSmoothMaximalField_zero (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) (y : ℝ^n) :
    higherSmoothMaximalField hv hq hs hf0 x (timeSpaceCons 0 y) =
      classicalRepresentativeCLM hq x.1 y := by
  rw [higherSmoothMaximalField_timeSpaceCons]
  exact congrArg (fun z : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) ↦ classicalRepresentativeCLM hq z.1 y)
    ((higherLinearSemigroup n (k + 1)).maximalMildSolution_zero (F := higherSmoothMap hv hs hf0)
      (locallyLipschitz_higherSmoothSource hv hs hf0) x)

/-- The right time derivative at zero is the canonical initial velocity. -/
theorem hasDerivWithinAt_higherSmoothMaximalField_zero (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    (y : ℝ^n) :
    HasDerivWithinAt (fun t ↦ higherSmoothMaximalField hv hq hs hf0 x
      (timeSpaceCons t y)) (classicalRepresentativeCLM hv x.2 y) (Ici 0) 0 := by
  let S := higherLinearSemigroup n (k + 1)
  let F := higherSmoothMap hv hs hf0
  have hF : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hv hs hf0
  obtain ⟨τ, hτ, V, hV⟩ :=
    (S.lt_mildLifespan_iff_exists_longer F x (τ := 0)).mp (S.mildLifespan_pos hF x)
  have heq := StronglyContinuousSemigroup.maximalMildSolution_eqOn hF hV
  have hzero : IccExtend τ.property V 0 = x :=
    (IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩).trans hV.initial_value
  have hd := (hasDerivWithinAt_classical_higherSmooth_trajectory
    hk hv hq hs hf0 V hV ⟨le_rfl, τ.property⟩ y).1
  dsimp only at hd
  rw [hzero] at hd
  have hfield (t : ℝ) (ht : t ∈ Icc 0 (τ : ℝ)) :
      higherSmoothMaximalField hv hq hs hf0 x (timeSpaceCons t y) =
        classicalRepresentativeCLM hq (IccExtend τ.property V t).1 y := by
    rw [higherSmoothMaximalField_timeSpaceCons]
    exact congrArg (fun z : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) ↦
      classicalRepresentativeCLM hq z.1 y) (heq ht)
  exact (hd.congr_of_mem hfield ⟨le_rfl, τ.property⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE (show (0 : ℝ) < τ from hτ))

end PDE.Hyperbolic.NonlinearWave.Cauchy
