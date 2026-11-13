/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FiniteInterval

/-!
# Energy waves with nonlinear gradient and velocity dependence

The reaction `‖Du‖ + |u_t| + u` is Lipschitz with constant `3` and is not
differentiable. For every datum in `H¹(ℝⁿ) × L²(ℝⁿ)` the wave equation with this
reaction has a unique global energy solution (`FirstJet.exists_unique_energySolution`)
and a unique bounded energy solution on every interval `[0, τ]`
(`FirstJet.exists_unique_energySolutionOn`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Examples.Cauchy.FirstJet

open PDE.Hyperbolic.NonlinearWave.Cauchy

/-- A globally Lipschitz reaction depending on the gradient, velocity and value. -/
def normReaction {n : ℕ} (z : ℝ^n × ℝ × ℝ) : ℝ :=
  ‖z.1‖ + ‖z.2.1‖ + z.2.2

/-- `normReaction` is Lipschitz with constant `3`. -/
theorem normReaction_lipschitz (n : ℕ) : LipschitzWith 3 (normReaction (n := n)) := by
  have hp : LipschitzWith 1 (fun z : ℝ^n × ℝ × ℝ ↦ ‖z.1‖) := by
    exact (lipschitzWith_one_norm.comp LipschitzWith.prod_fst).weaken (by norm_num)
  have hv : LipschitzWith 1 (fun z : ℝ^n × ℝ × ℝ ↦ ‖z.2.1‖) := by
    exact (lipschitzWith_one_norm.comp
      (LipschitzWith.prod_fst.comp LipschitzWith.prod_snd)).weaken (by norm_num)
  have hq : LipschitzWith 1 (fun z : ℝ^n × ℝ × ℝ ↦ z.2.2) := by
    exact (LipschitzWith.prod_snd.comp LipschitzWith.prod_snd).weaken (by norm_num)
  exact ((hp.add hv).add hq).weaken (by norm_num)

/-- Every energy datum has a unique global energy solution. -/
example {n : ℕ} (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      FirstJet.IsEnergySolution (normReaction_lipschitz n) (by simp [normReaction]) x u ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
        FirstJet.IsEnergySolution (normReaction_lipschitz n) (by simp [normReaction]) x v →
          EqOn u v (Ici 0) :=
  FirstJet.exists_unique_energySolution (normReaction_lipschitz n)
    (by simp [normReaction]) x

/-- On every interval `[0, τ]` there is a unique energy solution, and it is bounded. -/
example {n : ℕ} (x : H¹(ℝ^n) × DerivLp n 2 univ) (τ : NNReal) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      FirstJet.IsEnergySolutionOn (normReaction_lipschitz n) (by simp [normReaction]) x τ u ∧
      (∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 (τ : ℝ), ‖u t‖ ≤ R) ∧
      ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
        FirstJet.IsEnergySolutionOn (normReaction_lipschitz n) (by simp [normReaction]) x τ v →
          EqOn u v (Icc 0 (τ : ℝ)) :=
  FirstJet.exists_unique_energySolutionOn (normReaction_lipschitz n)
    (by simp [normReaction]) x τ

end PDE.Examples.Cauchy.FirstJet
