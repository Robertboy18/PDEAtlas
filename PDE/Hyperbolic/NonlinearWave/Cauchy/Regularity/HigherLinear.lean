/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.InverseGenerator

/-!
# Whole-space wave evolution at every integer Sobolev order

Iterating the differential generator isomorphism transports the constructed
energy semigroup to Hᵏ⁺¹ × Hᵏ. Commutation with the smoothing inverse proves
that this transport preserves the original displacement and velocity. Thus
higher regularity is propagated by the whole-space wave evolution,
with strong continuity at every order.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

variable (n : ℕ)

/-- Iterating the wave generator identifies each higher Sobolev energy level
with the original energy space. This equivalence differentiates the data. -/
def higherEnergyEquiv : (k : ℕ) →
    (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) ≃L[ℝ] EnergyState n
  | 0 => zeroOrderEnergyEquiv n
  | k + 1 => (higherGeneratorEquiv n k).trans (higherEnergyEquiv k)

/-- Raising the Sobolev level once applies the smoothing inverse. -/
theorem higherEnergyInclusionCLM_symm_equiv_succ (k : ℕ) (z : EnergyState n) :
    higherEnergyInclusionCLM n (k + 1) ((higherEnergyEquiv n (k + 1)).symm z) =
      inverseGeneratorCLM n (higherEnergyInclusionCLM n k ((higherEnergyEquiv n k).symm z)) := by
  rw [higherEnergyInclusionCLM_succ]
  change inverseGeneratorCLM n (higherEnergyInclusionCLM n k (higherGeneratorEquiv n k
      ((higherGeneratorEquiv n k).symm ((higherEnergyEquiv n k).symm z)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The constructed energy evolution preserves the range of every smoothing
power. -/
theorem linearSemigroup_higherEnergyInclusionCLM_symm (k : ℕ) (t : NNReal) (z : EnergyState n) :
    linearSemigroup n t (higherEnergyInclusionCLM n k ((higherEnergyEquiv n k).symm z)) =
      higherEnergyInclusionCLM n k ((higherEnergyEquiv n k).symm (linearSemigroup n t z)) := by
  induction k with
  | zero =>
    simp only [higherEnergyEquiv, higherEnergyInclusionCLM_zero,
      ContinuousLinearEquiv.apply_symm_apply]
  | succ k ih =>
    rw [higherEnergyInclusionCLM_symm_equiv_succ, linearSemigroup_inverseGeneratorCLM,
      ih, higherEnergyInclusionCLM_symm_equiv_succ]

/-- The constructed whole-space wave semigroup on Hᵏ⁺¹ × Hᵏ. -/
def higherLinearSemigroup (k : ℕ) :
    StronglyContinuousSemigroup (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) where
  toMonoidHom :=
    { toFun := fun t ↦ (higherEnergyEquiv n k).symm.toContinuousLinearMap.comp
        ((linearSemigroup n t.toAdd).comp (higherEnergyEquiv n k).toContinuousLinearMap)
      map_one' := by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change (higherEnergyEquiv n k).symm
          (linearSemigroup n 0 (higherEnergyEquiv n k x)) = x
        rw [(linearSemigroup n).map_zero_apply, ContinuousLinearEquiv.symm_apply_apply]
      map_mul' := by
        intro s t
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change (higherEnergyEquiv n k).symm
          (linearSemigroup n (s.toAdd + t.toAdd) (higherEnergyEquiv n k x)) =
          (higherEnergyEquiv n k).symm
            (linearSemigroup n s.toAdd
              (higherEnergyEquiv n k ((higherEnergyEquiv n k).symm
                (linearSemigroup n t.toAdd (higherEnergyEquiv n k x)))))
        rw [ContinuousLinearEquiv.apply_symm_apply, (linearSemigroup n).map_add_apply] }
  continuous_toPointwise := by
    refine PointwiseConvergenceCLM.continuous_of_continuous_eval fun x ↦ ?_
    exact (higherEnergyEquiv n k).symm.continuous.comp
      ((linearSemigroup n).continuous_orbit (higherEnergyEquiv n k x))

/-- The higher evolution is the differential-coordinate transport of the
constructed energy evolution. -/
theorem higherLinearSemigroup_apply (k : ℕ) (t : NNReal)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherLinearSemigroup n k t x =
      (higherEnergyEquiv n k).symm
        (linearSemigroup n t (higherEnergyEquiv n k x)) := rfl

/-- Forgetting higher derivatives recovers the original energy trajectory,
including its initial data. -/
theorem higherEnergyInclusionCLM_higherLinearSemigroup (k : ℕ) (t : NNReal)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherEnergyInclusionCLM n k (higherLinearSemigroup n k t x) =
      linearSemigroup n t (higherEnergyInclusionCLM n k x) := by
  rw [higherLinearSemigroup_apply, ← linearSemigroup_higherEnergyInclusionCLM_symm,
    ContinuousLinearEquiv.symm_apply_apply]

end PDE.Hyperbolic.NonlinearWave.Cauchy
