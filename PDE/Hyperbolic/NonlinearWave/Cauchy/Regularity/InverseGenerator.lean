/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.GeneratorScale

/-!
# The smoothing inverse of the whole-space wave generator

The massive wave generator has a bounded inverse on energy space. This
inverse is built from the whole-space elliptic resolvent. It commutes
with the constructed wave semigroup, providing the regularity mechanism for
all integer Sobolev levels.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable (n : ℕ)

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The order-zero inclusion is the original energy coordinate equivalence. -/
theorem higherEnergyInclusionCLM_zero (x : H¹(ℝ^n) × W^{0,2}(ℝ^n)) :
    higherEnergyInclusionCLM n 0 x = zeroOrderEnergyEquiv n x := by
  apply (C).injective
  rw [coordinates_higherEnergyInclusionCLM]
  change (lowerOrderCLM (by decide : 1 ≤ 1) x.1, wkpBaseCoordinateCLM x.2) =
    C ((C).symm (x.1, wkpBaseCoordinateCLM x.2))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · apply wkpBaseCoordinateCLM_injective isOpen_univ
    rfl
  · rfl

/-- The massive wave generator has trivial kernel, expressed on its graph. -/
theorem linearSemigroup_generator_left_unique {x y z : EnergyState n}
    (hx : (linearSemigroup n).HasGeneratorAt x z) (hy : (linearSemigroup n).HasGeneratorAt y z) :
    x = y := by
  have hx' := (linearSemigroup_generator_iff x z).mp hx
  have hy' := (linearSemigroup_generator_iff y z).mp hy
  apply (C).injective
  apply Prod.ext
  · exact (InnerProductSpace.toDual ℝ H¹(ℝ^n)).injective (hx'.2.trans hy'.2.symm)
  · exact hx'.1.symm.trans hy'.1

/-- The bounded inverse of the massive wave generator, constructed using the
whole-space elliptic inverse and the Sobolev inclusions. -/
def inverseGeneratorCLM : EnergyState n →L[ℝ] EnergyState n :=
  (higherEnergyInclusionCLM n 1).comp
    ((higherGeneratorEquiv n 0).symm.toContinuousLinearMap.comp
      (zeroOrderEnergyEquiv n).symm.toContinuousLinearMap)

/-- Applying the generator to its constructed inverse gives the input. -/
theorem hasGeneratorAt_inverseGeneratorCLM (x : EnergyState n) :
    (linearSemigroup n).HasGeneratorAt (inverseGeneratorCLM n x) x := by
  have h := hasGeneratorAt_higherOrder n 0
    ((higherGeneratorEquiv n 0).symm ((zeroOrderEnergyEquiv n).symm x))
  rw [ContinuousLinearEquiv.apply_symm_apply, higherEnergyInclusionCLM_zero,
    ContinuousLinearEquiv.apply_symm_apply] at h
  exact h

/-- Any generator graph pair is recovered by the constructed inverse. -/
theorem eq_inverseGeneratorCLM_of_hasGeneratorAt
    {x y : EnergyState n} (h : (linearSemigroup n).HasGeneratorAt x y) :
    x = inverseGeneratorCLM n y :=
  linearSemigroup_generator_left_unique n h (hasGeneratorAt_inverseGeneratorCLM n y)

/-- The smoothing inverse commutes with every time evolution operator. -/
theorem linearSemigroup_inverseGeneratorCLM (t : NNReal) (x : EnergyState n) :
    linearSemigroup n t (inverseGeneratorCLM n x) = inverseGeneratorCLM n (linearSemigroup n t x) :=
  eq_inverseGeneratorCLM_of_hasGeneratorAt n ((hasGeneratorAt_inverseGeneratorCLM n x).map t)

/-- Passing up one Sobolev level is application of the inverse generator after
the differential isomorphism between consecutive levels. -/
theorem higherEnergyInclusionCLM_succ (k : ℕ) (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :
    higherEnergyInclusionCLM n (k + 1) x =
      inverseGeneratorCLM n (higherEnergyInclusionCLM n k (higherGeneratorEquiv n k x)) :=
  eq_inverseGeneratorCLM_of_hasGeneratorAt n (hasGeneratorAt_higherOrder n k x)

end PDE.Hyperbolic.NonlinearWave.Cauchy
