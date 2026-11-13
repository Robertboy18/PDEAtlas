/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherElliptic
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# The integer Sobolev scale of the whole-space wave generator

The massive wave generator maps Hᵏ⁺² × Hᵏ⁺¹ isomorphically onto
Hᵏ⁺¹ × Hᵏ. Its inverse gains one spatial derivative in both components.
The graph identification below concerns the constructed energy semigroup,
so these isomorphisms describe its generator domains.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable (n : ℕ)

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Forgetting higher derivatives embeds the higher wave data into energy space. -/
def higherEnergyInclusionCLM (k : ℕ) :
    (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] EnergyState n :=
  (C).symm.toContinuousLinearMap.comp
    ((lowerOrderCLM (by omega : 1 ≤ k + 1)).prodMap wkpBaseCoordinateCLM)

/-- The energy coordinates of the higher-order inclusion. -/
theorem coordinates_higherEnergyInclusionCLM (k : ℕ)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    C (higherEnergyInclusionCLM n k x) =
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) :=
  (C).apply_symm_apply _

/-- Retaining only energy coordinates does not identify distinct Sobolev data. -/
theorem higherEnergyInclusionCLM_injective (k : ℕ) :
    Function.Injective (higherEnergyInclusionCLM n k) := by
  intro x y h
  have hc := congrArg C h
  rw [coordinates_higherEnergyInclusionCLM, coordinates_higherEnergyInclusionCLM] at hc
  apply Prod.ext
  · apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact congrArg (wkpBaseCoordinateCLM (m := 1)) (congrArg Prod.fst hc)
  · exact wkpBaseCoordinateCLM_injective isOpen_univ (congrArg Prod.snd hc)

/-- At order zero the higher energy coordinates give the original energy space. -/
def zeroOrderEnergyEquiv :
    (H¹(ℝ^n) × W^{0,2}(ℝ^n)) ≃L[ℝ] EnergyState n :=
  ((ContinuousLinearEquiv.refl ℝ H¹(ℝ^n)).prodCongr
    lpEquivZeroOrder.symm.toContinuousLinearEquiv).trans (C).symm

/-- The wave generator is an isomorphism between consecutive Sobolev energy levels. -/
def higherGeneratorEquiv (k : ℕ) :
    (W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) ≃L[ℝ]
      (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
  (ContinuousLinearEquiv.prodComm ℝ _ _).trans
    ((ContinuousLinearEquiv.refl ℝ _).prodCongr
      ((higherMassiveLaplacianEquiv n k).trans (ContinuousLinearEquiv.neg ℝ)))

/-- The higher generator acts by velocity and massive acceleration. -/
theorem higherGeneratorEquiv_apply (k : ℕ)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :
    higherGeneratorEquiv n k x =
      (x.2, -(lowerOrderCLM (by omega : k ≤ k + 2) x.1 -
        higherOrderLaplacianCLM le_rfl x.1)) := rfl

/-- Higher Sobolev data belong to the wave generator graph. -/
theorem hasGeneratorAt_higherOrder (k : ℕ)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :
    (linearSemigroup n).HasGeneratorAt
      (higherEnergyInclusionCLM n (k + 1) x)
      (higherEnergyInclusionCLM n k (higherGeneratorEquiv n k x)) := by
  apply (linearSemigroup_generator_iff _ _).mpr
  rw [coordinates_higherEnergyInclusionCLM, coordinates_higherEnergyInclusionCLM,
    higherGeneratorEquiv_apply]
  constructor
  · rfl
  · dsimp only
    rw [map_neg, map_neg, neg_neg, map_sub, higherOrderLaplacianCLM_base]
    have hm := massForm_h2 (lowerOrderCLM (by omega : 2 ≤ k + 2) x.1)
    rw [lowerOrderCLM_trans_apply] at hm
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex] using hm

end PDE.Hyperbolic.NonlinearWave.Cauchy
