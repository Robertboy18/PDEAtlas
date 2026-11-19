/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Linear
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.WholeSpace

/-!
# H² × H¹ initial data for the whole-space wave generator

Whole-space integration by parts identifies the constructed massive wave
generator on H² × H¹ with `(u,v) ↦ (v, Δu - u)`. This proves domain membership
from Sobolev regularity of the data, without an assumed weak operator equation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert InnerProductSpace Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The variational equations characterize the full graph of the constructed generator. -/
theorem linearSemigroup_generator_iff (x y : EnergyState n) :
    (linearSemigroup n).HasGeneratorAt x y ↔ (energyTriple n).inclusion (C y).1 = (C x).2 ∧
      massForm n (C x).1 = -(energyTriple n).pivotToDual (C y).2 := by
  rw [(linearSemigroup n).hasGeneratorAt_iff_mem_generatorPMap_graph]
  change (x, y) ∈ (waveContractionSemigroup (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric).generatorPMap.graph ↔ _
  rw [generatorPMap_waveContractionSemigroup]
  exact mem_waveOperator_graph_iff _ _ _ _ x y

/-- The gradient pairing for H² displacement is represented by its L² Laplacian. -/
theorem gradientForm_h2 (u : W^{2,2}(ℝ^n)) (w : H¹(ℝ^n)) :
    gradientForm n (lowerOrderCLM (by decide : 1 ≤ 2) u) w =
      -⟪Δ u, (energyTriple n).inclusion w⟫_ℝ := by
  rw [gradientForm_apply, laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply,
    sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hw := u.property.hasWeakDerivativeOn_from_coordinate [i] [i] (by simp)
  simpa only [wkpCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex, List.cons_append, List.nil_append,
    derivIndexOfList_singleton, derivIndexOfList_pair, secondDerivIndex_two, energyTriple] using
      weakDerivative_integrationByParts_H1_univ i _ _ hw w

/-- The massive form on H² is `u - Δu` as an L² load. -/
theorem massForm_h2 (u : W^{2,2}(ℝ^n)) :
    massForm n (lowerOrderCLM (by decide : 1 ≤ 2) u) =
      (energyTriple n).pivotToDual (wkpBaseCoordinateCLM u - Δ u) := by
  ext w
  have h := gradientForm_h2 u w
  change (massForm n (lowerOrderCLM (by decide : 1 ≤ 2) u)) w -
    (energyTriple n).energyToDual (lowerOrderCLM (by decide : 1 ≤ 2) u) w =
      -⟪Δ u, (energyTriple n).inclusion w⟫_ℝ at h
  rw [GelfandTriple.pivotToDual_apply, inner_sub_left]
  have hbase :
      (energyTriple n).inclusion (lowerOrderCLM (by decide : 1 ≤ 2) u) =
        wkpBaseCoordinateCLM u := rfl
  rw [GelfandTriple.energyToDual_apply, hbase] at h
  exact (sub_eq_iff_eq_add.mp h).trans (by abel)

/-- H² × H¹ data lie in the generator domain, with the expected acceleration. -/
theorem hasGeneratorAt_h2 (u : W^{2,2}(ℝ^n)) (v : H¹(ℝ^n)) :
    (linearSemigroup n).HasGeneratorAt
      ((C).symm (lowerOrderCLM (by decide : 1 ≤ 2) u, (energyTriple n).inclusion v))
      ((C).symm (v, Δ u - wkpBaseCoordinateCLM u)) := by
  apply (linearSemigroup_generator_iff _ _).mpr
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨trivial, ?_⟩
  rw [massForm_h2, ← map_neg, neg_sub]

/-- A pure H¹ velocity source belongs to the generator domain with zero acceleration. -/
theorem hasGeneratorAt_velocity (v : H¹(ℝ^n)) :
    (linearSemigroup n).HasGeneratorAt
      ((C).symm (0, (energyTriple n).inclusion v)) ((C).symm (v, 0)) := by
  apply (linearSemigroup_generator_iff _ _).mpr
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_zero, neg_zero, and_self]

end PDE.Hyperbolic.NonlinearWave.Cauchy
