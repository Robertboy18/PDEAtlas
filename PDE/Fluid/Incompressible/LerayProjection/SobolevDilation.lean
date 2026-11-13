/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Dilation
public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Sobolev dilation and Leray commutation

The actual scalar dilation acts componentwise on vector Sobolev graphs.
The base row identifies its spatial action in the fluid L² pivot. Injectivity
of this row lifts the established L² dilation/Leray commutation to every order.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace IncompressibleFlow

variable {n k : ℕ}

local notation "μ" => domainMeasure n Set.univ

/-- Taking a component of a vector Sobolev row recovers its scalar graph coordinate. -/
theorem l2Coordinate_l2SobolevRow (j : Fin n) (α : DerivIndex n k) (u : VectorH n k) :
    l2Coordinate j (l2SobolevRow α u) = wkpCoordinateCLM α (u j) :=
  l2Coordinate_euclideanTuple j _

/-- The physical vector base row determines the entire vector Sobolev graph. -/
theorem l2SobolevRow_base_injective :
    Function.Injective (l2SobolevRow (baseIndex n k)) := by
  intro u v huv
  apply PiLp.ext
  intro j
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  have h := congrArg (l2Coordinate j) huv
  simpa only [l2Coordinate_l2SobolevRow, wkpBaseCoordinateCLM_apply,
    wkpCoordinateCLM_apply] using h

/-- Dilation commutes with assembling the physical scalar components of a vector field. -/
theorem l2Dilation_euclideanTuple (a : ℝ) (ha : a ≠ 0)
    (f : Fin n → DerivLp n 2 Set.univ) :
    l2Dilation a ha (Lp.euclideanTuple f) =
      Lp.euclideanTuple (fun j ↦ Lp.compSMul μ 2 a ha (f j)) := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul μ ha).ae (Lp.euclideanTuple_apply_ae f)
  filter_upwards [l2Dilation_ae a ha (Lp.euclideanTuple f), hs,
    Lp.euclideanTuple_apply_ae (fun j ↦ Lp.compSMul μ 2 a ha (f j)),
    ae_all_iff.mpr (fun j ↦ Lp.coeFn_compSMul μ 2 a ha (f j))] with x hd hs ht hc
  apply PiLp.ext
  intro j
  rw [hd, hs j, ht j, hc j]

/-- Each derivative row has the exact weak chain-rule factor under vector dilation. -/
theorem l2SobolevRow_vectorDilation (a : ℝ) (ha : a ≠ 0)
    (α : DerivIndex n k) (u : VectorH n k) :
    l2SobolevRow α (vectorDilation n k a ha u) =
      a ^ α.toList.length • l2Dilation a ha (l2SobolevRow α u) := by
  simp only [l2SobolevRow_apply, vectorDilation_apply, dilationWkpCLM_coordinate,
    l2Dilation_euclideanTuple]
  exact map_smul Lp.euclideanTuple (a ^ α.toList.length)
    (fun j ↦ Lp.compSMul μ 2 a ha (wkpCoordinateCLM α (u j)))

/-- The base row is the literal dilation of the physical vector field. -/
theorem l2SobolevRow_base_vectorDilation (a : ℝ) (ha : a ≠ 0) (u : VectorH n k) :
    l2SobolevRow (baseIndex n k) (vectorDilation n k a ha u) =
      l2Dilation a ha (l2SobolevRow (baseIndex n k) u) := by
  rw [l2SobolevRow_vectorDilation]
  simp only [baseIndex_toList, List.length_nil, pow_zero, one_smul]

/-- The actual Sobolev Leray projector commutes with nonzero spatial dilation. -/
theorem leraySobolev_vectorDilation (a : ℝ) (ha : a ≠ 0) (u : VectorH n k) :
    leraySobolev n k (vectorDilation n k a ha u) =
      vectorDilation n k a ha (leraySobolev n k u) := by
  apply l2SobolevRow_base_injective
  rw [l2SobolevRow_leraySobolev, l2SobolevRow_base_vectorDilation,
    lerayProjection_l2Dilation, l2SobolevRow_base_vectorDilation,
    l2SobolevRow_leraySobolev]

end IncompressibleFlow
