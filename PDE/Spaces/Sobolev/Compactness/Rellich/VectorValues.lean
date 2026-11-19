/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
public import PDE.Analysis.Normed.Operator.FiniteProduct

/-!
# Rellich compactness for finite Sobolev systems

The Euclidean value map `vectorWkpValueCLM : H¹(Ω)^d → L²(Ω; ℝ^d)` assembles the scalar base
coordinates (`vectorWkpValueCLM_eq_euclideanTuple`). On a domain carrying the operational
`Boundary.C1ExtensionAtlas`, each scalar inclusion `H¹(Ω) → L²(Ω)` is compact
(`baseCoordinateL2_isCompactOperator_of_c1Domain`), so the value map is compact
(`vectorWkpValueCLM_isCompactOperator_of_c1Domain`).
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Rellich

open MeasureTheory
open scoped ENNReal Sobolev

variable {d n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The Euclidean value map of a finite Sobolev system assembles the scalar base coordinates. -/
theorem vectorWkpValueCLM_eq_euclideanTuple :
    vectorWkpValueCLM (m := d) (p := p) (Ω := Ω) =
      Lp.euclideanTuple.comp (ContinuousLinearMap.pi fun i ↦
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω)).comp
          (ContinuousLinearMap.proj i)) := by
  ext1 u
  apply Lp.ext
  filter_upwards [vectorWkpValueCLM_apply_ae u,
    Lp.euclideanTuple_apply_ae (fun i ↦ wkpBaseCoordinateCLM (u i))] with x hx hy
  refine PiLp.ext fun i ↦ ?_
  rw [hx i]
  exact (hy i).symm

/-- **Rellich compactness for vector fields.** On an operational `C¹` extension domain the
Euclidean value map `H¹(Ω)^d → L²(Ω; ℝ^d)` is compact. -/
theorem vectorWkpValueCLM_isCompactOperator_of_c1Domain [Fact (0 < n)]
    [Boundary.C1ExtensionAtlas n Ω] :
    IsCompactOperator (vectorWkpValueCLM (m := d) (p := 2) (Ω := Ω)) := by
  have hpi := ContinuousLinearMap.isCompactOperator_pi (𝕜 := ℝ) (E := Fin d → H¹(Ω))
    (F := fun _ : Fin d ↦ Lp ℝ 2 (domainMeasure n Ω)) (fun i : Fin d ↦
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ H¹(Ω)) i))
    fun i ↦ baseCoordinateL2_isCompactOperator_of_c1Domain.comp_clm _
  rw [vectorWkpValueCLM_eq_euclideanTuple]
  exact hpi.clm_comp Lp.euclideanTuple

end SobolevSpace.GraphSpace.Rellich
