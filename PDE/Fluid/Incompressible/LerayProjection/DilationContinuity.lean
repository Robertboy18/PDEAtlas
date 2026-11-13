/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation
public import PDE.Analysis.MeasureTheory.Lp.Composition.DilationContinuity

/-!
# Strong continuity of physical vector L² dilation

Scalar strong dilation continuity transfers through the bounded coordinate
maps and finite Euclidean assembly. The resulting statement is joint in the
physical vector field and a positive factor bounded away from zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

local notation "μₙ" => domainMeasure n univ

/-- Physical vector L² dilation is jointly strongly continuous away from a zero factor. -/
theorem continuous_l2Dilation_Ici {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun ua : WholeSpaceL2 n × Ici δ ↦
      l2Dilation ua.2.val (hδ.trans_le ua.2.property).ne' ua.1) := by
  have hscalar := Lp.continuous_compSMul_Ici (n := n) (μ := μₙ) hδ
  have htuple : Continuous (fun ua : WholeSpaceL2 n × Ici δ ↦
      fun j : Fin n ↦ Lp.compSMul μₙ 2 ua.2.val
        (hδ.trans_le ua.2.property).ne' (l2Coordinate j ua.1)) := by
    apply continuous_pi
    intro j
    have hc : Continuous (fun ua : WholeSpaceL2 n × Ici δ ↦ l2Coordinate j ua.1) :=
      (l2Coordinate j).continuous.comp continuous_fst
    have hp : Continuous (fun ua : WholeSpaceL2 n × Ici δ ↦
        (l2Coordinate j ua.1, ua.2)) := hc.prodMk continuous_snd
    have hh := hscalar.comp hp
    simpa only [Function.comp_def] using hh
  have hass : Continuous (fun ua : WholeSpaceL2 n × Ici δ ↦
      Lp.euclideanTuple (fun j : Fin n ↦ Lp.compSMul μₙ 2 ua.2.val
        (hδ.trans_le ua.2.property).ne' (l2Coordinate j ua.1))) :=
    Lp.euclideanTuple.continuous.comp htuple
  convert hass using 1
  funext ua
  rw [← l2Dilation_euclideanTuple]
  simp only [l2Coordinate, Lp.euclideanTuple_coordinates]

end IncompressibleFlow
