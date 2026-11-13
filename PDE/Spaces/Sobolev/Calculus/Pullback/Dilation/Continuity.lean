/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.HigherOrder
public import PDE.Analysis.MeasureTheory.Lp.Composition.DilationContinuity

/-!
# Strong continuity of dilation on integer Sobolev graphs

Every weak derivative row is a continuous scalar power times an L² dilation.
The finite product graph topology therefore gives joint strong continuity.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.GraphSpace

variable {n k : ℕ}

/-- Joint continuity of the full scaled derivative tuple. -/
theorem continuous_dilationWkpAmbientCLM_Ici {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦
      dilationWkpAmbientCLM ua.2.val (hδ.trans_le ua.2.property).ne' ua.1) := by
  have hLp : Continuous (fun va : DerivLp n 2 univ × Ici δ ↦
      Lp.compSMul (domainMeasure n univ) 2 va.2.val
        (hδ.trans_le va.2.property).ne' va.1) := by
    exact Lp.continuous_compSMul_Ici (μ := domainMeasure n univ) hδ
  change Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦ WithLp.toLp 2
    (fun α : DerivIndex n k ↦ ua.2.val ^ α.toList.length •
      Lp.compSMul (domainMeasure n univ) 2 ua.2.val
        (hδ.trans_le ua.2.property).ne' (wkpCoordinateCLM α ua.1)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro α
  let C : W^{k,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpCoordinateCLM α
  have hC : Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦ C ua.1) :=
    C.continuous.comp continuous_fst
  have hpair : Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦ (C ua.1, ua.2)) :=
    hC.prodMk continuous_snd
  have hrow : Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦
      Lp.compSMul (domainMeasure n univ) 2 ua.2.val (hδ.trans_le ua.2.property).ne'
        (wkpCoordinateCLM α ua.1)) :=
    by simpa only [Function.comp_def, C] using hLp.comp hpair
  exact ((continuous_subtype_val.comp continuous_snd).pow α.toList.length).smul hrow

/-- Scalar dilation is jointly continuous on the actual Sobolev graph and positive factors
bounded away from zero. This is strong continuity, rather than operator-norm continuity. -/
theorem continuous_dilationWkpCLM_Ici {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun ua : W^{k,2}(ℝ^n) × Ici δ ↦
      dilationWkpCLM (by norm_num) ua.2.val (hδ.trans_le ua.2.property).ne' ua.1) :=
  (continuous_dilationWkpAmbientCLM_Ici hδ).subtype_mk _

end SobolevSpace.GraphSpace
