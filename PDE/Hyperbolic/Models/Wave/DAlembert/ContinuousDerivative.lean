/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.DAlembert.ContinuousFamily

/-!
# Continuous first jets of one-dimensional wave families

Continuous initial velocities suffice for joint continuity of the first spacetime
derivative of the corresponding zero-displacement waves.
-/

@[expose] public noncomputable section

open PDE.Common

namespace WaveEquation

/-- Continuous velocities give jointly continuous first wave jets in any continuous family. -/
theorem continuous_fderiv_dAlembert_zero_displacement_family {T : Type*} [TopologicalSpace T]
    {h : T → ℝ → ℝ} (hc : Continuous (fun p : T × ℝ ↦ h p.1 p.2)) :
    Continuous (fun p : T × ℝ^2 ↦ fderiv ℝ
      (fun q : ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) (h p.1) (q 1) (q 0)) p.2) := by
  have hD (s : T) (p : ℝ^2) : fderiv ℝ
      (fun q : ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) (h s) (q 1) (q 0)) p =
      (1 / 2 : ℝ) • (h s (characteristicCoordinate 1 p) • characteristicCoordinate 1 -
        h s (characteristicCoordinate (-1) p) • characteristicCoordinate (-1)) := by
    simpa [characteristicCoordinate, sub_eq_add_neg] using
      (hasFDerivAt_dAlembertFormula (fun _ ↦ 0) (h s) (differentiable_const 0)
        (hc.comp (continuous_const.prodMk continuous_id)) p).fderiv
  simp_rw [hD]
  have hL (L : ℝ^2 →L[ℝ] ℝ) : Continuous (fun p : T × ℝ^2 ↦ h p.1 (L p.2) • L) :=
    (hc.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))).fun_smul continuous_const
  exact ((hL (characteristicCoordinate 1)).fun_sub
    (hL (characteristicCoordinate (-1)))).fun_const_smul (1 / 2 : ℝ)

end WaveEquation
