/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import PDE.FDeriv.Operators
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Interchanging two compact convolution kernels

Two continuous, compactly supported kernels can be applied in either order to locally integrable
data. The identity holds at every point. Compactness supplies the pointwise integrability
needed for Fubini, through the convolution of the two kernel norms.
-/

@[expose] public section

open MeasureTheory
open scoped Convolution

namespace PDE.Analysis

/-- The convolution of the kernel norms supplies the integrability needed for pointwise
associativity with locally integrable data. -/
private theorem convolution_assoc_compact_right {n : ℕ} {f g k : ℝ^n → ℝ}
    (hf : LocallyIntegrable f volume) (hg : Continuous g) (hk : Continuous k)
    (hgs : HasCompactSupport g) (hks : HasCompactSupport k) (x : ℝ^n) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x := by
  have hgn : HasCompactSupport (fun y ↦ ‖g y‖) := hgs.comp_left (by simp)
  have hkn : HasCompactSupport (fun y ↦ ‖k y‖) := hks.comp_left (by simp)
  have hc : Continuous
      ((fun y ↦ ‖g y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y ↦ ‖k y‖)) :=
    hkn.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hg.norm.locallyIntegrable hk.norm
  have hcs : HasCompactSupport
      ((fun y ↦ ‖g y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y ↦ ‖k y‖)) :=
    hgn.convolution (ContinuousLinearMap.mul ℝ ℝ) hkn
  apply convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c)
    hf.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Filter.Eventually.of_forall
      (hgs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf hg)
  · exact Filter.Eventually.of_forall
      (hkn.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
        hg.norm.locallyIntegrable hk.norm)
  · exact hcs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      (fun y ↦ (hf y).norm) hc x

/-- Continuous compact kernels commute when convolved with locally integrable data.
Both iterated convolutions are defined at every point, not merely almost everywhere. -/
theorem convolution_compact_kernels_interchange {n : ℕ} {f g k : ℝ^n → ℝ}
    (hf : LocallyIntegrable f volume) (hg : Continuous g) (hk : Continuous k)
    (hgs : HasCompactSupport g) (hks : HasCompactSupport k) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] k =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ] k) ⋆[ContinuousLinearMap.mul ℝ ℝ] g := by
  have hcomm : g ⋆[ContinuousLinearMap.mul ℝ ℝ] k =
      k ⋆[ContinuousLinearMap.mul ℝ ℝ] g := by
    simpa only [ContinuousLinearMap.flip_mul] using
      (convolution_flip (L := ContinuousLinearMap.mul ℝ ℝ)
        (μ := volume) (f := k) (g := g))
  ext x
  rw [convolution_assoc_compact_right hf hg hk hgs hks,
    convolution_assoc_compact_right hf hk hg hks hgs, hcomm]

end PDE.Analysis
