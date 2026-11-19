/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Strong spatial derivatives of L² convolution

For a compactly supported `C¹` scalar kernel, the translation curve of its convolution output
has a strong L² derivative at the origin. Differentiating Mathlib's Banach-valued convolution
of the translation orbit identifies the derivative with the integral against the derivative
kernel. The input is an arbitrary Banach-valued L² class.
Convolution by an integrable kernel also commutes with translation and preserves any
strong translation derivative of the input. This second assertion needs no kernel derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Translating the output of convolution is convolution with the translated input orbit.

The identity holds in `L²`. Moving translation through the integral uses its continuous
linear isometry, not pointwise evaluation of an equivalence class. -/
theorem translate_neg_convolutionL2CLM_eq (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (u : Lp E 2 (volume : Measure (ℝ^n))) (x : ℝ^n) :
    translateL2 ℝ (-x) (convolutionL2CLM k hk u) =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y : ℝ^n ↦ translateL2 ℝ (-y) u)) x := by
  rw [convolutionL2CLM_apply, ← (translateL2 ℝ (-x)).integral_comp_comm
    (fun y ↦ k y • translateL2 ℝ y u)]
  simp only [map_smul, translateL2_add, convolution_lsmul]
  apply integral_congr_ae
  filter_upwards with y
  rw [show -x + y = -(x - y) by abel]

/-- For a compactly supported `C¹` kernel `k`, the translation curve
`t ↦ τ_{-tv}(k ⋆ u)` has a strong `L²` derivative at `t = 0`, namely convolution with the
directional derivative `∂_v k`. -/
theorem hasDerivAt_translate_convolutionL2CLM {k : ℝ^n → ℝ}
    (hk : ContDiff ℝ 1 k) (hcs : HasCompactSupport k)
    (u : Lp E 2 (volume : Measure (ℝ^n))) (v : ℝ^n) :
    HasDerivAt
      (fun t : ℝ ↦ translateL2 ℝ (-(t • v))
        (convolutionL2CLM k (hk.continuous.integrable_of_hasCompactSupport hcs) u))
      (∫ y, fderiv ℝ k y v • translateL2 ℝ y u) 0 := by
  let L : ℝ →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp E 2 (volume : Measure (ℝ^n)) := ContinuousLinearMap.lsmul ℝ ℝ
  let orbit : ℝ^n → Lp E 2 (volume : Measure (ℝ^n)) :=
    fun x ↦ translateL2 ℝ (-x) u
  have horbit : LocallyIntegrable orbit volume :=
    ((continuous_translateL2 ℝ u).comp continuous_neg).locallyIntegrable
  let D : ℝ^n →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) :=
    (fderiv ℝ k ⋆[L.precompL (ℝ^n)] orbit) 0
  have hdiff : HasFDerivAt
      (fun x ↦ translateL2 ℝ (-x)
        (convolutionL2CLM k (hk.continuous.integrable_of_hasCompactSupport hcs) u))
      D 0 := by
    simpa only [translate_neg_convolutionL2CLM_eq] using
      hcs.hasFDerivAt_convolution_left L hk horbit (0 : ℝ^n)
  have hD : D v = ∫ y, fderiv ℝ k y v • translateL2 ℝ y u := by
    have hInt := (hcs.fderiv ℝ).convolutionExists_left
      (L.precompL (ℝ^n)) (hk.continuous_fderiv one_ne_zero) horbit (0 : ℝ^n)
    dsimp only [D]
    rw [convolution_def, ContinuousLinearMap.integral_apply hInt]
    simp only [ContinuousLinearMap.precompL_apply, orbit, zero_sub, neg_neg]
    rfl
  have hline : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const v using 1
    simp only [one_smul]
  have hcomp := hdiff.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  simpa only [Function.comp_def, hD] using hcomp

end PDE.Analysis

namespace PDE.Analysis

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Convolution by any integrable scalar kernel commutes with translation on L2.
The proof moves the translation isometry through the Bochner integral. -/
theorem translateL2_convolutionL2CLM (k : ℝ^n → ℝ) (hk : Integrable k volume)
    (y : ℝ^n) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    translateL2 ℝ y (convolutionL2CLM k hk u) =
      convolutionL2CLM k hk (translateL2 ℝ y u) := by
  simp only [convolutionL2CLM_apply]
  rw [← (translateL2 ℝ y).integral_comp_comm (fun z ↦ k z • translateL2 ℝ z u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [map_smul, translateL2_add, translateL2_add, add_comm y z]

/-- Integrable convolution preserves any strong directional translation derivative.
This requires no derivative of the convolution kernel. -/
theorem hasDerivAt_translate_convolutionL2CLM_of_hasDerivAt
    (k : ℝ^n → ℝ) (hk : Integrable k volume) (v : ℝ^n)
    (u g : Lp E 2 (volume : Measure (ℝ^n)))
    (hderiv : HasDerivAt (fun t : ℝ ↦ translateL2 ℝ (-(t • v)) u) g 0) :
    HasDerivAt (fun t : ℝ ↦ translateL2 ℝ (-(t • v)) (convolutionL2CLM k hk u))
      (convolutionL2CLM k hk g) 0 := by
  have h := (convolutionL2CLM (E := E) k hk).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hderiv
  change HasDerivAt (fun t : ℝ ↦ convolutionL2CLM k hk (translateL2 ℝ (-(t • v)) u))
    (convolutionL2CLM k hk g) 0 at h
  simpa only [← translateL2_convolutionL2CLM] using h

end PDE.Analysis
