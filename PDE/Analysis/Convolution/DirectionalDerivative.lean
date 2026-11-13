/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import PDE.Analysis.Calculus.SecondDirectionalDerivative

/-!
# Directional derivatives of convolution

For a compactly supported smooth kernel, applying the derivative of a convolution to a
direction amounts to differentiating the kernel in that direction. Iterating this identity
avoids introducing a Hessian for the locally integrable factor.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Convolution

variable {G E F H : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant]
  {f : G → E} {g : G → F}

namespace HasCompactSupport

/-- A directional derivative of convolution differentiates its compactly supported
`C¹` kernel. The other factor only needs local integrability. -/
theorem fderiv_convolution_apply_right (hg : HasCompactSupport g)
    (L : E →L[ℝ] F →L[ℝ] H) (hf : LocallyIntegrable f μ) (hreg : ContDiff ℝ 1 g)
    (x v : G) :
    fderiv ℝ (f ⋆[L, μ] g) x v =
      (f ⋆[L, μ] (fun y ↦ fderiv ℝ g y v)) x := by
  rw [(hg.hasFDerivAt_convolution_right L hf hreg x).fderiv]
  exact convolution_precompR_apply L hf (hg.fderiv ℝ)
    (hreg.continuous_fderiv one_ne_zero) x v

/-- Two directional derivatives of convolution differentiate its compactly supported
`C²` kernel twice. Neither derivative falls on the locally integrable factor. -/
theorem fderiv_fderiv_convolution_apply_right (hg : HasCompactSupport g)
    (L : E →L[ℝ] F →L[ℝ] H) (hf : LocallyIntegrable f μ) (hreg : ContDiff ℝ 2 g)
    (x v w : G) :
    fderiv ℝ (fun y ↦ fderiv ℝ (f ⋆[L, μ] g) y v) x w =
      (f ⋆[L, μ] (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ g z v) y w)) x := by
  have hfirst : (fun y ↦ fderiv ℝ (f ⋆[L, μ] g) y v) =
      f ⋆[L, μ] (fun y ↦ fderiv ℝ g y v) :=
    funext fun y ↦ hg.fderiv_convolution_apply_right L hf (hreg.of_le (by norm_num)) y v
  rw [hfirst]
  exact (hg.fderiv_apply ℝ v).fderiv_convolution_apply_right L hf
    ((hreg.fderiv_right (by norm_num)).clm_apply contDiff_const) x w

/-- The curvature of a scalar convolution is obtained by differentiating its compact
kernel twice in the given direction. -/
theorem secondDirectionalDerivative_convolution_right (hg : HasCompactSupport g)
    (L : E →L[ℝ] F →L[ℝ] ℝ) (hf : LocallyIntegrable f μ) (hreg : ContDiff ℝ 2 g)
    (x v : G) :
    PDE.Analysis.secondDirectionalDerivative (f ⋆[L, μ] g) x v =
      (f ⋆[L, μ] (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ g z v) y v)) x := by
  have hc : ContDiff ℝ 2 (f ⋆[L, μ] g) := hg.contDiff_convolution_right (L := L) hf hreg
  rw [PDE.Analysis.secondDirectionalDerivative_eq_fderiv hc.contDiffAt]
  have hd : DifferentiableAt ℝ (fderiv ℝ (f ⋆[L, μ] g)) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiable_one.differentiableAt
  have heq := congrArg (fun A : G →L[ℝ] ℝ ↦ A v)
    (fderiv_clm_apply hd (differentiableAt_const v))
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_const_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at heq
  rw [← heq]
  exact hg.fderiv_fderiv_convolution_apply_right L hf hreg x v v

end HasCompactSupport
